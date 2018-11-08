#include "../include/KaleidoscopeJIT.h"
#include "llvm/ADT/APFloat.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Scalar/GVN.h"
#include <algorithm>
#include <cassert>
#include <cctype>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <map>
#include <memory>
#include <string>
#include <vector>

using namespace llvm;
using namespace llvm::orc;

//===----------------------------------------------------------------------===//
// Lexer
//===----------------------------------------------------------------------===//

// The lexer returns tokens [0-255] if it is an unknown character, otherwise one
// of these for known things.
enum Token {
	tok_eof = -1,

	// commands
	tok_FUNC = -2,
	tok_PRINT = -3,
	tok_RETURN = -4,
	tok_CONTINUE = -5,
	tok_IF = -6,
	tok_THEN = -7,
	tok_ELSE = -8,
	tok_FI = -9,
	tok_WHILE = -10,
	tok_DO = -11,
	tok_DONE = -12,
	tok_VAR = -13,
	tok_ASSIGN = -14,

	// primary
	tok_identifier = -15,
	tok_number = -16,
	tok_text = -17,

	// operators
	tok_binary = -18,
	tok_unary = -19
};

static std::string IdentifierStr; // Filled in if tok_identifier
static int NumVal;                // Filled in if tok_number
static std::string text;          // Filled in tok_text

static int gettok() {
	static int LastChar = ' ';
	// skip any whitespace
	while (isspace(LastChar))
		LastChar = getchar();

	if (isalpha(LastChar)) {
		// identifier: [a-zA-Z][a-zA-Z0-9]*
		IdentifierStr = LastChar;
		while (isalnum((LastChar = getchar())))
			IdentifierStr += LastChar;

		if (IdentifierStr == "FUNC")
			return tok_FUNC;
		else if (IdentifierStr == "PRINT")
			return tok_PRINT;
		else if (IdentifierStr == "RETURN")
			return tok_RETURN;
		else if (IdentifierStr == "CONTINUE")
			return tok_CONTINUE;
		else if (IdentifierStr == "IF")
			return tok_IF;
		else if (IdentifierStr == "THEN")
			return tok_THEN;
		else if (IdentifierStr == "ELSE")
			return tok_ELSE;
		else if (IdentifierStr == "FI")
			return tok_FI;
		else if (IdentifierStr == "WHILE")
			return tok_WHILE;
		else if (IdentifierStr == "DO")
			return tok_DO;
		else if (IdentifierStr == "DONE")
			return tok_DONE;
		else if (IdentifierStr == "binary")
			return tok_binary;
		else if (IdentifierStr == "unary")
			return tok_unary;

		return tok_identifier;
	}

	if (isdigit(LastChar)) {
		// Number: [0-9]+
		std::string NumStr;
		do {
			NumStr += LastChar;
			LastChar = getchar();
		} while (isdigit(LastChar));

		NumVal = atoi(NumStr.c_str());
		return tok_number;
	}

	if (LastChar == '"') {
		std::string temp;
		do {
			temp += LastChar;
			LastChar = getchar();
		} while (LastChar != '"');
		if (temp == "\"//") {
			do
				LastChar = getchar();
			while (LastChar != EOF && LastChar != '\n' && LastChar != '\r');
			if (LastChar != EOF)
				return gettok();
		}
		else {
			text = temp.substr(1, temp.length() - 1);
			return tok_text;
		}
	}

	if (LastChar == '=') {
		LastChar = getchar(); // eat '='
		fprintf(stderr, "Error: Please use ':=' to assign.\n");
		return LastChar;
	}

	if (LastChar == ':') {
		LastChar = getchar(); // eat ':'
		if (LastChar != '=') {
			fprintf(stderr, "Error: Please use ':=' to assign.\n");
			return LastChar;
		}
		else {
			LastChar = getchar(); // eat '='
			return tok_ASSIGN;
		}
	}

	if (LastChar == EOF)
		return tok_eof;

	int ThisChar = LastChar;
	LastChar = getchar();
	return ThisChar;
}

//===----------------------------------------------------------------------===//
// Abstract Syntax Tree (aka Parse Tree)
//===----------------------------------------------------------------------===//

namespace {

	/// ExprAST - Base class for all expression nodes.
	class ExprAST {
	public:
		virtual ~ExprAST() = default;
		virtual Value *codegen() = 0;
	};

	/// NumberExprAST - Expression class for numeric literals like "1.0".
	class NumberExprAST : public ExprAST {
		double Val;

	public:
		NumberExprAST(double Val) : Val(Val) {}

		Value *codegen() override;
	};

	/// VariableExprAST - Expression class for referencing a variable, like "a".
	class VariableExprAST : public ExprAST {
		std::string Name;

	public:
		VariableExprAST(const std::string &Name) : Name(Name) {}

		Value *codegen() override;
	};

	/// UnaryExprAST - Expression class for a unary operator.
	class UnaryExprAST : public ExprAST {
		char Opcode;
		std::unique_ptr<ExprAST> Operand;

	public:
		UnaryExprAST(char Opcode, std::unique_ptr<ExprAST> Operand)
			: Opcode(Opcode), Operand(std::move(Operand)) {}

		Value *codegen() override;
	};

	/// BinaryExprAST - Expression class for a binary operator.
	class BinaryExprAST : public ExprAST {
		char Op;
		std::unique_ptr<ExprAST> LHS, RHS;

	public:
		BinaryExprAST(char Op, std::unique_ptr<ExprAST> LHS,
			std::unique_ptr<ExprAST> RHS)
			: Op(Op), LHS(std::move(LHS)), RHS(std::move(RHS)) {}

		Value *codegen() override;
	};

	/// CallExprAST - Expression class for function calls.
	class CallExprAST : public ExprAST {
		std::string Callee;
		std::vector<std::unique_ptr<ExprAST>> Args;

	public:
		CallExprAST(const std::string &Callee,
			std::vector<std::unique_ptr<ExprAST>> Args)
			: Callee(Callee), Args(std::move(Args)) {}

		Value *codegen() override;
	};

	/// IfExprAST - Expression class for if/then/else.
	class IfExprAST : public ExprAST {
		std::unique_ptr<ExprAST> Cond, Then, Else;

	public:
		IfExprAST(std::unique_ptr<ExprAST> Cond, std::unique_ptr<ExprAST> Then,
			std::unique_ptr<ExprAST> Else)
			: Cond(std::move(Cond)), Then(std::move(Then)), Else(std::move(Else)) {}
		// IfExprAST(std::unique_ptr<ExprAST> Cond, std::unique_ptr<ExprAST> Then)
		//  : Cond(std::move(Cond)), Then(std::move(Then)) {}

		Value *codegen() override;
	};

	/// ForExprAST - Expression class for for/in.
	class WhileExprAST : public ExprAST {
		std::string VarName;
		std::unique_ptr<ExprAST> Start, End, Step, Body;

	public:
		WhileExprAST(const std::string &VarName, std::unique_ptr<ExprAST> Start,
			std::unique_ptr<ExprAST> End, std::unique_ptr<ExprAST> Step,
			std::unique_ptr<ExprAST> Body)
			: VarName(VarName), Start(std::move(Start)), End(std::move(End)),
			Step(std::move(Step)), Body(std::move(Body)) {}

		Value *codegen() override;
	};

	/// PrototypeAST - This class represents the "prototype" for a function,
	/// which captures its name, and its argument names (thus implicitly the number
	/// of arguments the function takes).
	class PrototypeAST {
		std::string Name;
		std::vector<std::string> Args;
		bool IsOperator;
		unsigned Precedence; // Precedence if a binary op.

	public:
		PrototypeAST(const std::string &Name, std::vector<std::string> Args,
			bool IsOperator = false, unsigned Prec = 0)
			: Name(Name), Args(std::move(Args)), IsOperator(IsOperator),
			Precedence(Prec) {}

		Function *codegen();
		const std::string &getName() const { return Name; }

		bool isUnaryOp() const { return IsOperator && Args.size() == 1; }
		bool isBinaryOp() const { return IsOperator && Args.size() == 2; }

		char getOperatorName() const {
			assert(isUnaryOp() || isBinaryOp());
			return Name[Name.size() - 1];
		}

		unsigned getBinaryPrecedence() const { return Precedence; }
	};

	/// FunctionAST - This class represents a function definition itself.
	class FunctionAST {
		std::unique_ptr<PrototypeAST> Proto;
		std::unique_ptr<ExprAST> Body;

	public:
		FunctionAST(std::unique_ptr<PrototypeAST> Proto,
			std::unique_ptr<ExprAST> Body)
			: Proto(std::move(Proto)), Body(std::move(Body)) {}

		Function *codegen();
	};

} // end anonymous namespace

//===----------------------------------------------------------------------===//
// Parser
//===----------------------------------------------------------------------===//

/// CurTok/getNextToken - Provide a simple token buffer.  CurTok is the current
/// token the parser is looking at.  getNextToken reads another token from the
/// lexer and updates CurTok with its results.
static int CurTok;
static int getNextToken() { return CurTok = gettok(); }

/// BinopPrecedence - This holds the precedence for each binary operator that is
/// defined.
static std::map<char, int> BinopPrecedence;

/// GetTokPrecedence - Get the precedence of the pending binary operator token.
static int GetTokPrecedence() {
	if (!isascii(CurTok) && CurTok != -14)
		return -1;

	// Make sure it's a declared binop.
	int TokPrec;
	if (CurTok == -14)
		TokPrec = BinopPrecedence['='];
	else
		TokPrec = BinopPrecedence[CurTok];
	if (TokPrec <= 0)
		return -1;
	return TokPrec;
}

/// LogError* - These are little helper functions for error handling.
std::unique_ptr<ExprAST> LogError(const char *Str) {
	fprintf(stderr, "Error: %s\n", Str);
	return nullptr;
}
std::unique_ptr<PrototypeAST> LogErrorP(const char *Str) {
	LogError(Str);
	return nullptr;
}
static std::unique_ptr<ExprAST> ParseExpression();
static std::unique_ptr<ExprAST> parseExpression();

/// numberexpr ::= number
static std::unique_ptr<ExprAST> ParseNumberExpr() {
	auto Result = llvm::make_unique<NumberExprAST>(NumVal);
	getNextToken(); // consume the number
	return std::move(Result);
}

static std::unique_ptr<ExprAST> parseNumberExpr() {
	auto Result = llvm::make_unique<NumberExprAST>(0);
	return std::move(Result);
}

/// parenexpr ::= '(' expression ')'
static std::unique_ptr<ExprAST> ParseParenExpr() {
	getNextToken(); // eat (.
	auto V = ParseExpression();
	if (!V)
		return nullptr;

	if (CurTok != ')')
		return LogError("expected ')'");
	getNextToken(); // eat ).
	return V;
}

/// identifierexpr
///   ::= identifier
///   ::= identifier '(' expression* ')'
static std::unique_ptr<ExprAST> ParseIdentifierExpr() {
	std::string IdName = IdentifierStr;

	getNextToken(); // eat identifier.

	if (CurTok != '(') // Simple variable ref.
		return llvm::make_unique<VariableExprAST>(IdName);

	// Call.
	getNextToken(); // eat (
	std::vector<std::unique_ptr<ExprAST>> Args;
	if (CurTok != ')') {
		while (true) {
			if (auto Arg = ParseExpression())
				Args.push_back(std::move(Arg));
			else
				return nullptr;

			if (CurTok == ')')
				break;

			if (CurTok != ',')
				return LogError("Expected ')' or ',' in argument list");
			getNextToken();
		}
	}

	// Eat the ')'.
	getNextToken();

	return llvm::make_unique<CallExprAST>(IdName, std::move(Args));
}

/// ifexpr ::= 'if' expression 'then' expression 'else' expression
static std::unique_ptr<ExprAST> ParseIfExpr() {
	getNextToken(); // eat the IF.

	// condition.
	auto Cond = ParseExpression();
	if (!Cond)
		return nullptr;

	if (CurTok != tok_THEN)
		return LogError("expected THEN");
	getNextToken(); // eat the THEN

	if (CurTok != tok_RETURN)
		return LogError("expected RETURN");
	getNextToken(); // eat the RETURN

	auto Then = ParseExpression();
	if (!Then)
		return nullptr;

	if (CurTok != tok_ELSE) { //没有ELSE块的处理方法
	  // return LogError("expected ELSE");
		if (CurTok != tok_FI)
			return LogError("expected FI");
		getNextToken(); // eat the FI

		auto Else = parseExpression();
		return llvm::make_unique<IfExprAST>(std::move(Cond), std::move(Then),
			std::move(Else));
	}
	getNextToken(); // eat the ELSE

	if (CurTok != tok_RETURN)
		return LogError("expected RETURN");
	getNextToken(); // eat the RETURN

	auto Else = ParseExpression();
	if (!Else)
		return nullptr;

	if (CurTok != tok_FI) {
		return LogError("expected FI");
	}
	getNextToken(); // eat the FI

	return llvm::make_unique<IfExprAST>(std::move(Cond), std::move(Then),
		std::move(Else));
}

/// forexpr ::= 'for' identifier '=' expr ',' expr (',' expr)? 'in' expression
static std::unique_ptr<ExprAST> ParseWhileExpr() {
	getNextToken(); // eat the WHILE.

	if (CurTok != tok_identifier)
		return LogError("expected identifier after WHILE");
	std::string IdName = IdentifierStr;

	// getNextToken(); // eat identifier.

	// if (CurTok != '-')
	//  return LogError("expected '-' after WHILE");
	////getNextToken(); // eat '-'.

	auto Start = parseExpression();
	if (!Start)
		return nullptr;

	std::unique_ptr<ExprAST> Step;
	Step = parseExpression();
	if (!Step) {
		return nullptr;
	}

	auto End = ParseExpression();
	if (!End)
		return nullptr;

	if (CurTok != tok_DO)
		return LogError("expected 'DO' after WHILE");
	getNextToken(); // eat 'DO'.

	if (CurTok != '{')
		return LogError("expected '{' after WHILE");
	getNextToken(); // eat '{'.

	// if (CurTok != tok_RETURN)
	//  return LogError("expected 'RETURN' after '{'");
	// getNextToken(); // eat 'RETURN'.

	auto Body = ParseExpression();
	if (!Body)
		return nullptr;

	if (CurTok != '}')
		return LogError("expected '}' after WHILE");
	getNextToken(); // eat '}'

	if (CurTok != tok_DONE)
		return LogError("expected 'DONE' after WHILE");
	getNextToken(); // eat 'DONE'

	// if (CurTok != tok_RETURN)
	//  return LogError("expected 'RETURN' after DONE");
	// getNextToken(); // eat 'RETURN'

	return llvm::make_unique<WhileExprAST>(IdName, std::move(Start),
		std::move(End), std::move(nullptr),
		std::move(Body));
}

/// primary
///   ::= identifierexpr
///   ::= numberexpr
///   ::= parenexpr
///   ::= ifexpr
static std::unique_ptr<ExprAST> ParsePrimary() {
	switch (CurTok) {
	default:
		return LogError("unknown token when expecting an expression");
	case tok_identifier:
		return ParseIdentifierExpr();
	case tok_number:
		return ParseNumberExpr();
	case '(':
		return ParseParenExpr();
	case tok_IF:
		return ParseIfExpr();
	case tok_WHILE:
		return ParseWhileExpr();
	case tok_PRINT:
		// return ParsePrintExpr();
		return nullptr;
	}
}

static std::unique_ptr<ExprAST> parsePrimary() { return parseNumberExpr(); }

/// unary
///   ::= primary
///   ::= '!' unary
static std::unique_ptr<ExprAST> ParseUnary() {
	// If the current token is not an operator, it must be a primary expr.
	if (!isascii(CurTok) || CurTok == '(' || CurTok == ',')
		return ParsePrimary();

	// If this is a unary operator, read it.
	int Opc = CurTok;
	getNextToken();
	if (auto Operand = ParseUnary())
		return llvm::make_unique<UnaryExprAST>(Opc, std::move(Operand));
	return nullptr;
}

/// binoprhs
///   ::= ('+' primary)*
static std::unique_ptr<ExprAST> ParseBinOpRHS(int ExprPrec,
	std::unique_ptr<ExprAST> LHS) {
	// If this is a binop, find its precedence.
	while (true) {
		int TokPrec = GetTokPrecedence();

		// If this is a binop that binds at least as tightly as the current binop,
		// consume it, otherwise we are done.
		if (TokPrec < ExprPrec)
			return LHS;

		// Okay, we know this is a binop.
		int BinOp = CurTok;
		getNextToken(); // eat binop

		// Parse the primary expression after the binary operator.
		auto RHS = ParseUnary();
		if (!RHS)
			return nullptr;

		// If BinOp binds less tightly with RHS than the operator after RHS, let
		// the pending operator take RHS as its LHS.
		int NextPrec = GetTokPrecedence();
		if (TokPrec < NextPrec) {
			RHS = ParseBinOpRHS(TokPrec + 1, std::move(RHS));
			if (!RHS)
				return nullptr;
		}

		// Merge LHS/RHS.
		LHS =
			llvm::make_unique<BinaryExprAST>(BinOp, std::move(LHS), std::move(RHS));
	}
}

/// expression
///   ::= primary binoprhs
///
static std::unique_ptr<ExprAST> ParseExpression() {
	auto LHS = ParseUnary();
	if (!LHS)
		return nullptr;

	return ParseBinOpRHS(0, std::move(LHS));
}

static std::unique_ptr<ExprAST> parseExpression() {
	auto LHS = parsePrimary();
	if (!LHS)
		return nullptr;
	return ParseBinOpRHS(0, std::move(LHS));
}

/// prototype
///   ::= id '(' id* ')'
static std::unique_ptr<PrototypeAST> ParsePrototype() {
	std::string FnName;

	unsigned Kind = 0; // 0 = identifier, 1 = unary, 2 = binary.
	unsigned BinaryPrecedence = 30;

	switch (CurTok) {
	default:
		return LogErrorP("Expected function name in prototype");
	case tok_identifier:
		FnName = IdentifierStr;
		Kind = 0;
		getNextToken();
		break;
	case tok_unary:
		getNextToken();
		if (!isascii(CurTok))
			return LogErrorP("Expected unary operator");
		FnName = "unary";
		FnName += (char)CurTok;
		Kind = 1;
		getNextToken();
		break;
	case tok_binary:
		getNextToken();
		if (!isascii(CurTok))
			return LogErrorP("Expected binary operator");
		FnName = "binary";
		FnName += (char)CurTok;
		Kind = 2;
		getNextToken();

		// Read the precedence if present.
		if (CurTok == tok_number) {
			if (NumVal < 1 || NumVal > 100)
				return LogErrorP("Invalid precedence: must be 1..100");
			BinaryPrecedence = (unsigned)NumVal;
			getNextToken();
		}
		break;
	}

	if (CurTok != '(')
		return LogErrorP("Expected '(' in prototype");

	std::vector<std::string> ArgNames;
	while (getNextToken() == tok_identifier) {
		ArgNames.push_back(IdentifierStr);
		getNextToken(); // eat ','
		if (CurTok != ',')
			break;
	}
	if (CurTok != ')')
		return LogErrorP("Expected ')' in prototype");

	// success.
	getNextToken(); // eat ')'.

	// Verify right number of names for operator.
	if (Kind && ArgNames.size() != Kind)
		return LogErrorP("Invalid number of operands for operator");

	return llvm::make_unique<PrototypeAST>(FnName, ArgNames, Kind != 0,
		BinaryPrecedence);
}

/// definition ::= 'FUNC' prototype expression
static std::unique_ptr<FunctionAST> ParseDefinition() {
	getNextToken(); // eat FUNC.
	auto Proto = ParsePrototype();
	if (!Proto)
		return nullptr;
	if (CurTok != '{') {
		fprintf(stderr, "Expected '{' in function definition.\n");
		return nullptr;
	}
	else
		getNextToken(); // eat '{'
	if (CurTok != tok_RETURN) {

	}
	else {
		getNextToken();
	} // eat 'RETURN'
	if (auto E = ParseExpression()) {
		if (CurTok != '}') {
			fprintf(stderr, "Expected '}' in function definition.\n");
			return nullptr;
		}
		else {
			getNextToken(); // eat '}'
			return llvm::make_unique<FunctionAST>(std::move(Proto), std::move(E));
		}
	}
	return nullptr;
}

/// toplevelexpr ::= expression
static std::unique_ptr<FunctionAST> ParseTopLevelExpr() {
	if (auto E = ParseExpression()) {
		// Make an anonymous proto.
		auto Proto = llvm::make_unique<PrototypeAST>("__anon_expr",
			std::vector<std::string>());
		return llvm::make_unique<FunctionAST>(std::move(Proto), std::move(E));
	}
	return nullptr;
}

//===----------------------------------------------------------------------===//
// Code Generation
//===----------------------------------------------------------------------===//

static LLVMContext TheContext;
static IRBuilder<> Builder(TheContext);
static std::unique_ptr<Module> TheModule;
static std::map<std::string, Value *> NamedValues;
static std::unique_ptr<legacy::FunctionPassManager> TheFPM;
static std::unique_ptr<KaleidoscopeJIT> TheJIT;
static std::map<std::string, std::unique_ptr<PrototypeAST>> FunctionProtos;

Value *LogErrorV(const char *Str) {
	LogError(Str);
	return nullptr;
}

Function *getFunction(std::string Name) {
	// First, see if the function has already been added to the current module.
	if (auto *F = TheModule->getFunction(Name))
		return F;

	// If not, check whether we can codegen the declaration from some existing
	// prototype.
	auto FI = FunctionProtos.find(Name);
	if (FI != FunctionProtos.end())
		return FI->second->codegen();

	// If no existing prototype exists, return null.
	return nullptr;
}

Value *NumberExprAST::codegen() {
	return ConstantInt::get(TheContext, APInt(64, Val));
}

Value *VariableExprAST::codegen() {
	// Look this variable up in the function.
	Value *V = NamedValues[Name];
	if (!V)
		return LogErrorV("Unknown variable name");
	return V;
}

Value *UnaryExprAST::codegen() {
	Value *OperandV = Operand->codegen();
	if (!OperandV)
		return nullptr;

	Function *F = getFunction(std::string("unary") + Opcode);
	if (!F)
		return LogErrorV("Unknown unary operator");

	return Builder.CreateCall(F, OperandV, "unop");
}

Value *BinaryExprAST::codegen() {
	Value *L = LHS->codegen();
	Value *R = RHS->codegen();
	if (!L || !R)
		return nullptr;

	switch (Op) {
	case '+':
		return Builder.CreateAdd(L, R, "addtmp");
	case '-':
		return Builder.CreateSub(L, R, "subtmp");
	case '*':
		return Builder.CreateMul(L, R, "multmp");
	case '<':
		// return Builder.CreateICmpULT(L, R, "cmptmp");
		L = Builder.CreateICmpULT(L, R, "cmptmp");
		// Convert bool 0/1 to double 0.0 or 1.0
		return Builder.CreateUIToFP(L, Type::getDoubleTy(TheContext), "booltmp");
	default:
		break;
	}

	// If it wasn't a builtin binary operator, it must be a user defined one. Emit
	// a call to it.
	Function *F = getFunction(std::string("binary") + Op);
	assert(F && "binary operator not found!");

	Value *Ops[] = { L, R };
	return Builder.CreateCall(F, Ops, "binop");
}

Value *CallExprAST::codegen() {
	// Look up the name in the global module table.
	Function *CalleeF = getFunction(Callee);
	if (!CalleeF)
		return LogErrorV("Unknown function referenced");

	// If argument mismatch error.
	if (CalleeF->arg_size() != Args.size())
		return LogErrorV("Incorrect # arguments passed");

	std::vector<Value *> ArgsV;
	for (unsigned i = 0, e = Args.size(); i != e; ++i) {
		ArgsV.push_back(Args[i]->codegen());
		if (!ArgsV.back())
			return nullptr;
	}

	return Builder.CreateCall(CalleeF, ArgsV, "calltmp");
}

Value *IfExprAST::codegen() {
	Value *CondV = Cond->codegen();
	if (!CondV)
		return nullptr;

	// Convert condition to a bool by comparing non-equal to 0.
	if (CondV->getType() ==
		Type::getDoubleTy(TheContext)) { //处理if的Cond为x < 3(出现<的情况)
		CondV = Builder.CreateFCmpONE(
			CondV, ConstantFP::get(TheContext, APFloat(0.0)), "IFcond");
	}
	else { //处理if的Cond为if x(直接接数字的情况)
		CondV = Builder.CreateICmpNE(
			CondV, ConstantInt::get(TheContext, APInt(64, 0)), "IFcond");
	}

	Function *TheFunction = Builder.GetInsertBlock()->getParent();

	// Create blocks for the then and else cases.  Insert the 'then' block at the
	// end of the function.
	BasicBlock *ThenBB = BasicBlock::Create(TheContext, "THEN", TheFunction);
	BasicBlock *ElseBB = BasicBlock::Create(TheContext, "ELSE");
	BasicBlock *MergeBB = BasicBlock::Create(TheContext, "IFcond");

	Builder.CreateCondBr(CondV, ThenBB, ElseBB);

	// Emit then value.
	Builder.SetInsertPoint(ThenBB);

	Value *ThenV = Then->codegen();
	if (!ThenV)
		return nullptr;

	Builder.CreateBr(MergeBB);
	// Codegen of 'Then' can change the current block, update ThenBB for the PHI.
	ThenBB = Builder.GetInsertBlock();

	// Emit else block.
	TheFunction->getBasicBlockList().push_back(ElseBB);
	Builder.SetInsertPoint(ElseBB);

	Value *ElseV = Else->codegen();
	if (!ElseV)
		return nullptr;

	Builder.CreateBr(MergeBB);
	// Codegen of 'Else' can change the current block, update ElseBB for the PHI.
	ElseBB = Builder.GetInsertBlock();

	// Emit merge block.
	TheFunction->getBasicBlockList().push_back(MergeBB);
	Builder.SetInsertPoint(MergeBB);

	PHINode *PN = Builder.CreatePHI(Type::getInt64Ty(TheContext), 2, "IFtmp");

	PN->addIncoming(ThenV, ThenBB);
	PN->addIncoming(ElseV, ElseBB);
	return PN;
}

// Output for-loop as:
//   ...
//   start = startexpr
//   goto loop
// loop:
//   variable = phi [start, loopheader], [nextvariable, loopend]
//   ...
//   bodyexpr
//   ...
// loopend:
//   step = stepexpr
//   nextvariable = variable + step
//   endcond = endexpr
//   br endcond, loop, endloop
// outloop:
Value *WhileExprAST::codegen() {
	// Emit the start code first, without 'variable' in scope.
	Value *StartVal = Start->codegen();
	if (!StartVal)
		return nullptr;

	// Make the new basic block for the loop header, inserting after current
	// block.
	Function *TheFunction = Builder.GetInsertBlock()->getParent();
	BasicBlock *PreheaderBB = Builder.GetInsertBlock();
	BasicBlock *LoopBB = BasicBlock::Create(TheContext, "loop", TheFunction);

	// Insert an explicit fall through from the current block to the LoopBB.
	Builder.CreateBr(LoopBB);

	// Start insertion in LoopBB.
	Builder.SetInsertPoint(LoopBB);

	// Start the PHI node with an entry for Start.
	PHINode *Variable =
		Builder.CreatePHI(Type::getInt64Ty(TheContext), 2, VarName);
	Variable->addIncoming(StartVal, PreheaderBB);

	// Within the loop, the variable is defined equal to the PHI node.  If it
	// shadows an existing variable, we have to restore it, so save it now.
	Value *OldVal = NamedValues[VarName];
	NamedValues[VarName] = Variable;

	// Emit the body of the loop.  This, like any other expr, can change the
	// current BB.  Note that we ignore the value computed by the body, but don't
	// allow an error.
	if (!Body->codegen())
		return nullptr;

	// Emit the step value.
	Value *StepVal = nullptr;
	if (Step) {
		StepVal = Step->codegen();
		if (!StepVal)
			return nullptr;
	}
	else {
		// If not specified, use 1.
		StepVal = ConstantInt::get(TheContext, APInt(64, 1));
	}

	Value *NextVar = Builder.CreateAdd(Variable, StepVal, "nextvar");

	// Compute the end condition.
	Value *EndCond = End->codegen();
	if (!EndCond)
		return nullptr;

	// Convert condition to a bool by comparing non-equal to 0.

	if (EndCond->getType() ==
		Type::getDoubleTy(TheContext)) { //处理WHILE的Cond为x < 3(出现<的情况)
		EndCond = Builder.CreateFCmpONE(
			EndCond, ConstantFP::get(TheContext, APFloat(0.0)), "loopcond");
	}
	else { //处理WHILE的Cond为WHILE x(直接接数字的情况)
		EndCond = Builder.CreateICmpNE(
			EndCond, ConstantInt::get(TheContext, APInt(64, 0)), "loopcond");
	}

	// Create the "after loop" block and insert it.
	BasicBlock *LoopEndBB = Builder.GetInsertBlock();
	BasicBlock *AfterBB =
		BasicBlock::Create(TheContext, "afterloop", TheFunction);

	// Insert the conditional branch into the end of LoopEndBB.
	Builder.CreateCondBr(EndCond, LoopBB, AfterBB);

	// Any new code will be inserted in AfterBB.
	Builder.SetInsertPoint(AfterBB);

	// Add a new entry to the PHI node for the backedge.
	Variable->addIncoming(NextVar, LoopEndBB);

	// Restore the unshadowed variable.
	if (OldVal)
		NamedValues[VarName] = OldVal;
	else
		NamedValues.erase(VarName);

	// for expr always returns 0.0.
	return Constant::getNullValue(Type::getInt64Ty(TheContext));
}

Function *PrototypeAST::codegen() {
	// Make the function type:  double(double,double) etc.
	std::vector<Type *> Ints(Args.size(), Type::getInt64Ty(TheContext));
	FunctionType *FT =
		FunctionType::get(Type::getInt64Ty(TheContext), Ints, false);

	Function *F =
		Function::Create(FT, Function::ExternalLinkage, Name, TheModule.get());

	// Set names for all arguments.
	unsigned Idx = 0;
	for (auto &Arg : F->args())
		Arg.setName(Args[Idx++]);

	return F;
}

Function *FunctionAST::codegen() {
	// Transfer ownership of the prototype to the FunctionProtos map, but keep a
	// reference to it for use below.
	auto &P = *Proto;
	FunctionProtos[Proto->getName()] = std::move(Proto);
	Function *TheFunction = getFunction(P.getName());
	if (!TheFunction)
		return nullptr;

	// If this is an operator, install it.
	if (P.isBinaryOp())
		BinopPrecedence[P.getOperatorName()] = P.getBinaryPrecedence();

	// Create a new basic block to start insertion into.
	BasicBlock *BB = BasicBlock::Create(TheContext, "entry", TheFunction);
	Builder.SetInsertPoint(BB);

	// Record the function arguments in the NamedValues map.
	NamedValues.clear();
	for (auto &Arg : TheFunction->args())
		NamedValues[Arg.getName()] = &Arg;

	if (Value *RetVal = Body->codegen()) {
		// Finish off the function.
		Builder.CreateRet(RetVal);

		// Validate the generated code, checking for consistency.
		verifyFunction(*TheFunction);

		// Run the optimizer on the function.
		TheFPM->run(*TheFunction);

		return TheFunction;
	}

	// Error reading body, remove function.
	TheFunction->eraseFromParent();
	return nullptr;
}

//===----------------------------------------------------------------------===//
// Top-Level parsing
//===----------------------------------------------------------------------===//

static void InitializeModuleAndPassManager() {
	// Open a new module.
	TheModule = llvm::make_unique<Module>("my cool jit", TheContext);
	TheModule->setDataLayout(TheJIT->getTargetMachine().createDataLayout());

	// Create a new pass manager attached to it.
	TheFPM = llvm::make_unique<legacy::FunctionPassManager>(TheModule.get());

	// Do simple "peephole" optimizations and bit-twiddling optzns.
	TheFPM->add(createInstructionCombiningPass());
	// Reassociate expressions.
	TheFPM->add(createReassociatePass());
	// Eliminate Common SubExpressions.
	TheFPM->add(createGVNPass());
	// Simplify the control flow graph (deleting unreachable blocks, etc).
	TheFPM->add(createCFGSimplificationPass());

	TheFPM->doInitialization();
}

static void HandleDefinition() {
	if (auto FnAST = ParseDefinition()) {
		if (auto *FnIR = FnAST->codegen()) {
			fprintf(stderr, "Read function definition:");
			FnIR->print(errs());
			fprintf(stderr, "\n");
			TheJIT->addModule(std::move(TheModule));
			InitializeModuleAndPassManager();
		}
	}
	else {
		// Skip token for error recovery.
		getNextToken();
	}
}

static void HandleTopLevelExpression() {
	// Evaluate a top-level expression into an anonymous function.
	if (auto FnAST = ParseTopLevelExpr()) {
		if (FnAST->codegen()) {
			// JIT the module containing the anonymous expression, keeping a handle so
			// we can free it later.
			auto H = TheJIT->addModule(std::move(TheModule));
			InitializeModuleAndPassManager();

			// Search the JIT for the __anon_expr symbol.
			auto ExprSymbol = TheJIT->findSymbol("__anon_expr");
			assert(ExprSymbol && "Function not found");

			// Get the symbol's address and cast it to the right type (takes no
			// arguments, returns a double) so we can call it as a native function.

			/*int32_t (*FP)() =
				(int32_t(*)())(intptr_t)cantFail(ExprSymbol.getAddress());
			fprintf(stderr, "Evaluated to %d\n", FP());*/

			double(*FP)() =
				(double(*)())(intptr_t)cantFail(ExprSymbol.getAddress());
			fprintf(stderr, "Evaluated to %f\n", FP());

			// Delete the anonymous expression module from the JIT.
			TheJIT->removeModule(H);
		}
	}
	else {
		// Skip token for error recovery.
		getNextToken();
	}
}

/// top ::= definition | external | expression | ';'
static void MainLoop() {
	while (true) {
		fprintf(stderr, "ready> ");
		switch (CurTok) {
		case tok_eof:
			return;
		case ';': // ignore top-level semicolons.
			getNextToken();
			break;
		case tok_FUNC:
			HandleDefinition();
			break;
		default:
			HandleTopLevelExpression();
			break;
		}
	}
}

//===----------------------------------------------------------------------===//
// Main driver code.
//===----------------------------------------------------------------------===//

int main() {
	InitializeNativeTarget();
	InitializeNativeTargetAsmPrinter();
	InitializeNativeTargetAsmParser();

	// Install standard binary operators.
	// 1 is lowest precedence.
	BinopPrecedence['<'] = 10;
	BinopPrecedence['+'] = 20;
	BinopPrecedence['-'] = 20;
	BinopPrecedence['*'] = 40;
	BinopPrecedence['='] = 50; // highest.

	// Prime the first token.
	fprintf(stderr, "ready> ");
	getNextToken();

	TheJIT = llvm::make_unique<KaleidoscopeJIT>();

	InitializeModuleAndPassManager();

	// Run the main "interpreter loop" now.
	MainLoop();

	// Print out all of the generated code.
	// TheModule->print(errs(), nullptr);

	return 0;
}
