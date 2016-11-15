/*******************************************************************************
 * Copyright (C) 2016 Embedded Systems and Applications Group
 * Department of Computer Science, Technische Universitaet Darmstadt,
 * Hochschulstr. 10, 64289 Darmstadt, Germany.
 * 
 * All rights reserved.
 * 
 * This software is provided free for educational use only.
 * It may not be used for commercial purposes without the
 * prior written permission of the authors.
 ******************************************************************************/
package mavlc.parser.recursive_descent;

import mavlc.ast.nodes.expression.*;
import mavlc.ast.nodes.function.FormalParameter;
import mavlc.ast.nodes.function.Function;
import mavlc.ast.nodes.module.Module;
import mavlc.ast.nodes.statement.*;
import mavlc.ast.type.*;
import mavlc.error_reporting.SyntaxError;

import java.util.*;

import org.xmlunit.diff.Comparison;

import mavlc.parser.recursive_descent.Token.TokenType;
import static mavlc.ast.nodes.expression.Compare.Comparison.*;
import static mavlc.parser.recursive_descent.Token.TokenType.*;

/**
 * A recursive-descent parser for MAVL.
 */
public final class Parser {

	private final Deque<Token> tokens;
	private Token currentToken;

	/**
	 * Constructor.
	 * 
	 * @param tokens A token stream that was produced by the {@link Scanner}.
	 */
	public Parser(Deque<Token> tokens) {
		this.tokens = tokens;
		currentToken = tokens.poll();
	}

	/**
	 * Parses the MAVL grammar's start symbol, Module.
	 * 
	 * @return A {@link Module} node that is the root of the AST representing the tokenized input progam. 
	 * @throws SyntaxError to indicate that an unexpected token was encountered.
	 */
	public Module parse() throws SyntaxError {
		Module compilationUnit = new Module(tokens.peek().line, 0);
		while (!tokens.isEmpty()) {
			Function func = parseFunction();
			compilationUnit.addFunction(func);
		}
		return compilationUnit;
	}

	private String accept(TokenType type) throws SyntaxError {
		Token t = currentToken;
		if (t.type != type)
			throw new SyntaxError(t, type);
		acceptIt();
		return t.spelling;
	}

	private void acceptIt() {
		Token old = currentToken;
		currentToken = tokens.poll();
		if (old == null && currentToken == null)
			throw new SyntaxError(currentToken);
	}

	private Function parseFunction() throws SyntaxError {
		int line = currentToken.line;
		int column = currentToken.column;

		accept(FUNCTION);
		Type type = parseType();
		String name = accept(ID);

		Function function = new Function(line, column, name, type);

		accept(LPAREN);
		if (currentToken.type != RPAREN) {
			function.addParameter(parseFormalParameter());
			while (currentToken.type != RPAREN) {
				accept(COMMA);
				function.addParameter(parseFormalParameter());
			}
		}
		accept(RPAREN);

		accept(LBRACE);
		while (currentToken.type != RBRACE)
			function.addStatement(parseStatement());
		accept(RBRACE);

		return function;
	}

	private FormalParameter parseFormalParameter() throws SyntaxError {
		int line = currentToken.line;
		int column = currentToken.column;

		Type type = parseType();
		String name = accept(ID);
		
		return new FormalParameter(line, column, name, type);
	}

	private Type parseType() throws SyntaxError {
		boolean vector = false;
		switch (currentToken.type) {
		case INT:    acceptIt(); return Type.getIntType();
		case FLOAT:  acceptIt(); return Type.getFloatType();
		case BOOL:   acceptIt(); return Type.getBoolType();
		case VOID:   acceptIt(); return Type.getVoidType();
		case STRING: acceptIt(); return Type.getStringType();
		case VECTOR: accept(VECTOR); vector = true; break;
		case MATRIX: accept(MATRIX); break;
		default:
			throw new SyntaxError(currentToken, INT, FLOAT, BOOL, VOID, STRING, VECTOR, MATRIX);
		}

		accept(LANGLE);
		ScalarType subtype = null;
		switch (currentToken.type) {
		case INT:   subtype = Type.getIntType(); break;
		case FLOAT: subtype = Type.getFloatType(); break;
		default:
			throw new SyntaxError(currentToken, INT, FLOAT);
		}
		acceptIt();
		accept(RANGLE);
		accept(LBRACKET);
		int x = parseIntLit();
		accept(RBRACKET);

		if (vector)
			return new VectorType(subtype, x);

		accept(LBRACKET);
		int y = parseIntLit();
		accept(RBRACKET);

		return new MatrixType(subtype, x, y);
	}

	private Statement parseStatement() throws SyntaxError {
		Statement s = null;
		switch (currentToken.type) {
		case VAL:    s = parseValueDef();     break;
		case VAR:    s = parseVarDecl();      break;
		case RETURN: s = parseReturn();       break;
		case ID:     s = parseAssignOrCall(); break;
		case FOR:    s = parseFor();          break;
		case IF:     s = parseIf();           break;
		case LBRACE: s = parseCompound();     break;
		default:
			throw new SyntaxError(currentToken, VAL, VAR, FOR, IF, RETURN, LBRACE, ID);
		}

		return s;
	}

	private ValueDefinition parseValueDef() throws SyntaxError {
		int line = currentToken.line;
		int column = currentToken.column;
		Type type;
		
		accept(VAL);
		
		if (currentToken.type == TokenType.INT)
		{
			acceptIt();
			
			type = IntType.getIntType();
		}
		else if (currentToken.type == TokenType.FLOAT)
		{
			acceptIt();
			
			type = FloatType.getFloatType();
		}
		else if (currentToken.type == TokenType.BOOL)
		{
			acceptIt();
			
			type = BoolType.getBoolType();
		}
		else if (currentToken.type == TokenType.VOID)
		{
			acceptIt();
			
			type = VoidType.getVoidType();
		}
		else if (currentToken.type == TokenType.STRING)
		{
			acceptIt();
			
			type = StringType.getStringType();
		}
		else if (currentToken.type == TokenType.VECTOR)
		{
			acceptIt();
			accept(LANGLE);
			
			ScalarType t;
			
			if (currentToken.type != TokenType.INT &&
				currentToken.type != TokenType.FLOAT)
				throw new SyntaxError(currentToken, INT, FLOAT);
			
			if (currentToken.type == TokenType.INT)
				t = IntType.getIntType();
			else
				t = FloatType.getFloatType();
			
			acceptIt();
			accept(TokenType.RANGLE);
			accept(LBRACKET);
			int dimension = parseIntLit();
			accept(RBRACKET);
			
			type = new VectorType(t, dimension);
			
		}
		else if (currentToken.type == TokenType.MATRIX )
		{
			acceptIt();
			accept(LANGLE);
			
			ScalarType t;
			
			if (currentToken.type != TokenType.INT &&
				currentToken.type != TokenType.FLOAT)
				throw new SyntaxError(currentToken, INT, FLOAT);
			
			if (currentToken.type == TokenType.INT)
				t = IntType.getIntType();
			else
				t = FloatType.getFloatType();
			
			acceptIt();
			accept(TokenType.RANGLE);
			accept(LBRACKET);
			int xDimension = parseIntLit();
			accept(RBRACKET);
			accept(LBRACKET);
			int yDimension = parseIntLit();
			accept(RBRACKET);
			
			type = new MatrixType(t, xDimension, yDimension);
			
		}
		else
		{
			throw new SyntaxError(currentToken, INT, FLOAT, BOOL, VOID, STRING, VECTOR, MATRIX);
		}
		
		String id = accept(ID);
		accept(ASSIGN);
		
		Expression expr = parseExpr();
		
		accept(SEMICOLON);
		
		return new ValueDefinition(line, column, type, id, expr);
	}

	private VariableDeclaration parseVarDecl() throws SyntaxError {
		int line = currentToken.line;
		int column = currentToken.column;
		Type type;
		
		accept(VAR);
		
		if (currentToken.type == TokenType.INT)
		{
			acceptIt();
			
			type = IntType.getIntType();
		}
		else if (currentToken.type == TokenType.FLOAT)
		{
			acceptIt();
			
			type = FloatType.getFloatType();
		}
		else if (currentToken.type == TokenType.BOOL)
		{
			acceptIt();
			
			type = BoolType.getBoolType();
		}
		else if (currentToken.type == TokenType.VOID)
		{
			acceptIt();
			
			type = VoidType.getVoidType();
		}
		else if (currentToken.type == TokenType.STRING)
		{
			acceptIt();
			
			type = StringType.getStringType();
		}
		else if (currentToken.type == TokenType.VECTOR)
		{
			acceptIt();
			accept(LANGLE);
			
			ScalarType t;
			
			if (currentToken.type != TokenType.INT &&
				currentToken.type != TokenType.FLOAT)
				throw new SyntaxError(currentToken, INT, FLOAT);
			
			if (currentToken.type == TokenType.INT)
				t = IntType.getIntType();
			else
				t = FloatType.getFloatType();
			
			acceptIt();
			accept(TokenType.RANGLE);
			accept(LBRACKET);
			int dimension = parseIntLit();
			accept(RBRACKET);
			
			type = new VectorType(t, dimension);
			
		}
		else if (currentToken.type == TokenType.MATRIX )
		{
			acceptIt();
			accept(LANGLE);
			
			ScalarType t;
			
			if (currentToken.type != TokenType.INT &&
				currentToken.type != TokenType.FLOAT)
				throw new SyntaxError(currentToken, INT, FLOAT);
			
			if (currentToken.type == TokenType.INT)
				t = IntType.getIntType();
			else
				t = FloatType.getFloatType();
			
			acceptIt();
			accept(TokenType.RANGLE);
			accept(LBRACKET);
			int xDimension = parseIntLit();
			accept(RBRACKET);
			accept(LBRACKET);
			int yDimension = parseIntLit();
			accept(RBRACKET);
			
			type = new MatrixType(t, xDimension, yDimension);
			
		}
		else
		{
			throw new SyntaxError(currentToken, INT, FLOAT, BOOL, VOID, STRING, VECTOR, MATRIX);
		}
		
		String id = accept(ID);
		accept(TokenType.SEMICOLON);
		
		return new VariableDeclaration(line, column, type, id);
	}

	private ReturnStatement parseReturn() throws SyntaxError {
		int line = currentToken.line;
		int column = currentToken.column;
		accept(RETURN);
		Expression e = parseExpr();
		accept(SEMICOLON);
		
		return new ReturnStatement(line, column, e);
	}

	private Statement parseAssignOrCall() throws SyntaxError {
		int line = currentToken.line;
		int column = currentToken.column;

		String name = accept(ID);

		Statement s;
		if (currentToken.type != LPAREN)
			s = parseAssign(name, line, column);
		else
			s = new CallStatement(line, column, parseCall(name, line, column));
		accept(SEMICOLON);
		
		return s;
	}

	private VariableAssignment parseAssign(String name, int line, int column) throws SyntaxError {
		Expression expr1;
		Expression expr2;
		
		if (currentToken.type == TokenType.LBRACKET)
		{
			acceptIt();
			expr1 = parseExpr();
			accept(RBRACKET);
		}
		
		if (currentToken.type == TokenType.LBRACKET)
		{
			acceptIt();
			expr2 = parseExpr();
			accept(RBRACKET);
		}
		
		accept(TokenType.ASSIGN);
		Expression expr = parseExpr();
		
		return new VariableAssignment(line, column, new LeftHandIdentifier(line, column, name), expr);
	}
	
	private CallExpression parseCall(String name, int line, int column) {
		CallExpression callExpression = new CallExpression(line, column, name);
		accept(LPAREN);
		if (currentToken.type != RPAREN) {
			callExpression.addActualParameter(parseExpr());
			while (currentToken.type != RPAREN) {
				accept(COMMA);
				callExpression.addActualParameter(parseExpr());
			}
		}
		accept(RPAREN);
		
		return callExpression;
	}

	private ForLoop parseFor() throws SyntaxError {
		int line = currentToken.line;
		int column = currentToken.column;
		
		acceptIt();
		accept(LPAREN);
		String varName = accept(ID);
		accept(ASSIGN);
		Expression initVal = parseExpr();
		accept(SEMICOLON);
		Expression condition = parseExpr();
		accept(SEMICOLON);
		String varName2 = accept(ID);
		accept(ASSIGN);
		Expression ex = parseExpr();
		accept(RPAREN);
		
		Statement statement = parseStatement();
		
		return new ForLoop(line, column, varName, initVal, condition, varName2, ex, statement);
	}

	private IfStatement parseIf() throws SyntaxError {
		int line = currentToken.line;
		int column = currentToken.column;
		
		acceptIt();
		accept(LPAREN);
		Expression expr = parseExpr();
		accept(RPAREN);
		Statement statement = parseStatement();
		
		IfStatement is;
		
		if (currentToken.type == ELSE)
		{
			acceptIt();
			Statement elseStatement = parseStatement();
			
			is = new IfStatement(line, column, expr, statement, elseStatement);
		}
		else
			is = new IfStatement(line, column, expr, statement);
		
		return is;
	}

	private CompoundStatement parseCompound() throws SyntaxError {
		int line = currentToken.line;
		int column = currentToken.column;
		
		accept(LBRACE);
		
		CompoundStatement cs = new CompoundStatement(line, column);
		
		while (currentToken.type != TokenType.RBRACE)
		{
			Statement s = parseStatement();
			cs.addStatement(s);
		}
			
		accept(RBRACE);
		
		return cs;
	}

	private Expression parseExpr() throws SyntaxError {
		return parseOr();
	}
	
	private Expression parseOr() throws SyntaxError {
		int line = currentToken.line;
		int column = currentToken.column;

		Expression x = parseAnd();
		while (currentToken.type == OR) {
			acceptIt();
			x = new Or(line, column, x, parseAnd());
		}
		return x;
	}

	private Expression parseAnd() throws SyntaxError {
		int line = currentToken.line;
		int column = currentToken.column;

		Expression x = parseNot();
		while (currentToken.type == AND) {
			acceptIt();
			x = new And(line, column, x, parseNot());
		}
		return x;
	}

	private Expression parseNot() throws SyntaxError {
		int line = currentToken.line;
		int column = currentToken.column;
		
		if (currentToken.type == NOT) {
			acceptIt();
			return new BoolNot(line, column, parseCompare());
		}
		return parseCompare();
	}

	private Expression parseCompare() throws SyntaxError {
		int line = currentToken.line;
		int column = currentToken.column;

		Expression x = parseAddSub();
		
		while (currentToken.type == RANGLE || 
			   currentToken.type == LANGLE ||
			   currentToken.type == CMPLE  ||
			   currentToken.type == CMPGE  ||
			   currentToken.type == CMPEQ  ||
			   currentToken.type == CMPNE  )
		{
			mavlc.ast.nodes.expression.Compare.Comparison comparator;
			
			if (currentToken.type == RANGLE)
				comparator = GREATER;
			else if (currentToken.type == LANGLE)
				comparator = LESS;
			else if (currentToken.type == CMPLE)
				comparator = LESS_EQUAL;
			else if (currentToken.type == CMPGE)
				comparator = GREATER_EQUAL;
			else if (currentToken.type == CMPEQ)
				comparator = EQUAL;
			else
				comparator = NOT_EQUAL;
			
			acceptIt();
			x = new Compare(line, column, x, parseAddSub(), comparator);
		}
		return x;
	}

	private Expression parseAddSub() throws SyntaxError {
		int line = currentToken.line;
		int column = currentToken.column;

		Expression x = parseMulDiv();
		
		while (currentToken.type == ADD || currentToken.type == SUB) {
			if (currentToken.type == ADD)
			{
				acceptIt();
				x = new Addition(line, column, x, parseMulDiv());
			}
			else
			{
				acceptIt();
				x = new Subtraction(line, column, x, parseMulDiv());
			}
		}
		return x;
	}

	private Expression parseMulDiv() throws SyntaxError {
		int line = currentToken.line;
		int column = currentToken.column;

		Expression x = parseUnaryMinus();
		
		while (currentToken.type == MULT || currentToken.type == DIV) {
			if (currentToken.type == MULT)
			{
				acceptIt();
				x = new Multiplication(line, column, x, parseUnaryMinus());
			}
			else
			{
				acceptIt();
				x = new Division(line, column, x, parseUnaryMinus());
			}
		}
		return x;
	}

	private Expression parseUnaryMinus() throws SyntaxError {
		int line = currentToken.line;
		int column = currentToken.column;

		if (currentToken.type == SUB) {
			acceptIt();
			return new UnaryMinus(line, column, parseDim());
		} else {
			return parseDim();
		}
	}

	private Expression parseDim() throws SyntaxError {
		int line = currentToken.line;
		int column = currentToken.column;

		Expression x = parseElementSelect();
		switch (currentToken.type) {
		case XDIM: acceptIt(); return new MatrixXDimension(line, column, x);
		case YDIM: acceptIt(); return new MatrixYDimension(line, column, x);
		case DIM:  acceptIt(); return new VectorDimension(line, column, x);
		default:
			return x;
		}
	}

	private Expression parseElementSelect() throws SyntaxError {
		int line = currentToken.line;
		int column = currentToken.column;

		Expression x = parseDotProd();

		while (currentToken.type == LBRACKET) {
			acceptIt();
			Expression idx = parseExpr();
			accept(RBRACKET);
			x = new ElementSelect(line, column, x, idx);
		}

		return x;
	}

	private Expression parseDotProd() throws SyntaxError {
		int line = currentToken.line;
		int column = currentToken.column;

		Expression x = parseMatrixMul();
		while (currentToken.type == DOTPROD) {
			acceptIt();
			x = new DotProduct(line, column, x, parseMatrixMul());
		}
		
		return x;
	}

	private Expression parseMatrixMul() throws SyntaxError {
		int line = currentToken.line;
		int column = currentToken.column;

		Expression x = parseSubrange();
		while (currentToken.type == MATMULT) {
			acceptIt();
			x = new MatrixMultiplication(line, column, x, parseSubrange());
		}
		return x;

	}

	private Expression parseSubrange() throws SyntaxError {
		int line = currentToken.line;
		int column = currentToken.column;
		
		Expression x = parseAtom();
		
		if (currentToken.type == LBRACE)
		{
			acceptIt();
			Expression expr1 = parseExpr();
			accept(COLON);
			Expression expr2 = parseExpr();
			accept(COLON);
			Expression expr3 = parseExpr();
			accept(RBRACE);
			
			if (currentToken.type == LBRACE)
			{
				acceptIt();
				Expression expr4 = parseExpr();
				accept(COLON);
				Expression expr5 = parseExpr();
				accept(COLON);
				Expression expr6 = parseExpr();
				accept(RBRACE);
				
				x = new SubMatrix(line, column, x, expr2, expr1, expr3, expr5, expr4, expr6);
			}
			else
			{
				x = new SubVector(line, column, x, expr2, expr1, expr3);
			}
		}
		
		return x;
	}

	private Expression parseAtom() throws SyntaxError {
		int line = currentToken.line;
		int column = currentToken.column;

		switch (currentToken.type) {
		case INTLIT:    return new IntValue(line, column, parseIntLit());
		case FLOATLIT:  return new FloatValue(line, column, parseFloatLit());
		case BOOLLIT:   return new BoolValue(line, column, parseBoolLit());
		case STRINGLIT: return new StringValue(line, column, accept(STRINGLIT));
		default: /* check other cases below */
		}

		if (currentToken.type == ID) {
			String name = accept(ID);
			if (currentToken.type != LPAREN)
				return new IdentifierReference(line, column, name);
			else
				return parseCall(name, line, column);
		}

		if (currentToken.type == LPAREN) {
			acceptIt();
			Expression x = parseExpr();
			accept(RPAREN);
			return x;
		}

		if (currentToken.type == LBRACKET) {
			acceptIt();
			StructureInit s = new StructureInit(line, column);
			s.addElement(parseExpr());
			while (currentToken.type == COMMA) {
				accept(COMMA);
				s.addElement(parseExpr());
			}
			accept(RBRACKET);
			return s;
		}

		throw new SyntaxError(currentToken, INTLIT, FLOATLIT, BOOLLIT, STRINGLIT, ID, LPAREN, LBRACKET);
	}

	private int parseIntLit() throws SyntaxError {
		String s = accept(INTLIT);
		return Integer.parseInt(s);
	}

	private float parseFloatLit() throws SyntaxError {
		return Float.parseFloat(accept(FLOATLIT));
	}

	private boolean parseBoolLit() throws SyntaxError {
		return Boolean.parseBoolean(accept(BOOLLIT));
	}
}
