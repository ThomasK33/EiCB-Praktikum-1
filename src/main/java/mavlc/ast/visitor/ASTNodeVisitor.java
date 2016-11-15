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
package mavlc.ast.visitor;

import mavlc.ast.nodes.expression.Addition;
import mavlc.ast.nodes.expression.And;
import mavlc.ast.nodes.expression.BinaryExpression;
import mavlc.ast.nodes.expression.BoolNot;
import mavlc.ast.nodes.expression.BoolValue;
import mavlc.ast.nodes.expression.CallExpression;
import mavlc.ast.nodes.expression.Compare;
import mavlc.ast.nodes.expression.Division;
import mavlc.ast.nodes.expression.DotProduct;
import mavlc.ast.nodes.expression.ElementSelect;
import mavlc.ast.nodes.expression.Expression;
import mavlc.ast.nodes.expression.FloatValue;
import mavlc.ast.nodes.expression.IdentifierReference;
import mavlc.ast.nodes.expression.IntValue;
import mavlc.ast.nodes.expression.MatrixMultiplication;
import mavlc.ast.nodes.expression.MatrixXDimension;
import mavlc.ast.nodes.expression.MatrixYDimension;
import mavlc.ast.nodes.expression.Multiplication;
import mavlc.ast.nodes.expression.Or;
import mavlc.ast.nodes.expression.StringValue;
import mavlc.ast.nodes.expression.StructureInit;
import mavlc.ast.nodes.expression.SubMatrix;
import mavlc.ast.nodes.expression.SubVector;
import mavlc.ast.nodes.expression.Subtraction;
import mavlc.ast.nodes.expression.UnaryExpression;
import mavlc.ast.nodes.expression.UnaryMinus;
import mavlc.ast.nodes.expression.VectorDimension;
import mavlc.ast.nodes.function.FormalParameter;
import mavlc.ast.nodes.function.Function;
import mavlc.ast.nodes.module.Module;
import mavlc.ast.nodes.statement.CallStatement;
import mavlc.ast.nodes.statement.CompoundStatement;
import mavlc.ast.nodes.statement.Declaration;
import mavlc.ast.nodes.statement.ForLoop;
import mavlc.ast.nodes.statement.IfStatement;
import mavlc.ast.nodes.statement.LeftHandIdentifier;
import mavlc.ast.nodes.statement.MatrixLHSIdentifier;
import mavlc.ast.nodes.statement.ReturnStatement;
import mavlc.ast.nodes.statement.Statement;
import mavlc.ast.nodes.statement.ValueDefinition;
import mavlc.ast.nodes.statement.VariableAssignment;
import mavlc.ast.nodes.statement.VariableDeclaration;
import mavlc.ast.nodes.statement.VectorLHSIdentifier;

/**
 * AST-node visitor interface.
 *
 * @param <RetTy> The return type of the visit-methods.
 * @param <ArgTy> The type of the additional argument.
 */
public interface ASTNodeVisitor<RetTy, ArgTy> {
	
	public RetTy visitModule(Module module, ArgTy obj);

	public RetTy visitFunction(Function functionNode, ArgTy obj);

	public RetTy visitFormalParameter(FormalParameter formalParameter, ArgTy obj);
	
	/*
	 * Statements
	 */
	public RetTy visitStatement(Statement statement, ArgTy obj);
	
	public RetTy visitDeclaration(Declaration declaration, ArgTy obj);

	public RetTy visitValueDefinition(ValueDefinition valueDefinition, ArgTy obj);

	public RetTy visitVariableDeclaration(VariableDeclaration variableDeclaration, ArgTy obj);
	
	public RetTy visitVariableAssignment(VariableAssignment variableAssignment, ArgTy obj);

	public RetTy visitLeftHandIdentifier(LeftHandIdentifier leftHandIdentifier, ArgTy obj);

	public RetTy visitMatrixLHSIdentifier(MatrixLHSIdentifier matrixLHSIdentifier, ArgTy obj);

	public RetTy visitVectorLHSIdentifier(VectorLHSIdentifier vectorLHSIdentifier, ArgTy obj);

	public RetTy visitForLoop(ForLoop forLoop, ArgTy obj);

	public RetTy visitIfStatement(IfStatement ifStatement, ArgTy obj);
	
	public RetTy visitCallStatement(CallStatement callStatement, ArgTy obj);

	public RetTy visitReturnStatement(ReturnStatement returnStatement, ArgTy obj);

	public RetTy visitCompoundStatement(CompoundStatement compoundStatement, ArgTy obj);
	
	/*
	 * Expressions
	 */
	public RetTy visitExpression(Expression expression, ArgTy obj);
	
	/*
	 * Binary Expressions
	 */
	public RetTy visitBinaryExpression(BinaryExpression binaryExpression, ArgTy obj);
	
	public RetTy visitMatrixMultiplication(MatrixMultiplication matrixMultiplication, ArgTy obj);
	
	public RetTy visitDotProduct(DotProduct dotProduct, ArgTy obj);
	
	public RetTy visitMultiplication(Multiplication multiplication, ArgTy obj);
	
	public RetTy visitDivision(Division division, ArgTy obj);
	
	public RetTy visitAddition(Addition addition, ArgTy obj);
	
	public RetTy visitSubtraction(Subtraction subtraction, ArgTy obj);
	
	public RetTy visitCompare(Compare compare, ArgTy obj);
	
	public RetTy visitAnd(And and, ArgTy obj);
	
	public RetTy visitOr(Or or, ArgTy obj);
	
	/*
	 * Unary Expressions
	 */
	public RetTy visitUnaryExpression(UnaryExpression unaryExpression, ArgTy obj);
	
	public RetTy visitMatrixXDimension(MatrixXDimension xDimension, ArgTy obj);
	
	public RetTy visitMatrixYDimension(MatrixYDimension yDimension, ArgTy obj);
	
	public RetTy visitVectorDimension(VectorDimension vectorDimension, ArgTy obj);
	
	public RetTy visitUnaryMinus(UnaryMinus unaryMinus, ArgTy obj);
	
	public RetTy visitBoolNot(BoolNot boolNot, ArgTy obj);

	/*
	 * Call expression
	 */
	public RetTy visitCallExpression(CallExpression callExpression, ArgTy obj);
	
	/*
	 * Matrix- and Vector-primitives
	 */
	public RetTy visitElementSelect(ElementSelect elementSelect, ArgTy obj);
	
	public RetTy visitSubMatrix(SubMatrix subSelect, ArgTy obj);
	
	public RetTy visitSubVector(SubVector subVector, ArgTy obj);
	
	public RetTy visitStructureInit(StructureInit structureInit, ArgTy obj);

	/*
	 * Primitive and String-values
	 */
	public RetTy visitStringValue(StringValue stringValue, ArgTy obj);

	public RetTy visitBoolValue(BoolValue boolValue, ArgTy obj);

	public RetTy visitIntValue(IntValue intValue, ArgTy obj);

	public RetTy visitFloatValue(FloatValue floatValue, ArgTy obj);
	
	/*
	 * Identifier reference
	 */
	public RetTy visitIdentifierReference(IdentifierReference identifierReference, ArgTy obj);


}
