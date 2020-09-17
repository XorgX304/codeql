/**
 * Provides Java-specific definitions for use in sign analysis.
 */

import semmle.code.java.dataflow.RangeUtils as RU
private import semmle.code.java.dataflow.SSA as Ssa
private import semmle.code.java.controlflow.Guards as G
private import java as J
private import semmle.code.java.Reflection as Reflection
private import semmle.code.java.Collections as Collections
private import semmle.code.java.Maps as Maps
private import Sign
private import SignAnalysisCommon
private import SsaReadPositionCommon

class ConstantIntegerExpr = RU::ConstantIntegerExpr;

class Guard = G::Guard;

class SsaVariable = Ssa::SsaVariable;

class SsaPhiNode = Ssa::SsaPhiNode;

class VarAccess = J::VarAccess;

class FieldAccess = J::FieldAccess;

class CharacterLiteral = J::CharacterLiteral;

class IntegerLiteral = J::IntegerLiteral;

class LongLiteral = J::LongLiteral;

class CastExpr = J::CastExpr;

class Type = J::Type;

class Expr = J::Expr;

class ComparisonExpr = J::ComparisonExpr;

class NumericOrCharType = J::NumericOrCharType;

float getNonIntegerValue(Expr e) {
  result = e.(J::LongLiteral).getValue().toFloat() or
  result = e.(J::FloatingPointLiteral).getValue().toFloat() or
  result = e.(J::DoubleLiteral).getValue().toFloat()
}

predicate containerSizeAccess(Expr e) {
  e.(J::MethodAccess).getMethod() instanceof J::StringLengthMethod
  or
  e.(J::MethodAccess).getMethod() instanceof Collections::CollectionSizeMethod
  or
  e.(J::MethodAccess).getMethod() instanceof Maps::MapSizeMethod
}

predicate unknownIntegerAccess(Expr e) {
  e instanceof J::ArrayAccess and e.getType() instanceof J::NumericOrCharType
  or
  e instanceof J::MethodAccess and e.getType() instanceof J::NumericOrCharType
  or
  e instanceof J::ClassInstanceExpr and e.getType() instanceof J::NumericOrCharType
}

Sign explicitSsaDefSign(SsaVariable v) {
  exists(J::VariableUpdate def | def = v.(Ssa::SsaExplicitUpdate).getDefiningExpr() |
    result = exprSign(def.(J::VariableAssign).getSource())
    or
    exists(J::EnhancedForStmt for | def = for.getVariable())
    or
    result = exprSign(def.(J::PostIncExpr).getExpr()).inc()
    or
    result = exprSign(def.(J::PreIncExpr).getExpr()).inc()
    or
    result = exprSign(def.(J::PostDecExpr).getExpr()).dec()
    or
    result = exprSign(def.(J::PreDecExpr).getExpr()).dec()
    or
    exists(J::AssignOp a | a = def and result = exprSign(a))
  )
}

Sign implicitSsaDefSign(SsaVariable v) {
  result = fieldSign(v.(Ssa::SsaImplicitUpdate).getSourceVariable().getVariable())
  or
  result = fieldSign(v.(Ssa::SsaImplicitInit).getSourceVariable().getVariable())
  or
  exists(J::Parameter p | v.(Ssa::SsaImplicitInit).isParameterDefinition(p))
}

/** Gets a possible sign for `f`. */
Sign fieldSign(J::Field f) {
  result = exprSign(f.getAnAssignedValue())
  or
  exists(J::PostIncExpr inc | inc.getExpr() = f.getAnAccess() and result = fieldSign(f).inc())
  or
  exists(J::PreIncExpr inc | inc.getExpr() = f.getAnAccess() and result = fieldSign(f).inc())
  or
  exists(J::PostDecExpr inc | inc.getExpr() = f.getAnAccess() and result = fieldSign(f).dec())
  or
  exists(J::PreDecExpr inc | inc.getExpr() = f.getAnAccess() and result = fieldSign(f).dec())
  or
  exists(J::AssignOp a | a.getDest() = f.getAnAccess() | result = exprSign(a))
  or
  exists(Reflection::ReflectiveFieldAccess rfa | rfa.inferAccessedField() = f)
  or
  if f.fromSource()
  then not exists(f.getInitializer()) and result = TZero()
  else
    if f instanceof J::ArrayLengthField
    then result != TNeg()
    else
      if f.hasName("MAX_VALUE")
      then result = TPos()
      else
        if f.hasName("MIN_VALUE")
        then result = TNeg()
        else any()
}

Sign specificSubExprSign(Expr e) {
  result = exprSign(e.(J::AssignExpr).getSource())
  or
  result = exprSign(e.(J::PlusExpr).getExpr())
  or
  result = exprSign(e.(J::PostIncExpr).getExpr())
  or
  result = exprSign(e.(J::PostDecExpr).getExpr())
  or
  result = exprSign(e.(J::PreIncExpr).getExpr()).inc()
  or
  result = exprSign(e.(J::PreDecExpr).getExpr()).dec()
  or
  result = exprSign(e.(J::MinusExpr).getExpr()).neg()
  or
  result = exprSign(e.(J::BitNotExpr).getExpr()).bitnot()
  or
  exists(J::DivExpr div |
    div = e and
    result = exprSign(div.getLeftOperand()) and
    result != TZero()
  |
    div.getRightOperand().(J::FloatingPointLiteral).getValue().toFloat() = 0 or
    div.getRightOperand().(J::DoubleLiteral).getValue().toFloat() = 0
  )
  or
  exists(Sign s1, Sign s2 | binaryOpSigns(e, s1, s2) |
    (e instanceof J::AssignAddExpr or e instanceof J::AddExpr) and
    result = s1.add(s2)
    or
    (e instanceof J::AssignSubExpr or e instanceof J::SubExpr) and
    result = s1.add(s2.neg())
    or
    (e instanceof J::AssignMulExpr or e instanceof J::MulExpr) and
    result = s1.mul(s2)
    or
    (e instanceof J::AssignDivExpr or e instanceof J::DivExpr) and
    result = s1.div(s2)
    or
    (e instanceof J::AssignRemExpr or e instanceof J::RemExpr) and
    result = s1.rem(s2)
    or
    (e instanceof J::AssignAndExpr or e instanceof J::AndBitwiseExpr) and
    result = s1.bitand(s2)
    or
    (e instanceof J::AssignOrExpr or e instanceof J::OrBitwiseExpr) and
    result = s1.bitor(s2)
    or
    (e instanceof J::AssignXorExpr or e instanceof J::XorBitwiseExpr) and
    result = s1.bitxor(s2)
    or
    (e instanceof J::AssignLShiftExpr or e instanceof J::LShiftExpr) and
    result = s1.lshift(s2)
    or
    (e instanceof J::AssignRShiftExpr or e instanceof J::RShiftExpr) and
    result = s1.rshift(s2)
    or
    (e instanceof J::AssignURShiftExpr or e instanceof J::URShiftExpr) and
    result = s1.urshift(s2)
  )
  or
  result = exprSign(e.(J::ChooseExpr).getAResultExpr())
  or
  result = exprSign(e.(J::CastExpr).getExpr())
}

private Sign binaryOpLhsSign(Expr e) {
  result = exprSign(e.(J::BinaryExpr).getLeftOperand()) or
  result = exprSign(e.(J::AssignOp).getDest())
}

private Sign binaryOpRhsSign(Expr e) {
  result = exprSign(e.(J::BinaryExpr).getRightOperand()) or
  result = exprSign(e.(J::AssignOp).getRhs())
}

pragma[noinline]
private predicate binaryOpSigns(Expr e, Sign lhs, Sign rhs) {
  lhs = binaryOpLhsSign(e) and
  rhs = binaryOpRhsSign(e)
}

Expr getARead(SsaVariable v) { result = v.getAUse() }

J::Field getField(FieldAccess fa) { result = fa.getField() }

Expr getAnExpression(SsaReadPositionBlock bb) { result = bb.getBlock().getANode() }

Guard getComparisonGuard(J::ComparisonExpr ce) { result = ce }

Expr ssaRead(SsaVariable v, int delta) { result = RU::ssaRead(v, delta) }

predicate guardControlsSsaRead(Guard guard, SsaReadPosition controlled, boolean testIsTrue) {
  RU::guardControlsSsaRead(guard, controlled, testIsTrue)
}
