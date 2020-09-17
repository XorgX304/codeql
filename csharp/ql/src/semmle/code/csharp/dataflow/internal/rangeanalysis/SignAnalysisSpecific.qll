/**
 * Provides C#-specific definitions for use in sign analysis.
 */

private import SsaUtils as SU
private import csharp as CS
private import ConstantUtils as CU
private import semmle.code.csharp.controlflow.Guards as G
private import Linq.Helpers as Linq
private import Sign
private import SignAnalysisCommon
private import SsaReadPositionCommon
private import semmle.code.csharp.commons.ComparisonTest

private class BooleanValue = G::AbstractValues::BooleanValue;

class Guard = G::Guard;

class ConstantIntegerExpr = CU::ConstantIntegerExpr;

class SsaVariable = CS::Ssa::Definition;

class SsaPhiNode = CS::Ssa::PhiNode;

class VarAccess = CS::AssignableAccess;

class FieldAccess = CS::FieldAccess;

class CharacterLiteral = CS::CharLiteral;

class IntegerLiteral = CS::IntegerLiteral;

class LongLiteral = CS::LongLiteral;

class CastExpr = CS::CastExpr;

class Type = CS::Type;

class Expr = CS::Expr;

float getNonIntegerValue(Expr e) {
  exists(string s |
    s = e.getValue() and
    result = s.toFloat() and
    not exists(s.toInt())
  )
}

predicate containerSizeAccess(Expr e) {
  exists(CS::Property p | p = e.(CS::PropertyAccess).getTarget() |
    CU::propertyOverrides(p, "System.Collections.Generic.IEnumerable<>", "Count") or
    CU::propertyOverrides(p, "System.Collections.ICollection", "Count") or
    CU::propertyOverrides(p, "System.String", "Length") or
    CU::propertyOverrides(p, "System.Array", "Length")
  )
  or
  e instanceof Linq::CountCall
}

class NumericOrCharType extends Type {
  NumericOrCharType() {
    this instanceof CS::CharType or
    this instanceof CS::IntegralType or
    this instanceof CS::FloatingPointType or
    this instanceof CS::DecimalType
  }
}

predicate unknownIntegerAccess(Expr e) {
  // array access, indexer access
  e instanceof CS::ElementAccess and e.getType() instanceof NumericOrCharType
  or
  // property access
  e instanceof CS::PropertyAccess and e.getType() instanceof NumericOrCharType
  or
  //method call, local function call, ctor call, ...
  e instanceof CS::Call and e.getType() instanceof NumericOrCharType
  or
  // checked
  e instanceof CS::CheckedExpr and e.getType() instanceof NumericOrCharType
  or
  // unchecked
  e instanceof CS::UncheckedExpr and e.getType() instanceof NumericOrCharType
}

Sign explicitSsaDefSign(CS::Ssa::ExplicitDefinition v) {
  exists(CS::AssignableDefinition def | def = v.getADefinition() |
    result = exprSign(def.getSource())
    or
    not exists(def.getSource()) and
    not def.getElement() instanceof CS::MutatorOperation
    or
    result = exprSign(def.getElement().(CS::IncrementOperation).getOperand()).inc()
    or
    result = exprSign(def.getElement().(CS::DecrementOperation).getOperand()).dec()
  )
}

Sign implicitSsaDefSign(CS::Ssa::ImplicitDefinition v) {
  result = fieldSign(v.getSourceVariable().getAssignable()) or
  not v.getSourceVariable().getAssignable() instanceof CS::Field
}

/** Gets a possible sign for `f`. */
Sign fieldSign(CS::Field f) {
  result = exprSign(f.getAnAssignedValue())
  or
  any(CS::IncrementOperation inc).getOperand() = f.getAnAccess() and result = fieldSign(f).inc()
  or
  any(CS::DecrementOperation dec).getOperand() = f.getAnAccess() and result = fieldSign(f).dec()
  or
  exists(CS::AssignOperation a | a.getLValue() = f.getAnAccess() | result = exprSign(a))
  or
  f.fromSource() and not exists(f.getInitializer()) and result = TZero()
}

Sign specificSubExprSign(Expr e) {
  result = exprSign(e.(CS::AssignExpr).getRValue())
  or
  result = exprSign(e.(CS::AssignOperation).getExpandedAssignment())
  or
  result = exprSign(e.(CS::UnaryPlusExpr).getOperand())
  or
  result = exprSign(e.(CS::PostIncrExpr).getOperand())
  or
  result = exprSign(e.(CS::PostDecrExpr).getOperand())
  or
  result = exprSign(e.(CS::PreIncrExpr).getOperand()).inc()
  or
  result = exprSign(e.(CS::PreDecrExpr).getOperand()).dec()
  or
  result = exprSign(e.(CS::UnaryMinusExpr).getOperand()).neg()
  or
  result = exprSign(e.(CS::ComplementExpr).getOperand()).bitnot()
  or
  e =
    any(CS::DivExpr div |
      result = exprSign(div.getLeftOperand()) and
      result != TZero() and
      div.getRightOperand().(CS::RealLiteral).getValue().toFloat() = 0
    )
  or
  exists(Sign s1, Sign s2 | binaryOpSigns(e, s1, s2) |
    e instanceof CS::AddExpr and result = s1.add(s2)
    or
    e instanceof CS::SubExpr and result = s1.add(s2.neg())
    or
    e instanceof CS::MulExpr and result = s1.mul(s2)
    or
    e instanceof CS::DivExpr and result = s1.div(s2)
    or
    e instanceof CS::RemExpr and result = s1.rem(s2)
    or
    e instanceof CS::BitwiseAndExpr and result = s1.bitand(s2)
    or
    e instanceof CS::BitwiseOrExpr and result = s1.bitor(s2)
    or
    e instanceof CS::BitwiseXorExpr and result = s1.bitxor(s2)
    or
    e instanceof CS::LShiftExpr and result = s1.lshift(s2)
    or
    e instanceof CS::RShiftExpr and result = s1.rshift(s2)
  )
  or
  result = exprSign(e.(CS::ConditionalExpr).getThen())
  or
  result = exprSign(e.(CS::ConditionalExpr).getElse())
  or
  result = exprSign(e.(CS::SwitchExpr).getACase().getBody())
  or
  result = exprSign(e.(CastExpr).getExpr())
}

private Sign binaryOpLhsSign(CS::BinaryOperation e) { result = exprSign(e.getLeftOperand()) }

private Sign binaryOpRhsSign(CS::BinaryOperation e) { result = exprSign(e.getRightOperand()) }

pragma[noinline]
private predicate binaryOpSigns(Expr e, Sign lhs, Sign rhs) {
  lhs = binaryOpLhsSign(e) and
  rhs = binaryOpRhsSign(e)
}

Expr getARead(SsaVariable v) { result = v.getARead() }

CS::Field getField(FieldAccess fa) { result = fa.getTarget() }

Expr getAnExpression(SsaReadPositionBlock bb) { result = bb.getBlock().getANode().getElement() }

Guard getComparisonGuard(ComparisonExpr ce) { result = ce.getExpr() }

/**
 * Holds if `guard` controls the position `controlled` with the value `testIsTrue`.
 */
predicate guardControlsSsaRead(Guard guard, SsaReadPosition controlled, boolean testIsTrue) {
  exists(BooleanValue b | b.getValue() = testIsTrue |
    guard.controlsBasicBlock(controlled.(SsaReadPositionBlock).getBlock(), b)
  )
}

/** A relational comparison */
class ComparisonExpr extends ComparisonTest {
  private boolean strict;

  ComparisonExpr() {
    this.getComparisonKind() =
      any(ComparisonKind ck |
        ck.isLessThan() and strict = true
        or
        ck.isLessThanEquals() and
        strict = false
      )
  }

  /**
   * Gets the operand on the "greater" (or "greater-or-equal") side
   * of this relational expression, that is, the side that is larger
   * if the overall expression evaluates to `true`; for example on
   * `x <= 20` this is the `20`, and on `y > 0` it is `y`.
   */
  Expr getGreaterOperand() { result = this.getSecondArgument() }

  /**
   * Gets the operand on the "lesser" (or "lesser-or-equal") side
   * of this relational expression, that is, the side that is smaller
   * if the overall expression evaluates to `true`; for example on
   * `x <= 20` this is `x`, and on `y > 0` it is the `0`.
   */
  Expr getLesserOperand() { result = this.getFirstArgument() }

  /** Holds if this comparison is strict, i.e. `<` or `>`. */
  predicate isStrict() { strict = true }
}

Expr ssaRead(SsaVariable v, int delta) { result = SU::ssaRead(v, delta) }
