/**
 * Provides C#-specific definitions for use in sign analysis.
 */
module Private {
  import ConstantUtils
  import SsaUtils
  import csharp
  import Ssa
  private import SsaReadPositionCommon
  private import semmle.code.csharp.controlflow.Guards as G
  private import Linq.Helpers as Linq
  private import Sign
  private import SignAnalysisCommon
  private import semmle.code.csharp.commons.ComparisonTest

  private class BooleanValue = G::AbstractValues::BooleanValue;

  class CharacterLiteral = CharLiteral;

  class SsaVariable = Definition;

  class SsaPhiNode = Ssa::PhiNode;

  class VarAccess = AssignableAccess;

  class Guard = G::Guard;

  float getNonIntegerValue(Expr e) {
    exists(string s |
      s = e.getValue() and
      result = s.toFloat() and
      not exists(s.toInt())
    )
  }

  predicate containerSizeAccess(Expr e) {
    exists(Property p | p = e.(PropertyAccess).getTarget() |
      propertyOverrides(p, "System.Collections.Generic.IEnumerable<>", "Count") or
      propertyOverrides(p, "System.Collections.ICollection", "Count") or
      propertyOverrides(p, "System.String", "Length") or
      propertyOverrides(p, "System.Array", "Length")
    )
    or
    e instanceof Linq::CountCall
  }

  class NumericOrCharType extends Type {
    NumericOrCharType() {
      this instanceof CharType or
      this instanceof IntegralType or
      this instanceof FloatingPointType or
      this instanceof DecimalType
    }
  }

  predicate unknownIntegerAccess(Expr e) {
    // array access, indexer access
    e instanceof ElementAccess and e.getType() instanceof NumericOrCharType
    or
    // property access
    e instanceof PropertyAccess and e.getType() instanceof NumericOrCharType
    or
    //method call, local function call, ctor call, ...
    e instanceof Call and e.getType() instanceof NumericOrCharType
  }

  Sign explicitSsaDefSign(ExplicitDefinition v) {
    exists(AssignableDefinition def | def = v.getADefinition() |
      result = exprSign(def.getSource())
      or
      not exists(def.getSource()) and
      not def.getElement() instanceof MutatorOperation
      or
      result = exprSign(def.getElement().(IncrementOperation).getOperand()).inc()
      or
      result = exprSign(def.getElement().(DecrementOperation).getOperand()).dec()
    )
  }

  Sign implicitSsaDefSign(ImplicitDefinition v) {
    result = fieldSign(v.getSourceVariable().getAssignable()) or
    not v.getSourceVariable().getAssignable() instanceof Field
  }

  /** Gets a possible sign for `f`. */
  Sign fieldSign(Field f) {
    result = exprSign(f.getAnAssignedValue())
    or
    any(IncrementOperation inc).getOperand() = f.getAnAccess() and result = fieldSign(f).inc()
    or
    any(DecrementOperation dec).getOperand() = f.getAnAccess() and result = fieldSign(f).dec()
    or
    exists(AssignOperation a | a.getLValue() = f.getAnAccess() | result = exprSign(a))
    or
    f.fromSource() and not exists(f.getInitializer()) and result = TZero()
  }

  Sign specificSubExprSign(Expr e) {
    result = exprSign(e.(AssignExpr).getRValue())
    or
    result = exprSign(e.(AssignOperation).getExpandedAssignment())
    or
    result = exprSign(e.(UnaryPlusExpr).getOperand())
    or
    result = exprSign(e.(PostIncrExpr).getOperand())
    or
    result = exprSign(e.(PostDecrExpr).getOperand())
    or
    result = exprSign(e.(PreIncrExpr).getOperand()).inc()
    or
    result = exprSign(e.(PreDecrExpr).getOperand()).dec()
    or
    result = exprSign(e.(UnaryMinusExpr).getOperand()).neg()
    or
    result = exprSign(e.(ComplementExpr).getOperand()).bitnot()
    or
    e =
      any(DivExpr div |
        result = exprSign(div.getLeftOperand()) and
        result != TZero() and
        div.getRightOperand().(RealLiteral).getValue().toFloat() = 0
      )
    or
    exists(Sign s1, Sign s2 | binaryOpSigns(e, s1, s2) |
      e instanceof AddExpr and result = s1.add(s2)
      or
      e instanceof SubExpr and result = s1.add(s2.neg())
      or
      e instanceof MulExpr and result = s1.mul(s2)
      or
      e instanceof DivExpr and result = s1.div(s2)
      or
      e instanceof RemExpr and result = s1.rem(s2)
      or
      e instanceof BitwiseAndExpr and result = s1.bitand(s2)
      or
      e instanceof BitwiseOrExpr and result = s1.bitor(s2)
      or
      e instanceof BitwiseXorExpr and result = s1.bitxor(s2)
      or
      e instanceof LShiftExpr and result = s1.lshift(s2)
      or
      e instanceof RShiftExpr and result = s1.rshift(s2)
    )
    or
    result = exprSign(e.(ConditionalExpr).getThen())
    or
    result = exprSign(e.(ConditionalExpr).getElse())
    or
    result = exprSign(e.(SwitchExpr).getACase().getBody())
    or
    result = exprSign(e.(CastExpr).getExpr())
  }

  private Sign binaryOpLhsSign(BinaryOperation e) { result = exprSign(e.getLeftOperand()) }

  private Sign binaryOpRhsSign(BinaryOperation e) { result = exprSign(e.getRightOperand()) }

  pragma[noinline]
  private predicate binaryOpSigns(Expr e, Sign lhs, Sign rhs) {
    lhs = binaryOpLhsSign(e) and
    rhs = binaryOpRhsSign(e)
  }

  Expr getARead(SsaVariable v) { result = v.getARead() }

  Field getField(FieldAccess fa) { result = fa.getTarget() }

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
}
