/**
 * Provides C#-specific definitions for use in sign analysis.
 */
module Private {
  import csharp
  import RangeUtils
  import ConstantUtils
  import SsaUtils
  private import Ssa
  private import SsaReadPositionCommon
  private import semmle.code.csharp.controlflow.Guards as G
  private import Linq.Helpers as Linq
  private import Sign::Internal
  private import SignAnalysisCommon

  class CharacterLiteral = CharLiteral;

  class SsaVariable = Definition;

  class SsaPhiNode = PhiNode;

  class ComparisonExpr = RelationalOperation;

  class VarAccess = AssignableAccess;

  class Guard = G::Guard;

  float getNonIntegerValue(Expr e) {
    result = e.(LongLiteral).getValue().toFloat() or
    result = e.(RealLiteral).getValue().toFloat()
  }

  predicate containerSizeAccess(Expr e) {
    propertyOverrides(e.(PropertyAccess).getTarget(), "System.Collections.Generic.IEnumerable<>",
      "Count") or
    propertyOverrides(e.(PropertyAccess).getTarget(), "System.Collections.ICollection", "Count") or
    propertyOverrides(e.(PropertyAccess).getTarget(), "System.String", "Length") or
    propertyOverrides(e.(PropertyAccess).getTarget(), "System.Array", "Length") or
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

  Sign explicitSsaDefSign(SsaVariable v) {
    exists(AssignableDefinition def | def = v.(ExplicitDefinition).getADefinition() |
      result = exprSign(def.getSource())
      or
      not exists(def.getSource()) and
      not def.getElement() instanceof MutatorOperation
      or
      result = exprSign(def.getElement().(PostIncrExpr).getOperand()).inc()
      or
      result = exprSign(def.getElement().(PreIncrExpr).getOperand()).inc()
      or
      result = exprSign(def.getElement().(PostDecrExpr).getOperand()).dec()
      or
      result = exprSign(def.getElement().(PreDecrExpr).getOperand()).dec()
    )
  }

  Sign implicitSsaDefSign(SsaVariable v) {
    v =
      any(ImplicitDefinition id |
        result = fieldSign(id.getSourceVariable().getAssignable()) or
        not id.getSourceVariable().getAssignable() instanceof Field
      )
  }

  /** Gets a possible sign for `f`. */
  Sign fieldSign(Field f) {
    result = exprSign(f.getAnAssignedValue())
    or
    exists(PostIncrExpr inc | inc.getOperand() = f.getAnAccess() and result = fieldSign(f).inc())
    or
    exists(PreIncrExpr inc | inc.getOperand() = f.getAnAccess() and result = fieldSign(f).inc())
    or
    exists(PostDecrExpr inc | inc.getOperand() = f.getAnAccess() and result = fieldSign(f).dec())
    or
    exists(PreDecrExpr inc | inc.getOperand() = f.getAnAccess() and result = fieldSign(f).dec())
    or
    exists(AssignOperation a | a.getLValue() = f.getAnAccess() | result = exprSign(a))
    or
    f.fromSource() and not exists(f.getInitializer()) and result = TZero()
  }

  Sign specificSubExprSign(Expr e) {
    result = exprSign(e.(AssignExpr).getRValue())
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
    exists(DivExpr div |
      div = e and
      result = exprSign(div.getLeftOperand()) and
      result != TZero()
    |
      div.getRightOperand().(RealLiteral).getValue().toFloat() = 0
    )
    or
    exists(Sign s1, Sign s2 | binaryOpSigns(e, s1, s2) |
      (e instanceof AssignAddExpr or e instanceof AddExpr) and
      result = s1.add(s2)
      or
      (e instanceof AssignSubExpr or e instanceof SubExpr) and
      result = s1.add(s2.neg())
      or
      (e instanceof AssignMulExpr or e instanceof MulExpr) and
      result = s1.mul(s2)
      or
      (e instanceof AssignDivExpr or e instanceof DivExpr) and
      result = s1.div(s2)
      or
      (e instanceof AssignRemExpr or e instanceof RemExpr) and
      result = s1.rem(s2)
      or
      (e instanceof AssignAndExpr or e instanceof BitwiseAndExpr) and
      result = s1.bitand(s2)
      or
      (e instanceof AssignOrExpr or e instanceof BitwiseOrExpr) and
      result = s1.bitor(s2)
      or
      (e instanceof AssignXorExpr or e instanceof BitwiseXorExpr) and
      result = s1.bitxor(s2)
      or
      (e instanceof AssignLShiftExpr or e instanceof LShiftExpr) and
      result = s1.lshift(s2)
      or
      (e instanceof AssignRShiftExpr or e instanceof RShiftExpr) and
      result = s1.rshift(s2)
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

  private Sign binaryOpLhsSign(Expr e) {
    result = exprSign(e.(BinaryOperation).getLeftOperand()) or
    result = exprSign(e.(AssignOperation).getLValue())
  }

  private Sign binaryOpRhsSign(Expr e) {
    result = exprSign(e.(BinaryOperation).getRightOperand()) or
    result = exprSign(e.(AssignOperation).getRValue())
  }

  pragma[noinline]
  private predicate binaryOpSigns(Expr e, Sign lhs, Sign rhs) {
    lhs = binaryOpLhsSign(e) and
    rhs = binaryOpRhsSign(e)
  }

  Expr getARead(SsaVariable v) { result = v.getARead() }

  Field getField(FieldAccess fa) { result = fa.getTarget() }

  Expr getAnExpression(SsaReadPositionBlock bb) { result = bb.getBlock().getANode().getElement() }
}
