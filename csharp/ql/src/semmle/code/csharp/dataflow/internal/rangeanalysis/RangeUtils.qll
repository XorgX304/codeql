private import csharp
private import Ssa
private import SsaReadPositionCommon
private import semmle.code.csharp.controlflow.Guards as G

private class Guard = G::Guard;

private class BooleanValue = G::AbstractValues::BooleanValue;

/**
 * Holds if `guard` controls the position `controlled` with the value `testIsTrue`.
 */
predicate guardControlsSsaRead(Guard guard, SsaReadPosition controlled, boolean testIsTrue) {
  exists(BooleanValue b | b.getValue() = testIsTrue |
    guard.controlsNode(controlled.(SsaReadPositionBlock).getBlock().getANode(), _, b)
  )
}
