/**
 * Provides C#-specific definitions for use in the `SsaReadPosition`.
 */
module Private {
  import csharp
  import Ssa

  class SsaVariable = Definition;

  class SsaPhiNode = PhiNode;

  /** Gets a `BasicBlock` for the SSA variable `v`. */
  BasicBlock getBasicBlock(SsaVariable v) {
    result = v.getARead().getAControlFlowNode().getBasicBlock()
  }
}
