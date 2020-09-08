/**
 * Provides Java-specific definitions for use in the `SsaReadPosition`.
 */
module Private {
  import java
  import semmle.code.java.dataflow.SSA

  /** Gets a `BasicBlock` for the SSA variable `v`. */
  BasicBlock getBasicBlock(SsaVariable v) { result = v.getAUse().getBasicBlock() }
}
