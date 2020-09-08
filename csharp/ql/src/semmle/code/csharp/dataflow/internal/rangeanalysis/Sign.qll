/**
 * INTERNAL: Do not use.
 */
module Internal {
  newtype TSign =
    TNeg() or
    TZero() or
    TPos()

  /** Class representing expression signs (+, -, 0). */
  class Sign extends TSign {
    /** Gets the string representation of the sign. */
    string toString() {
      result = "-" and this = TNeg()
      or
      result = "0" and this = TZero()
      or
      result = "+" and this = TPos()
    }

    /** Increments the sign. */
    Sign inc() {
      this = TNeg() and result = TNeg()
      or
      this = TNeg() and result = TZero()
      or
      this = TZero() and result = TPos()
      or
      this = TPos() and result = TPos()
    }

    /** Decrements the sign. */
    Sign dec() { result.inc() = this }

    /** Negates the sign. */
    Sign neg() {
      this = TNeg() and result = TPos()
      or
      this = TZero() and result = TZero()
      or
      this = TPos() and result = TNeg()
    }

    /** Bitwise complements the sign. */
    Sign bitnot() {
      this = TNeg() and result = TPos()
      or
      this = TNeg() and result = TZero()
      or
      this = TZero() and result = TNeg()
      or
      this = TPos() and result = TNeg()
    }

    /** Adds the two signs. */
    Sign add(Sign s) {
      this = TZero() and result = s
      or
      s = TZero() and result = this
      or
      this = s and this = result
      or
      this = TPos() and s = TNeg()
      or
      this = TNeg() and s = TPos()
    }

    /** Multiplies the two signs. */
    Sign mul(Sign s) {
      result = TZero() and this = TZero()
      or
      result = TZero() and s = TZero()
      or
      result = TNeg() and this = TPos() and s = TNeg()
      or
      result = TNeg() and this = TNeg() and s = TPos()
      or
      result = TPos() and this = TPos() and s = TPos()
      or
      result = TPos() and this = TNeg() and s = TNeg()
    }

    /** Integer divides the two signs. */
    Sign div(Sign s) {
      result = TZero() and s = TNeg()
      or
      result = TZero() and s = TPos() // ex: 3 / 5 = 0
      or
      result = TNeg() and this = TPos() and s = TNeg()
      or
      result = TNeg() and this = TNeg() and s = TPos()
      or
      result = TPos() and this = TPos() and s = TPos()
      or
      result = TPos() and this = TNeg() and s = TNeg()
    }

    /** Modulo divides the two signs. */
    Sign rem(Sign s) {
      result = TZero() and s = TNeg()
      or
      result = TZero() and s = TPos()
      or
      result = this and s = TNeg()
      or
      result = this and s = TPos()
    }

    /** Bitwise `and` the two signs. */
    Sign bitand(Sign s) {
      result = TZero() and this = TZero()
      or
      result = TZero() and s = TZero()
      or
      result = TZero() and this = TPos()
      or
      result = TZero() and s = TPos()
      or
      result = TNeg() and this = TNeg() and s = TNeg()
      or
      result = TPos() and this = TNeg() and s = TPos()
      or
      result = TPos() and this = TPos() and s = TNeg()
      or
      result = TPos() and this = TPos() and s = TPos()
    }

    /** Bitwise `or` the two signs. */
    Sign bitor(Sign s) {
      result = TZero() and this = TZero() and s = TZero()
      or
      result = TNeg() and this = TNeg()
      or
      result = TNeg() and s = TNeg()
      or
      result = TPos() and this = TPos() and s = TZero()
      or
      result = TPos() and this = TZero() and s = TPos()
      or
      result = TPos() and this = TPos() and s = TPos()
    }

    /** Bitwise `xor` the two signs. */
    Sign bitxor(Sign s) {
      result = TZero() and this = s
      or
      result = this and s = TZero()
      or
      result = s and this = TZero()
      or
      result = TPos() and this = TPos() and s = TPos()
      or
      result = TNeg() and this = TNeg() and s = TPos()
      or
      result = TNeg() and this = TPos() and s = TNeg()
      or
      result = TPos() and this = TNeg() and s = TNeg()
    }

    /** Left shifts the sign by `s`. */
    Sign lshift(Sign s) {
      result = TZero() and this = TZero()
      or
      result = this and s = TZero()
      or
      this != TZero() and s != TZero()
    }

    /** Right shifts the sign by `s`. */
    Sign rshift(Sign s) {
      result = TZero() and this = TZero()
      or
      result = this and s = TZero()
      or
      result = TNeg() and this = TNeg()
      or
      result != TNeg() and this = TPos() and s != TZero()
    }

    /** Unsigned right shifts the sign by `s`. */
    Sign urshift(Sign s) {
      result = TZero() and this = TZero()
      or
      result = this and s = TZero()
      or
      result != TZero() and this = TNeg() and s != TZero()
      or
      result != TNeg() and this = TPos() and s != TZero()
    }
  }
}
