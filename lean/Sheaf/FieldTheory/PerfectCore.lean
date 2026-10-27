module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Algebra.Field.Subfield.Basic

/-!
# The perfect core of a field of positive characteristic

Source: ILO, Travaux de Gabber, Exposé IV, §3.2.1, printed p. 55
(blueprint: def-per-field-perfect-core).
-/

@[expose] public section

universe u

namespace Field

/-- The perfect core is the intersection of the images of all iterates of Frobenius.
The range of the `n`th iterate is exactly the set of `p ^ n`th powers.

Source: ILO, Travaux de Gabber, Exposé IV, §3.2.1, printed p. 55
(blueprint: def-per-field-perfect-core). -/
def perfectCore (K : Type u) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] : Subfield K :=
  ⨅ n : ℕ, (iterateFrobenius K p n).fieldRange

end Field
