module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Flat.Basic

/-!
# Flatness of completed flat modules

Source: literature/stacks-project/more-algebra.tex, Lemma Tag 0AGW (lemma-flat-after-completion).
(blueprint: lem-weil-pbc-flat-module-completion-flat)
-/

@[expose] public section

universe u v

namespace Module

/-- The adic completion of a flat module over a Noetherian ring is flat over the completed ring.

Source: literature/stacks-project/more-algebra.tex, Lemma Tag 0AGW (lemma-flat-after-completion).
(blueprint: lem-weil-pbc-flat-module-completion-flat)

Proof: For every positive `n`, flat base change identifies `M / I ^ n M` with a flat
`R / I ^ n`-module. The completion of a Noetherian ring is Noetherian, and its quotient by
the `n`-th power of the extended ideal is `R / I ^ n`. Thus these quotients, viewed as
modules over the completed ring, are flat with surjective transition maps. The inverse
limit flatness lemma (Tag 0912) then gives flatness of `AdicCompletion I M` over
`AdicCompletion I R`, with the componentwise module structure.
-/
theorem flat_adicCompletion
    (R : Type u) [CommRing R] (I : Ideal R) (M : Type v) [AddCommGroup M]
    [Module R M] [IsNoetherianRing R] [Module.Flat R M] :
    Module.Flat (AdicCompletion I R) (AdicCompletion I M) := by
  sorry

end Module
