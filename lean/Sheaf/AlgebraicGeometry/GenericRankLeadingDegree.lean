/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.Modules.Ample

/-! # Generic rank and the top Hilbert coefficient

Source: Stacks Project, Varieties, Lemma 33.45.2, Tag 0BEN, specialized to an integral
proper scheme and one ample invertible module (blueprint: lem-sc-generic-rank-leading-degree).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- A coherent module free of rank `r` on a nonempty open of an integral proper scheme
has top Hilbert coefficient `r` times the corresponding coefficient for the ample module.
The rational polynomials represent the Euler-characteristic functions at every natural
exponent, as in `lem-sc-hilbert-polynomial`. The coefficient at the dimension is used even
when the twisted polynomial has smaller degree, in particular when `r = 0`.
Source: Stacks Project, Varieties, Lemma 33.45.2, Tag 0BEN
(blueprint: lem-sc-generic-rank-leading-degree).

Proof for stage 3:
1. Apply `lem-weil-pbc-coherent-filtration-integral-subschemes` to `E`. At the generic
   point each quotient supported on all of `Y` has rank one, while the other quotients
   vanish. Additivity of generic rank gives exactly `r` quotients supported on `Y`.
   For each of these ideals `I`, compare `I` with the structure sheaf using the exact
   sequence with quotient `O_Y/I`. That quotient has proper closed support. Tensoring
   by invertible powers of `M` preserves exactness, and `lem-pc-euler-additive` gives
   additivity of Euler characteristics. By `lem-sc-snapper-numerical-polynomial`, every
   proper-support contribution has polynomial degree strictly below `g`. Thus the
   difference from `r` times the Hilbert polynomial has zero coefficient at `g`.
2. Use `lem-sc-hilbert-polynomial` for the untwisted Hilbert function and add the
   lower-degree difference to obtain a polynomial for the twisted function. Comparing
   coefficients proves the claim. Multiplication by the nonzero rational number `g!`
   gives the equivalent factorial-scaled formulation. In dimension zero the
   proper-support contributions vanish, so the difference polynomial is zero. -/
theorem exists_polynomials_coeff_eq_genericRank
    (K : Type u) [Field K] (Y : Scheme.{u}) [IsIntegral Y]
    [Y.Over (Spec (.of K))] [IsProper (Y ↘ Spec (.of K))]
    (g : ℕ) (hdim : topologicalKrullDim Y = g)
    (M : Y.Modules) (hM : IsAmple (Y ↘ Spec (.of K)) M)
    (E : Y.Modules) (hE : RingedSpace.IsCoherent Y.toRingedSpace E)
    (U : Y.Opens) (hU : (U : Set Y).Nonempty) (r : ℕ)
    (e : E.over U ≅
      SheafOfModules.free (R := (moduleRings Y.toRingedSpace).over U) (ULift.{u} (Fin r))) :
    ∃ P Q : Polynomial ℚ,
      (∀ m : ℕ, P.eval (m : ℚ) = ((E ⊗ M.tensorPow m).eulerChar K : ℚ)) ∧
      (∀ m : ℕ, Q.eval (m : ℚ) = ((M.tensorPow m).eulerChar K : ℚ)) ∧
      P.coeff g = (r : ℚ) * Q.coeff g := by
  sorry

end AlgebraicGeometry.Scheme.Modules
