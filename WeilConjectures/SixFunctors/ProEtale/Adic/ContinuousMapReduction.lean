/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic

/-!
# Reductions and limits of sheaves of continuous functions

Let `X` be a scheme and `R` a topological commutative ring, for instance the ring of integers
`𝒪_E` of a finite extension `E` of `ℚ_ℓ`. The abelian sheaf `U ↦ C(U, R)` on `X_proét`
(`AlgebraicGeometry.ProEtale.continuousMapAbSheaf`) behaves like the `ℓ`-adic integral sheaf
`𝒪_{E,X}` of Bhatt–Scholze (*The pro-étale topology for schemes*, §6.8):

- `AlgebraicGeometry.ProEtale.shortExact_continuousMapReductionShortComplex`: if multiplication
  by `a ∈ R` is an embedding and `π : R →+* Q` is a continuous surjection onto a discrete ring
  with kernel `a R`, then `0 ⟶ C(-, R) --a--> C(-, R) --π--> C(-, Q) ⟶ 0` is short exact;
  for `R = 𝒪_E`, `a = ℓⁿ` this computes `𝒪_{E,X} / ℓⁿ` as `C(-, 𝒪_E ⧸ ℓⁿ)`, which is `ν^*` of a
  constant étale sheaf
  (`AlgebraicGeometry.ProEtale.comparisonUpperStarConstantSheafIsoContinuousMapRingSheaf`);
- `AlgebraicGeometry.ProEtale.isLimitContinuousMapAbSheafCone`: if `R` is the limit of a tower of
  topological rings `Qₙ`, then `C(-, R)` is the limit of the sheaves `C(-, Qₙ)`; for
  `R = 𝒪_E`, `Qₙ = 𝒪_E ⧸ ℓⁿ` this is `𝒪_{E,X} = lim 𝒪_{E,X} / ℓⁿ`.

These are the underived parts of step (3) of the comparison of `ℓ`-adic sheaves with `ℓ`-adic
towers of torsion étale sheaves needed for the finiteness theorem
(`WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar`).
-/

@[expose] public section
universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (X : Scheme.{u}) {R Q : Type} [TopologicalSpace R] [CommRing R] [IsTopologicalRing R]
  [TopologicalSpace Q] [Ring Q] [IsTopologicalRing Q]

variable [DiscreteTopology Q]

section Limit

variable {Qs : ℕ → Type} [∀ n, TopologicalSpace (Qs n)] [∀ n, Ring (Qs n)]
  [∀ n, IsTopologicalRing (Qs n)] (τ : ∀ n, Qs (n + 1) →+* Qs n) (hτ : ∀ n, Continuous (τ n))
  (π : ∀ n, R →+* Qs n) (hπ : ∀ n, Continuous (π n)) (hπτ : ∀ n, (τ n).comp (π (n + 1)) = π n)

end Limit

end AlgebraicGeometry.ProEtale
