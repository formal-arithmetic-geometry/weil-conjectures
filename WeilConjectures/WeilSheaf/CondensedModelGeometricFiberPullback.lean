/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.GeometricFiberPullback

/-!
# Pulled-back Weil sheaves in the condensed model

Let `k₀` be a finite field, `X₀` a `k₀`-scheme, `p : X̄ ⟶ X₀` the projection of its geometric
fibre and `Fr_X` the geometric Galois Frobenius of `X̄`. An `ℓ`-adic sheaf `H` on `X₀` gives the
pro-étale Weil sheaf `p^* H` of the old model, with its canonical Weil structure
(`AlgebraicGeometry.ProEtaleWeilSheaf.geometricFiberPullback`), and the module object `E H` over
`ℚ̲̄_ℓ,X₀` gives the condensed Weil object `p^* (E H)`, with its canonical Weil structure
(`AlgebraicGeometry.ProEtale.CondensedRing.geometricFiberWeilLowerStar`). Through the comparison
`AlgebraicGeometry.ProEtaleWeilSheaf.toCondensed` of the two models they agree
(`AlgebraicGeometry.ProEtaleWeilSheaf.geometricFiberPullbackCompToCondensedIso`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtaleWeilSheaf

open ProEtale

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- **Pulled-back Weil sheaves in the two models**: the old-model Weil sheaf `p^* H` with its
canonical Weil structure becomes, through `toCondensed`, the condensed Weil object `p^* (E H)`
with its canonical Weil structure. -/
noncomputable def geometricFiberPullbackCompToCondensedIso :
    geometricFiberPullback k₀ l X ⋙ toCondensed k₀ l X ≅
      (adicSheafEquivCondensedMod l X).functor ⋙
        CondensedRing.geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l)
          (X ↘ Spec (CommRingCat.of k₀)) :=
  sorry

end AlgebraicGeometry.ProEtaleWeilSheaf
