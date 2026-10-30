/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.PullbackStrCompat
public import WeilConjectures.WeilSheaf.GeometricFiberPullback

/-!
# The Weil structure of a pulled-back sheaf

The canonical Weil structure of the pro-étale Weil sheaf `p^* H` pulled back from the model
(`AlgebraicGeometry.ProEtaleWeilSheaf.geometricFiberPullback`) is the canonical Weil structure
`AlgebraicGeometry.ProEtale.pullbackStrIso` attached to `Fr ≫ p = p`
(`AlgebraicGeometry.ProEtaleWeilSheaf.geometricFiberPullback_eq_functorOfNatIso`).
-/

@[expose] public section

universe u

open CategoryTheory Endofunctor

namespace AlgebraicGeometry.ProEtaleWeilSheaf

open ProEtale

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- The canonical Weil structure of the pullbacks along `p` is `pullbackStrIso`. -/
lemma geometricFiberPullbackFrobeniusIso_eq_pullbackStrIso :
    geometricFiberPullbackFrobeniusIso k₀ l X =
      pullbackStrIso (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius _
        (Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj _) :=
  rfl

/-- The pulled-back pro-étale Weil sheaf `p^* H`, as an algebra. -/
lemma geometricFiberPullback_obj_eq_mk (H : AdicSheaf l X) :
    (geometricFiberPullback k₀ l X).obj H =
      IsoAlgebra.mk (((X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj)^*ᵃ[l].obj H)
        ((pullbackStrIso (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius _
          (Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj _)).app H) := by
  rw [← geometricFiberPullbackFrobeniusIso_eq_pullbackStrIso]
  rfl

/-- The pullback functor `p^*` to pro-étale Weil sheaves, with the Weil structure
`pullbackStrIso`. -/
lemma geometricFiberPullback_eq_functorOfNatIso :
    geometricFiberPullback k₀ l X =
      IsoAlgebra.functorOfNatIso ((X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj)^*ᵃ[l]
        (pullbackStrIso (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius _
          (Scheme.Hom.geometricGaloisFrobenius_hom_comp_geometricFiberProj _)) := by
  rw [geometricFiberPullback, geometricFiberPullbackFrobeniusIso_eq_pullbackStrIso]

end AlgebraicGeometry.ProEtaleWeilSheaf
