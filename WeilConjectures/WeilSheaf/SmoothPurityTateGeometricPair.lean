/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityTatePowersDescentLaw
public import WeilConjectures.WeilSheaf.SmoothPurityPairTransport
import WeilConjectures.Tactic.ExactModProofs

/-! # The geometric Tate pair as descent from the finite base -/

@[expose] public section

universe u

open CategoryTheory Endofunctor MonoidalCategory
open scoped CategoryTheory.Obj AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The all-power Tate pullback comparison is an isomorphism for the inverse
Frobenius pushforward convention. -/
noncomputable def purity_geometricTatePairIso
    {k₀ : Type u} [Field k₀] [Finite k₀] (ℓ : ℕ) [Fact ℓ.Prime]
    [NeZero (ℓ : k₀)] [NeZero (ℓ : AlgebraicClosure k₀)]
    {X : Scheme.{u}} (a : X ⟶ Spec (.of k₀)) (d : ℕ) :
    (geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj ℓ) a).obj
        (tateTwistNat X ℓ d) ≅
      IsoAlgebra.mk (tateTwistNat a.geometricFiber ℓ d)
        (((upperStarIsoLowerStarInv (Profinite.padicAlgClRingObj ℓ)
          a.geometricGaloisFrobenius).app _).symm ≪≫
          upperStarTateTwistNatIso ℓ a.geometricGaloisFrobenius.hom
            a.geometricFiberToAlgebraicClosure d) := by
  have h := purity_upperStarTateTwistNatIso_geometricFiber ℓ a d
  let e := purity_pairIso_transport (upperStarIsoLowerStarInv (Profinite.padicAlgClRingObj ℓ)
      a.geometricGaloisFrobenius)
    ((geometricFiberProjUpperStarFrobeniusIso (Profinite.padicAlgClRingObj ℓ)
      a).app (tateTwistNat X ℓ d))
    (upperStarTateTwistNatIso ℓ a.geometricGaloisFrobenius.hom
      a.geometricFiberToAlgebraicClosure d)
    ((geometricFiberProjLowerStarFrobeniusIso (Profinite.padicAlgClRingObj ℓ)
      a).app (tateTwistNat X ℓ d))
    (((upperStarIsoLowerStarInv (Profinite.padicAlgClRingObj ℓ)
      a.geometricGaloisFrobenius).app _).symm ≪≫
      upperStarTateTwistNatIso ℓ a.geometricGaloisFrobenius.hom
        a.geometricFiberToAlgebraicClosure d)
    (purity_geometricFiberProjLowerStarFrobeniusIso_app
      (Profinite.padicAlgClRingObj ℓ) a (tateTwistNat X ℓ d))
    rfl (upperStarTateTwistNatIso ℓ a.geometricFiberProj
      a d) (by
        dsimp only [Iso.app_hom, Functor.comp_obj, Functor.comp_map] at h ⊢
        exact_mod_proofs h)
  dsimp only [geometricFiberWeilLowerStar, Functor.comp_obj] at e ⊢
  exact e

end AlgebraicGeometry.ProEtale.CondensedRing
