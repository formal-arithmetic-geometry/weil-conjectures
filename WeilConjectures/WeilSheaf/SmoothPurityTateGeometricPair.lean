/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityTateInterfacePair

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
  -- Compose the interface comparison with the root-pair identification.
  exact purity_geometricTateInterfacePairIso ℓ a d ≪≫
    eqToIso (purityTateRootPair_eq ℓ a d)

end AlgebraicGeometry.ProEtale.CondensedRing
