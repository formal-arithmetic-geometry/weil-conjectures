/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityTatePowersDescentLaw
public import WeilConjectures.WeilSheaf.SmoothPurityPairTransport
public import WeilConjectures.WeilSheaf.SmoothPurityFrobeniusFactorAlias
public import WeilConjectures.WeilSheaf.TateTwistCondensedBridge
import WeilConjectures.Tactic.ExactModProofs

/-! # The Tate datum from finite-base descent is the canonical root datum -/

@[expose] public section

universe u

open CategoryTheory Endofunctor MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.WeilSheaf

open ProEtale ProEtaleWeilSheaf CondensedRing

variable (k₀ : Type u) [Field k₀] [Finite k₀] (ℓ : ℕ) [Fact ℓ.Prime]
  [Fact (ringChar k₀ ≠ ℓ)] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

local instance : NeZero (ℓ : k₀) := ⟨by
  rw [Ne, ringChar.spec, Nat.prime_dvd_prime_iff_eq (CharP.char_is_prime k₀ _) Fact.out]
  exact Fact.out⟩
attribute [local instance] neZero_natCast_algebraicClosure

/-- The pullback comparison of the Tate powers is an isomorphism of condensed Weil pairs. -/
noncomputable def purity_geometricFiberWeilLowerStarTateNatIso (d : ℕ) :
    (CondensedRing.geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj ℓ)
        (X ↘ Spec (.of k₀))).obj (tateTwistNat X ℓ d) ≅
      tateTwistLowerPair k₀ ℓ X d := by
  have h := purity_upperStarTateTwistNatIso_geometricFiber ℓ (X ↘ Spec (.of k₀)) d
  let e := purity_pairIso_transport (frobeniusUpperStarIsoLowerStarInv k₀ ℓ X)
    ((geometricFiberProjUpperStarFrobeniusIso (Profinite.padicAlgClRingObj ℓ)
      (X ↘ Spec (.of k₀))).app (tateTwistNat X ℓ d))
    (upperStarTateTwistNatIso ℓ (X ↘ Spec (.of k₀)).geometricGaloisFrobenius.hom
      (X ↘ Spec (.of k₀)).geometricFiberToAlgebraicClosure d)
    ((geometricFiberProjLowerStarFrobeniusIso (Profinite.padicAlgClRingObj ℓ)
      (X ↘ Spec (.of k₀))).app (tateTwistNat X ℓ d))
    (((frobeniusUpperStarIsoLowerStarInv k₀ ℓ X).app _).symm ≪≫
      upperStarTateTwistNatIso ℓ (X ↘ Spec (.of k₀)).geometricGaloisFrobenius.hom
        (X ↘ Spec (.of k₀)).geometricFiberToAlgebraicClosure d)
    (purity_geometricFiberProjLowerStarFrobeniusIso_app
      (Profinite.padicAlgClRingObj ℓ) (X ↘ Spec (.of k₀)) (tateTwistNat X ℓ d))
    rfl (upperStarTateTwistNatIso ℓ (X ↘ Spec (.of k₀)).geometricFiberProj
      (X ↘ Spec (.of k₀)) d) (by
        dsimp only [Iso.app_hom, Functor.comp_obj, Functor.comp_map] at h ⊢
        cast_proofs h)
  exact e

end AlgebraicGeometry.WeilSheaf
