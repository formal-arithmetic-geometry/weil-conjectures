/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityTateInterfacePair
public import WeilConjectures.WeilSheaf.TateTwistCondensedBridge

/-! # Whole-object equations for the native Tate pair names -/

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

/-- The two named root pairs use the same Frobenius datum. -/
lemma purityTateRootPair_eq_lowerPair (d : ℕ) :
    purityTateRootPair ℓ (X ↘ Spec (.of k₀)) d = tateTwistLowerPair k₀ ℓ X d := rfl

omit [Fact (ringChar k₀ ≠ ℓ)] in
/-- The named Frobenius constraint is the geometric Frobenius constraint. -/
lemma purity_tateUnitConstraint_eq_named :
    (upperStarIsoLowerStarInv (Profinite.padicAlgClRingObj ℓ)
      (X ↘ Spec (.of k₀)).geometricGaloisFrobenius).inv.app (𝟙_ _) ≫
        tateUnitDatum ℓ (X ↘ Spec (.of k₀)).geometricGaloisFrobenius.hom =
      (frobeniusUpperStarIsoLowerStarInv k₀ ℓ X).inv.app (𝟙_ _) ≫
        tateUnitDatum ℓ (geometricFiberFrobeniusIso k₀ X).hom := rfl

end AlgebraicGeometry.WeilSheaf
