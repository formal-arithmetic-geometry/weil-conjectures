/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityTateOnePair
public import WeilConjectures.WeilSheaf.SmoothPurityConstantWeilDatum
public import WeilConjectures.WeilSheaf.TateTwistCondensedBridge

/-! # The canonical geometric Tate datum in the condensed Weil model -/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.WeilSheaf

open ProEtale ProEtaleWeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (ℓ : ℕ) [Fact ℓ.Prime]
  [Fact (ringChar k₀ ≠ ℓ)] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- The root-defined geometric Tate datum agrees with the native cyclotomic twist
in every nonnegative degree. -/
theorem purity_nonempty_tateTwistLowerPair_iso_toCondensed_constantTwist (d : ℕ) :
    Nonempty (tateTwistLowerPair k₀ ℓ X d ≅
      (toCondensed k₀ ℓ X).obj
        ((ProEtaleWeilSheaf.constantTwist k₀ ℓ X (cyclotomicUnit k₀ ℓ ^ d)).obj
          (ProEtaleWeilSheaf.adicConstant k₀ ℓ X))) := by
  obtain ⟨e₁⟩ := purity_nonempty_tateTwistOnePair_iso_unitScalar k₀ ℓ X
  apply nonempty_tateTwistLowerPair_iso_toCondensed_constantTwist k₀ ℓ X e₁ _ d
  exact purity_adicConstantCondensedStr_hom k₀ ℓ X

end AlgebraicGeometry.WeilSheaf
