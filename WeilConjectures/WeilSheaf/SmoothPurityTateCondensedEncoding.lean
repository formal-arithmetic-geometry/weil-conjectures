/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityTateOnePair
public import WeilConjectures.WeilSheaf.SmoothPurityConstantWeilDatum
public import WeilConjectures.WeilSheaf.SmoothPurityTatePairNames
public import WeilConjectures.WeilSheaf.TateTwistCondensedBridge
import WeilConjectures.Tactic.ExactModProofs

/-! # The canonical geometric Tate datum in the condensed Weil model -/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Endofunctor
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.WeilSheaf

open ProEtale ProEtaleWeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (ℓ : ℕ) [Fact ℓ.Prime]
  [Fact (ringChar k₀ ≠ ℓ)] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

attribute [local instance] neZero_natCast_algebraicClosure

lemma purity_nonempty_tateTwistOnePair_named :
    Nonempty (tateTwistOnePair ℓ (geometricFiberFrobeniusIso k₀ X).hom
        (X ↘ Spec (.of k₀)).geometricFiberToAlgebraicClosure ≅
      IsoAlgebra.unitScalarPair _ (regularSmulIso k₀ ℓ X (cyclotomicUnit k₀ ℓ))) := by
  dsimp only [geometricFiberFrobeniusIso]
  exact_mod_proofs purity_nonempty_tateTwistOnePair_iso_unitScalar k₀ ℓ X

omit [Fact (ringChar k₀ ≠ ℓ)] in
lemma purity_adicConstantCondensedStr_named :
    (adicConstantCondensedStr k₀ ℓ X).hom =
      (frobeniusUpperStarIsoLowerStarInv k₀ ℓ X).inv.app (𝟙_ _) ≫
        tateUnitDatum ℓ (geometricFiberFrobeniusIso k₀ X).hom :=
  (purity_adicConstantCondensedStr_hom k₀ ℓ X).trans
    (purity_tateUnitConstraint_eq_named k₀ ℓ X)

/-- The root-defined geometric Tate datum agrees with the native cyclotomic twist
in every nonnegative degree. -/
theorem purity_nonempty_tateTwistLowerPair_iso_toCondensed_constantTwist (d : ℕ) :
    Nonempty (tateTwistLowerPair k₀ ℓ X d ≅
      (toCondensed k₀ ℓ X).obj
        ((ProEtaleWeilSheaf.constantTwist k₀ ℓ X (cyclotomicUnit k₀ ℓ ^ d)).obj
          (ProEtaleWeilSheaf.adicConstant k₀ ℓ X))) := by
  obtain ⟨e₁⟩ := purity_nonempty_tateTwistOnePair_named k₀ ℓ X
  exact nonempty_tateTwistLowerPair_iso_toCondensed_constantTwist k₀ ℓ X e₁
    (purity_adicConstantCondensedStr_named k₀ ℓ X) d

end AlgebraicGeometry.WeilSheaf
