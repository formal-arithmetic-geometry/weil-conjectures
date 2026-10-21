/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q12
-/
module

public import Sheaf.Paper.SfConstructibleHeart
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-! # Local finite freeness at a finite rational coefficient stage

Source: Bhatt--Scholze, Definition 6.8.3 and Proposition 6.8.14(2)
(blueprint: def-real-rational-lisse-heart).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- Locally a finite sum of the rational coefficient unit. The integral model is chosen
on each chart independently, and only its rationalization is identified with the pullback.
The rank can be zero and can vary with the chart. No global integral lattice is required.
Source: Bhatt--Scholze, Definition 6.8.3, Proposition 6.8.14(2), Remark 6.8.15
(blueprint: def-real-rational-lisse-heart). -/
def IsRationalLisse (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [hX : ∀ x : X, Invertible (l : X.residueField x)]
    (K : sfRationalConstructibleCategory l E X) : Prop :=
  ∃ (I : Type (u + 1)) (V : I → X.ProEt)
    (a : ∀ i : I, V i ⟶ ⊤_ X.ProEt),
    Sieve.ofArrows V a ∈ ProEt.topology X (⊤_ X.ProEt) ∧
      ∀ i : I, ∃ hV : ∀ x : (V i).left, Invertible (l : (V i).left.residueField x),
        ∃ (r : ℕ) (M : sfIntegralConstructibleCategory l E (V i).left),
          Nonempty (M.obj ≅ (DerivedCategory.singleFunctor _ 0).obj
            (SheafOfModules.free
              (R := completedIntegralCoefficientSheafUnrestricted l E (V i).left)
              (ULift.{u + 1} (Fin r)))) ∧
          Nonempty (((@rationalDerivedPullback l _ E _ _ _ _ _ (V i).hom hV hX).obj K) ≅
            (sfRationalConstructibleLocalization l E (V i).left).obj M)

/-- The lisse part of the recorded standard heart, as a full subcategory of raw
rationalization. Source: Bhatt--Scholze, 6.8.3 and 6.8.14(2)
(blueprint: def-real-rational-lisse-heart). -/
def rationalLisseHeartProperty (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)] :
    ObjectProperty (sfRationalConstructibleCategory l E X) :=
  sfRationalHeartProperty l E X ⊓ IsRationalLisse l E X

end WeilConjectures
