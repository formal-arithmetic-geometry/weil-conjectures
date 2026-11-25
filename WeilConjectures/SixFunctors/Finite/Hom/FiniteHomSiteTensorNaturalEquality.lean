/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Coef.CoefFiniteHomSiteDescentData
import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomSiteTensorChainEquation
import WeilConjectures.SixFunctors.Finite.Coefficient.FiniteCoefficientKFlatRepresentatives
/-! # The two finite site tensor routes in the direction of beta -/
@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
private theorem models_eq
    {C : Type*} [Category C] {S A B T : C}
    (s : S ≅ A) (t : B ≅ T) {f g : A ⟶ B} {x y : S ⟶ T}
    (hf : s.hom ≫ f ≫ t.hom = x) (hg : s.hom ≫ g ≫ t.hom = y)
    (h : x = y) : f = g := by
  apply (cancel_epi s.hom).mp
  apply (cancel_mono t.hom).mp
  simpa only [Category.assoc] using hf.trans (h.trans hg.symm)

/-- Whiskering the intrinsic tensor comparison and then the two beta components. -/
def finiteHomTensorBetaLeftOfComparisons
    {C₁ C₂ D₁ D₂ : Type*} [Category C₁] [Category C₂] [Category D₁] [Category D₂]
    (A : C₁ × C₁ ⥤ C₁) (B : D₁ × D₁ ⥤ D₁) (D : D₂ × D₂ ⥤ D₂)
    (F : C₁ ⥤ C₂) (G : D₁ ⥤ D₂) (U : C₁ ⥤ D₁) (V : C₂ ⥤ D₂)
    (α : A ⋙ U ⟶ U.prod U ⋙ B) (τ : B ⋙ G ⟶ G.prod G ⋙ D)
    (β : U ⋙ G ⟶ F ⋙ V) : A ⋙ U ⋙ G ⟶ (F ⋙ V).prod (F ⋙ V) ⋙ D :=
  Functor.whiskerRight α G ≫ Functor.whiskerLeft (U.prod U) τ ≫
    Functor.whiskerRight (NatTrans.prod β β) D

/-- Whiskering beta on the tensor before the etale tensor comparisons. -/
def finiteHomTensorBetaRightOfComparisons
    {C₁ C₂ D₁ D₂ : Type*} [Category C₁] [Category C₂] [Category D₁] [Category D₂]
    (A : C₁ × C₁ ⥤ C₁) (C : C₂ × C₂ ⥤ C₂) (D : D₂ × D₂ ⥤ D₂)
    (F : C₁ ⥤ C₂) (G : D₁ ⥤ D₂) (U : C₁ ⥤ D₁) (V : C₂ ⥤ D₂)
    (δ : A ⋙ F ⟶ F.prod F ⋙ C) (γ : C ⋙ V ⟶ V.prod V ⋙ D)
    (β : U ⋙ G ⟶ F ⋙ V) : A ⋙ U ⋙ G ⟶ (F ⋙ V).prod (F ⋙ V) ⋙ D :=
  Functor.whiskerLeft A β ≫ Functor.whiskerRight δ V ≫
    Functor.whiskerLeft (F.prod F) γ

-- Comparing the chosen intrinsic closed structures requires a larger kernel budget.
/-- The route through the intrinsic scalar tensorator, in the direction of beta. -/
noncomputable def finiteHomSiteTensorBetaLeft
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) {n m : ℕ} (h : m ≤ n) :
    (finiteHomEtaleClosed l E X n).tensor ⋙ finiteHomNu l E X n ⋙
      coefficientFiniteQuotientDerived l E X h ⟶
    (finiteHomEtaleReduction l E X h ⋙ finiteHomNu l E X m).prod
      (finiteHomEtaleReduction l E X h ⋙ finiteHomNu l E X m) ⋙
      (finiteIntrinsicClosed l E X m).tensor :=
  finiteHomTensorBetaLeftOfComparisons
    (finiteHomEtaleClosed l E X n).tensor
    (finiteIntrinsicClosed l E X n).tensor (finiteIntrinsicClosed l E X m).tensor
    (finiteHomEtaleReduction l E X h) (coefficientFiniteQuotientDerived l E X h)
    (finiteHomNu l E X n) (finiteHomNu l E X m)
    (finiteHomNuTensor l E X n).hom (coefFiniteHomProTensor l E X h).hom
    (finiteHomSiteBeta l E X h)

-- Comparing the chosen etale closed structures requires a larger kernel budget.
/-- The route through the etale scalar tensorator, in the direction of beta. -/
noncomputable def finiteHomSiteTensorBetaRight
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) {n m : ℕ} (h : m ≤ n) :
    (finiteHomEtaleClosed l E X n).tensor ⋙ finiteHomNu l E X n ⋙
      coefficientFiniteQuotientDerived l E X h ⟶
    (finiteHomEtaleReduction l E X h ⋙ finiteHomNu l E X m).prod
      (finiteHomEtaleReduction l E X h ⋙ finiteHomNu l E X m) ⋙
      (finiteIntrinsicClosed l E X m).tensor :=
  finiteHomTensorBetaRightOfComparisons
    (finiteHomEtaleClosed l E X n).tensor (finiteHomEtaleClosed l E X m).tensor
    (finiteIntrinsicClosed l E X m).tensor
    (finiteHomEtaleReduction l E X h) (coefficientFiniteQuotientDerived l E X h)
    (finiteHomNu l E X n) (finiteHomNu l E X m)
    (finiteHomEtaleTensor l E X h).hom (finiteHomNuTensor l E X m).hom
    (finiteHomSiteBeta l E X h)
end WeilConjectures
