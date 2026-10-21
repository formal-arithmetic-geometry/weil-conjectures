/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups NY and NC
-/
module

public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import Sheaf.Paper.CompletedPullbackReduction
public import Sheaf.Paper.SfImmersionCompletedPullbackComparison
public import Sheaf.Paper.CompletedPullbackTriangles
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
import Sheaf.CategoryTheory.StrictRoosComparison
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses

/-! # Signed integral pullback shift coordinates and descent

Source: Stacks Project, derived.tex, Tag 014E, and sites-cohomology.tex,
Tag 0941; trace-definition auxiliary whole-tower comparison, shift clause
(blueprint: def-fd-integral-pullback-shift-coordinates).

These are the existing finite-level and product shift maps, the actual Roos
endomorphism, and predicates fixing its signed cochain shift and derived descent.
No existence or comparison theorem is asserted here.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.IntegralCompletedComparison

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Pin the existing countable-product structure to the actual coefficient universe.
Source: Bhatt--Scholze 4.2.8
(blueprint: def-fd-integral-pullback-shift-coordinates). -/
instance (priority := 2500) products (T : Scheme.{u}) :
    HasCountableProducts (integralTowerModules.{u, u} l E T) :=
  integralOperationsCountableProducts.{u, u} l E T

/-- Termwise products of integral complexes in the fixed coefficient universe.
Source: Stacks 0941 (blueprint: def-fd-integral-pullback-shift-coordinates). -/
instance (priority := 2500) complexProducts (T : Scheme.{u}) :
    HasCountableProducts (CochainComplex (integralTowerModules.{u, u} l E T) ℤ) where
  out J := by
    intro hJ
    have : HasProductsOfShape J (integralTowerModules.{u, u} l E T) :=
      (products l E T).out J
    exact HomologicalComplex.instHasLimitsOfShape


variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The canonical finite-level termwise shift comparison.
Source: Stacks 014E, 099N(5)
(blueprint: def-fd-integral-pullback-shift-coordinates). -/
def levelShift (P : CochainComplex (integralTowerModules.{u, u} l E Y) ℤ) (r : ℤ) (n : ℕ) :
    (integralOperationsPullbackLevel.{u, u} l E g n).obj (P⟦r⟧) ≅
      ((integralOperationsPullbackLevel.{u, u} l E g n).obj P)⟦r⟧ :=
  letI := unrestrictedIntegralReductionFunctor_additive.{u, u} l E Y n
  letI := integralOperationsLevelPullback_additive.{u, u} l E g n
  ((unrestrictedIntegralReductionFunctor.{u, u} l E Y n ⋙
    integralOperationsLevelPullback.{u, u} l E g n ⋙
    SheafOfModules.restrictScalars.{u + 1}
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (completedIntegralCommRingProjectionUnrestricted.{u, u} l E X n)))
          |>.mapCochainComplexShiftIso r).app P

/-- The product of the canonical finite-level shift comparisons.
Source: Stacks 014E, 0941
(blueprint: def-fd-integral-pullback-shift-coordinates). -/
def productShift (P : CochainComplex (integralTowerModules.{u, u} l E Y) ℤ) (r : ℤ) :
    (∏ᶜ fun n : ℕ ↦ ((integralOperationsPullbackTowerFunctor.{u, u} l E g).obj
      (P⟦r⟧)).obj (op n)) ≅
      (∏ᶜ fun n : ℕ ↦ ((integralOperationsPullbackTowerFunctor.{u, u} l E g).obj
        P).obj (op n))⟦r⟧ :=
  Pi.mapIso.{0, u + 1, u + 2}
    (C := CochainComplex (integralTowerModules.{u, u} l E X) ℤ)
    (fun n : ℕ ↦ levelShift l E g P r n) ≪≫
    (PreservesProduct.iso.{0, u + 1, u + 1, u + 2, u + 2}
      (shiftFunctor (CochainComplex (integralTowerModules.{u, u} l E X) ℤ) r)
      (fun n : ℕ ↦ ((integralOperationsPullbackTowerFunctor.{u, u} l E g).obj P).obj (op n))).symm

/-- The endomorphism whose mapping cocone defines integral pullback on a representative.
Source: Stacks 0941 (blueprint: def-fd-integral-pullback-shift-coordinates). -/
abbrev roosEnd (P : CochainComplex (integralTowerModules.{u, u} l E Y) ℤ) :=
  towerTransitionEndomorphism
    (K := fun n : ℕ ↦ ((integralOperationsPullbackTowerFunctor.{u, u} l E g).obj P).obj (op n))
    (integralOperationsTowerStep ((integralOperationsPullbackTowerFunctor.{u, u} l E g).obj P))

/-- Shift on the actual Roos complex is (x,y) mapped to (x,(-1)^r y) in
mapping-cocone coordinates, equivalently (y,x) mapped to ((-1)^r y,x).
Source: Stacks 014E, 0941; the whole-tower comparison shift clause
(blueprint: def-fd-integral-pullback-shift-coordinates). -/
def ShiftCoordinates
    (c : (integralOperationsPullbackComplexFunctor.{u, u} l E g).CommShift ℤ) : Prop :=
  ∀ (P : CochainComplex (integralTowerModules.{u, u} l E Y) ℤ) (r : ℤ),
    (∀ j : ℤ,
      (CochainComplex.mappingCocone.inl (roosEnd l E g (P⟦r⟧))).v j j (by omega) ≫
          ((Functor.commShiftIso (integralOperationsPullbackComplexFunctor.{u, u} l E g)
            (self := c) r).hom.app P).f j =
        (productShift l E g P r).hom.f j ≫
          (CochainComplex.mappingCocone.inl (roosEnd l E g P)).v
            (j + r) (j + r) (by omega) ≫
          (CochainComplex.shiftFunctorObjXIso
            ((integralOperationsPullbackComplexFunctor.{u, u} l E g).obj P)
            r j (j + r) rfl).inv) ∧
    (∀ (i j : ℤ) (h : i + 1 = j),
      (CochainComplex.mappingCocone.inr (roosEnd l E g (P⟦r⟧))).1.v i j h ≫
          ((Functor.commShiftIso (integralOperationsPullbackComplexFunctor.{u, u} l E g)
            (self := c) r).hom.app P).f j =
        r.negOnePow • ((productShift l E g P r).hom.f i ≫
          (CochainComplex.mappingCocone.inr (roosEnd l E g P)).1.v
            (i + r) (j + r) (by omega) ≫
          (CochainComplex.shiftFunctorObjXIso
            ((integralOperationsPullbackComplexFunctor.{u, u} l E g).obj P)
            r j (j + r) rfl).inv))

/-- The integral derived shift is the descent of the specified representative shift.
Source: Stacks 014E, 0941, resolving-class localization
(blueprint: def-fd-integral-pullback-shift-coordinates). -/
def ShiftDescent
    (c : (integralOperationsPullbackComplexFunctor.{u, u} l E g).CommShift ℤ)
    (d : (integralDerivedPullback.{u, u} l E g).CommShift ℤ) : Prop :=
  ∀ (P : (integralOperationsGoodComplex.{u, u} l E Y).FullSubcategory) (r : ℤ),
    ∃ hP : integralOperationsGoodComplex.{u, u} l E Y (P.obj⟦r⟧),
      (Functor.commShiftIso (integralDerivedPullback.{u, u} l E g) (self := d) r).hom.app
          (DerivedCategory.Q.obj P.obj) ≫
        ((integralDerivedPullbackComparison.{u, u} l E g).hom.app P)⟦r⟧' =
      (integralDerivedPullback.{u, u} l E g).map
          ((DerivedCategory.Q.commShiftIso r).inv.app P.obj) ≫
        (integralDerivedPullbackComparison.{u, u} l E g).hom.app ⟨P.obj⟦r⟧, hP⟩ ≫
        DerivedCategory.Q.map
          ((Functor.commShiftIso (integralOperationsPullbackComplexFunctor.{u, u} l E g)
            (self := c) r).hom.app P.obj) ≫
        (DerivedCategory.Q.commShiftIso r).hom.app
          ((integralOperationsPullbackComplexFunctor.{u, u} l E g).obj P.obj)

end WeilConjectures.IntegralCompletedComparison
