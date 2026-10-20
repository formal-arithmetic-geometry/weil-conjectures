/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Sheaf.Paper.PurityConventions
public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.AlgebraicGeometry.SupportedExteriorProduct
public import Sheaf.Paper.PurityFrameClass
import Sheaf.Paper.PurityFrameIndependence
public import Sheaf.Paper.SupportedCupFunctoriality
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonDerived
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedUpperShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion

/-!
# Normalized regular-immersion fundamental class

Source: blueprint main-20261015, sec-smooth-purity/sk-thm-regular,
def-pur-regular-immersion-class-data (blueprint: def-pur-regular-immersion-class-data).

All coefficients are the actual finite quotient of the fixed purity setting. Supported
classes use the published Hom model, and their restriction uses the section-normalized
closed coefficient exchange. The frame product is the existing ordered Kummer-boundary fold.

## Main declarations

* `regularFundamentalClass`.
* `regularFundamentalClassMap`.
* `regularSupportedEquiv`.
* `regularTensorTools`, `regularCup`, and `RegularCancellationEquation`: canonical adapters.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u u' c v w

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale

namespace WeilConjectures.PurityFiniteSetting

/-- A shared reference to the published derived monoidal structure, before coefficient
specialization. Source: the K-flat tensor used in sk-thm-regular(c)
(blueprint: def-pur-regular-immersion-class-data). -/
@[no_expose, implicit_reducible]
def regularTensorMonoidal (C : Type u') [Category.{u} C] [Abelian C]
    [hD : HasDerivedCategory.{u} C] [IsGrothendieckAbelian.{u} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C] : MonoidalCategory (_root_.DerivedCategory C) :=
  inferInstance

/-- Characterization of the hidden canonical regularTensorMonoidal construction.
Source: the tensor localization and shift comparisons used in supported cup products
(blueprint: def-pur-regular-immersion-class-data).
Proof: unfold regularTensorMonoidal. Its definition is exactly the displayed published instance
or composite, so reflexivity proves this equation; no existence choice is used. -/
theorem regularTensorMonoidal_eq (C : Type u') [Category.{u} C] [Abelian C]
    [hD : HasDerivedCategory.{u} C] [IsGrothendieckAbelian.{u} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C] :
    regularTensorMonoidal C = (inferInstance : MonoidalCategory (_root_.DerivedCategory C)) := by
  sorry


/-- The existing localization tensorator and shift comparisons with one shared tensor
structure. No new monoidal structure is chosen. Source: inverse twisting in sk-thm-regular(c)
(blueprint: def-pur-regular-immersion-class-data). -/
structure RegularTensorTools (C : Type u') [Category.{u} C] [Abelian C]
    [hD : HasDerivedCategory.{u} C] [HasColimitsOfSize.{0, 0} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [hDM : MonoidalCategory (_root_.DerivedCategory C)] where
  /-- The published degree-zero localization tensorator.
  Source: tensor localization (blueprint: def-pur-regular-immersion-class-data). -/
  qLax : (_root_.DerivedCategory.Q (C := C)).LaxMonoidal
  /-- The published right-factor shift comparison.
  Source: shifted tensor (blueprint: def-pur-regular-immersion-class-data). -/
  rightShift : ∀ K : _root_.DerivedCategory C, ((curriedTensor _).obj K).CommShift ℤ
  /-- The published left-factor shift comparison.
  Source: shifted tensor (blueprint: def-pur-regular-immersion-class-data). -/
  leftShift : ∀ K : _root_.DerivedCategory C, ((curriedTensor _).flip.obj K).CommShift ℤ

/-- Package the actual published comparisons at an abstract category, so that their
shared monoidal argument is retained during coefficient specialization.
Source: inverse twisting in sk-thm-regular(c)
(blueprint: def-pur-regular-immersion-class-data). -/
def regularTensorToolsCanonical (C : Type u') [Category.{u} C] [Abelian C]
    [hD : HasDerivedCategory.{u} C] [IsGrothendieckAbelian.{u} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C] :
    RegularTensorTools (hDM := (inferInstance :
      MonoidalCategory (_root_.DerivedCategory C))) C where
  qLax := inferInstance
  rightShift := fun _ ↦ inferInstance
  leftShift := fun _ ↦ inferInstance


/-- The named body of the canonical tensor comparison package.
Source: the canonical localization tensorator and shift comparisons
(blueprint: def-pur-regular-immersion-class-data). -/
@[no_expose]
def regularTensorTools (C : Type u') [Category.{u} C] [Abelian C]
    [hD : HasDerivedCategory.{u} C] [IsGrothendieckAbelian.{u} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C] :
    RegularTensorTools (hDM := regularTensorMonoidal C) C :=
  cast (congrArg (fun M : MonoidalCategory (_root_.DerivedCategory C) ↦
    RegularTensorTools (hDM := M) C) (regularTensorMonoidal_eq C).symm)
      (regularTensorToolsCanonical C)

/-- Shifted evaluation using the published tensor and degree-zero comparisons,
formed before specializing the sheaf category or coefficient ring.
Source: cancelling opposite Tate shifts in sk-thm-regular(c)
(blueprint: def-pur-regular-immersion-class-data). -/
@[no_expose]
def regularEvaluationGeneral {C : Type u'} [Category.{u} C] [Abelian C]
    [hD : HasDerivedCategory.{u} C] [HasColimitsOfSize.{0, 0} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [hDM : MonoidalCategory (_root_.DerivedCategory C)]
    [hLax : (_root_.DerivedCategory.Q (C := C)).LaxMonoidal]
    [hRight : ∀ K : _root_.DerivedCategory C, ((curriedTensor _).obj K).CommShift ℤ]
    [hLeft : ∀ K : _root_.DerivedCategory C, ((curriedTensor _).flip.obj K).CommShift ℤ]
    (F G U : C) (a b : ℤ) (hab : a + b = 0) (e : F ⊗ G ⟶ U) :
    ((_root_.DerivedCategory.singleFunctor C 0).obj F)⟦a⟧ ⊗
      ((_root_.DerivedCategory.singleFunctor C 0).obj G)⟦b⟧ ⟶
        (_root_.DerivedCategory.singleFunctor C 0).obj U :=
  (ProEtale.cupTensorShiftIso ((_root_.DerivedCategory.singleFunctor C 0).obj F)
    ((_root_.DerivedCategory.singleFunctor C 0).obj G) a b).hom ≫
    (ProEtale.cupSingleTensorMap F G ≫ (_root_.DerivedCategory.singleFunctor C 0).map e)⟦a + b⟧' ≫
    eqToHom (congrArg (fun r : ℤ ↦
      ((_root_.DerivedCategory.singleFunctor C 0).obj U)⟦r⟧) hab) ≫
    (shiftFunctorZero (_root_.DerivedCategory C) ℤ).hom.app _


/-- Shift the second factor, then apply the published degree-zero tensor comparison
and the specified ordinary action. Source: inverse twisting of cl_i
(blueprint: def-pur-regular-immersion-class-data). -/
@[no_expose]
def regularShiftedActionGeneral {C : Type u'} [Category.{u} C] [Abelian C]
    [hD : HasDerivedCategory.{u} C] [HasColimitsOfSize.{0, 0} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [hDM : MonoidalCategory (_root_.DerivedCategory C)]
    [hLax : (_root_.DerivedCategory.Q (C := C)).LaxMonoidal]
    [hRight : ∀ K : _root_.DerivedCategory C, ((curriedTensor _).obj K).CommShift ℤ]
    (F G : C) (b : ℤ) (e : F ⊗ G ⟶ G) :
    (_root_.DerivedCategory.singleFunctor C 0).obj F ⊗
      ((_root_.DerivedCategory.singleFunctor C 0).obj G)⟦b⟧ ⟶
        ((_root_.DerivedCategory.singleFunctor C 0).obj G)⟦b⟧ :=
  (((curriedTensor (_root_.DerivedCategory C)).obj
    ((_root_.DerivedCategory.singleFunctor C 0).obj F)).commShiftIso b).hom.app
      ((_root_.DerivedCategory.singleFunctor C 0).obj G) ≫
    (ProEtale.cupSingleTensorMap F G ≫ (_root_.DerivedCategory.singleFunctor C 0).map e)⟦b⟧'



/-- Characterization of the hidden canonical regularTensorTools construction.
Source: the tensor localization and shift comparisons used in supported cup products
(blueprint: def-pur-regular-immersion-class-data).
Proof: unfold regularTensorTools. Its definition is exactly the displayed published instance
or composite, so reflexivity proves this equation; no existence choice is used. -/
theorem regularTensorTools_eq (C : Type u') [Category.{u} C] [Abelian C]
    [hD : HasDerivedCategory.{u} C] [IsGrothendieckAbelian.{u} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C] :
    regularTensorTools C =
      cast (congrArg (fun M : MonoidalCategory (_root_.DerivedCategory C) ↦
        RegularTensorTools (hDM := M) C) (regularTensorMonoidal_eq C).symm)
          (regularTensorToolsCanonical C) := by
  sorry

/-- Characterization of the hidden canonical regularEvaluationGeneral construction.
Source: the tensor localization and shift comparisons used in supported cup products
(blueprint: def-pur-regular-immersion-class-data).
Proof: unfold regularEvaluationGeneral. Its definition is exactly the displayed published instance
or composite, so reflexivity proves this equation; no existence choice is used. -/
theorem regularEvaluationGeneral_eq {C : Type u'} [Category.{u} C] [Abelian C]
    [hD : HasDerivedCategory.{u} C] [HasColimitsOfSize.{0, 0} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [hDM : MonoidalCategory (_root_.DerivedCategory C)]
    [hLax : (_root_.DerivedCategory.Q (C := C)).LaxMonoidal]
    [hRight : ∀ K : _root_.DerivedCategory C, ((curriedTensor _).obj K).CommShift ℤ]
    [hLeft : ∀ K : _root_.DerivedCategory C, ((curriedTensor _).flip.obj K).CommShift ℤ]
    (F G U : C) (a b : ℤ) (hab : a + b = 0) (e : F ⊗ G ⟶ U) :
    regularEvaluationGeneral F G U a b hab e =
  (ProEtale.cupTensorShiftIso ((_root_.DerivedCategory.singleFunctor C 0).obj F)
    ((_root_.DerivedCategory.singleFunctor C 0).obj G) a b).hom ≫
    (ProEtale.cupSingleTensorMap F G ≫ (_root_.DerivedCategory.singleFunctor C 0).map e)⟦a + b⟧' ≫
    eqToHom (congrArg (fun r : ℤ ↦
      ((_root_.DerivedCategory.singleFunctor C 0).obj U)⟦r⟧) hab) ≫
    (shiftFunctorZero (_root_.DerivedCategory C) ℤ).hom.app _ := by
  sorry

/-- Characterization of the hidden canonical regularShiftedActionGeneral construction.
Source: the tensor localization and shift comparisons used in supported cup products
(blueprint: def-pur-regular-immersion-class-data).
Proof: unfold regularShiftedActionGeneral. Its definition is the displayed published
composite, so reflexivity proves this equation; no existence choice is used. -/
theorem regularShiftedActionGeneral_eq {C : Type u'} [Category.{u} C] [Abelian C]
    [hD : HasDerivedCategory.{u} C] [HasColimitsOfSize.{0, 0} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [hDM : MonoidalCategory (_root_.DerivedCategory C)]
    [hLax : (_root_.DerivedCategory.Q (C := C)).LaxMonoidal]
    [hRight : ∀ K : _root_.DerivedCategory C, ((curriedTensor _).obj K).CommShift ℤ]
    (F G : C) (b : ℤ) (e : F ⊗ G ⟶ G) :
    regularShiftedActionGeneral F G b e =
  (((curriedTensor (_root_.DerivedCategory C)).obj
    ((_root_.DerivedCategory.singleFunctor C 0).obj F)).commShiftIso b).hom.app
      ((_root_.DerivedCategory.singleFunctor C 0).obj G) ≫
    (ProEtale.cupSingleTensorMap F G ≫ (_root_.DerivedCategory.singleFunctor C 0).map e)⟦b⟧' := by
  sorry

/-- Carrier identification for arbitrary degrees and signed twists in the two
published supported-Hom APIs. Source: supported exterior products in sk-thm-regular(d)
(blueprint: def-pur-regular-immersion-class-data).
Proof: unfold the true site branch and the shared single-functor references. The
source, target, shift and canonical localization agree literally. -/
theorem regularFunctorialHom_eq (P : PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) (a r : ℤ) :
    P.FunctorialCupH true i a r =
      ProEtale.cupSupportedHom P i
        ((ProEtale.cupSingle P X).obj (P.functorialCupTwist true X r)) a := by
  sorry

/-- The published supported cup, transported between its identical Hom carriers.
Source: exterior-product compatibility in sk-thm-regular(d)
(blueprint: def-pur-regular-immersion-class-data). -/
@[no_expose]
def regularCup (P : PurityFiniteSetting.{u}) {C D X : Scheme.{u}}
    (aX : X ⟶ Spec (.of P.field.k)) (i : C ⟶ X) (j : D ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] (a b r t : ℤ)
    (α : ProEtale.cupSupportedHom P i
      ((ProEtale.cupSingle P X).obj (P.functorialCupTwist true X r)) a)
    (β : ProEtale.cupSupportedHom P j
      ((ProEtale.cupSingle P X).obj (P.functorialCupTwist true X t)) b) :
    ProEtale.cupSupportedHom P (ProEtale.cupIntersection i j)
      ((ProEtale.cupSingle P X).obj (P.functorialCupTwist true X (r + t))) (a + b) :=
  cast (P.regularFunctorialHom_eq (ProEtale.cupIntersection i j) (a + b) (r + t))
    (P.functorialCup true aX i j a b r t
      (cast (P.regularFunctorialHom_eq i a r).symm α)
      (cast (P.regularFunctorialHom_eq j b t).symm β))

/-- The supported cup adapter is exactly equality transport of the published cup.
Source: the tensor-morphism prescription (blueprint: def-pur-regular-immersion-class-data).
Proof: unfold regularCup; the displayed composite is its definition. -/
theorem regularCup_eq (P : PurityFiniteSetting.{u}) {C D X : Scheme.{u}}
    (aX : X ⟶ Spec (.of P.field.k)) (i : C ⟶ X) (j : D ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] (a b r t : ℤ)
    (α : ProEtale.cupSupportedHom P i
      ((ProEtale.cupSingle P X).obj (P.functorialCupTwist true X r)) a)
    (β : ProEtale.cupSupportedHom P j
      ((ProEtale.cupSingle P X).obj (P.functorialCupTwist true X t)) b) :
    P.regularCup aX i j a b r t α β =
  cast (P.regularFunctorialHom_eq (ProEtale.cupIntersection i j) (a + b) (r + t))
    (P.functorialCup true aX i j a b r t
      (cast (P.regularFunctorialHom_eq i a r).symm α)
      (cast (P.regularFunctorialHom_eq j b t).symm β)) := by
  sorry


open AlgebraicGeometry.ProEtale

/-- The Hom type of the published projection component, shared before specialization.
Source: inverse twisting in sk-thm-regular(c)
(blueprint: def-pur-regular-immersion-class-data). -/
def regularProjectionHom (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [HasCompactification i]
    (M : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Z) A))
    (L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) : Type _ :=
  ((derivedTensorRightDerivedLowerShriek A
    (HasCompactification.compactification i)).obj M).obj L ⟶
      ((rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar A
        (HasCompactification.compactification i)).obj M).obj L

/-- The published projection component in its shared Hom type.
Keeping the coefficient category abstract shares the generic derived tensor instance.
Source: inverse twisting in sk-thm-regular(c)
(blueprint: def-pur-regular-immersion-class-data). -/
def regularProjectionCanonical (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [UpperStarPreservesFlat A] {Z X : Scheme.{u}} (i : Z ⟶ X) [HasCompactification i]
    (M : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Z) A))
    (L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    regularProjectionHom A i M L :=
  ((projectionMap A i).app M).app L

/-- The native bifunctor-component Hom is the ordinary projection-formula Hom.
Source: inverse twisting in sk-thm-regular(c)
(blueprint: def-pur-regular-immersion-class-data).
Proof: unfold the two published bifunctors at M and L and the chosen compactification.
Their source is Ri_! M tensor L and their target is Ri_! (M tensor Li* L), with
exactly the same canonical derived tensor and inverse image. -/
theorem regularProjectionHom_eq (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [HasCompactification i]
    (M : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Z) A))
    (L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    regularProjectionHom A i M L =
      ((rightDerivedLowerShriek A i).obj M ⊗ L ⟶
        (rightDerivedLowerShriek A i).obj (M ⊗ (upperStar A i).leftDerivedFunctor.obj L)) := by
  sorry

/-- The actual published projection component in ordinary tensor endpoint notation.
Only its identical native Hom carrier is transported.
Source: inverse twisting in sk-thm-regular(c)
(blueprint: def-pur-regular-immersion-class-data). -/
def regularProjectionTensor (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [UpperStarPreservesFlat A] {Z X : Scheme.{u}} (i : Z ⟶ X) [HasCompactification i]
    (M : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Z) A))
    (L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    (rightDerivedLowerShriek A i).obj M ⊗ L ⟶
      (rightDerivedLowerShriek A i).obj (M ⊗ (upperStar A i).leftDerivedFunctor.obj L) :=
  cast (regularProjectionHom_eq A i M L) (regularProjectionCanonical A i M L)

/-- The native cancellation-isomorphism type for the published derived tensor.
Source: inverse twisting in sk-thm-regular(c)
(blueprint: def-pur-regular-immersion-class-data). -/
def regularCancellationIso (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (Z : Scheme.{u})
    (M N V : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Z) A)) : Type _ :=
  M ⊗ N ≅ V

/-- Native signed-pullback comparison carrier for the co-projection equation.
Source: inverse twisting in sk-thm-regular(c)
(blueprint: def-pur-regular-immersion-class-data). -/
def regularCancellationPullbackType (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    {Z X : Scheme.{u}} (i : Z ⟶ X)
    (T : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (N : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Z) A)) : Type _ :=
  (upperStar A i).leftDerivedFunctor.obj T ≅ N

/-- Native counit carrier for the co-projection equation.
Source: inverse twisting in sk-thm-regular(c)
(blueprint: def-pur-regular-immersion-class-data). -/
def regularCancellationCounitType (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [HasCompactification i]
    (M : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Z) A))
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) : Type _ :=
  (rightDerivedLowerShriek A i).obj M ⟶ K

/-- Native tensor-evaluation carrier for the co-projection equation.
Source: inverse twisting in sk-thm-regular(c)
(blueprint: def-pur-regular-immersion-class-data). -/
def regularCancellationEvaluationType (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u})
    (K T U : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) : Type _ :=
  K ⊗ T ⟶ U

/-- The co-projection mate equation, expressed before specializing coefficients.
It uses exactly the published projection component, pullback comparison, two counits,
and evaluation. Source: cancellation in sk-thm-regular(c)
(blueprint: def-pur-regular-immersion-class-data). -/
def RegularCancellationEquation (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [UpperStarPreservesFlat A] {Z X : Scheme.{u}} (i : Z ⟶ X) [HasCompactification i]
    (M N V : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Z) A))
    (K T U : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (p : regularCancellationPullbackType A i T N)
    (e : regularCancellationIso A Z M N V)
    (ε : regularCancellationCounitType A i M K)
    (η : regularCancellationCounitType A i V U)
    (ev : regularCancellationEvaluationType A X K T U) : Prop :=
  regularProjectionTensor A i M T ≫
      (rightDerivedLowerShriek A i).map (M ◁ p.hom) ≫
      (rightDerivedLowerShriek A i).map e.hom ≫ η = (ε ▷ T) ≫ ev

/-- The published exact right-derived/single comparison, assembled before specializing
its coefficient categories. Source: the supported Hom model and exact closed pushforward
(blueprint: def-pur-regular-immersion-class-data). -/
def regularRightDerivedSingle {B D : Type c} [Category.{v} B] [Category.{v} D]
    [Abelian B] [Abelian D] [hB : HasDerivedCategory.{w} B]
    [hD : HasDerivedCategory.{w} D] [Abelian.HasKInjectiveResolutions B]
    (F : B ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (M : B) :
    F.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor B 0).obj M) ≅
      (DerivedCategory.singleFunctor D 0).obj (F.obj M) :=
  F.rightDerivedFunctorIsoMapDerivedCategory.app _ ≪≫
    (F.mapDerivedCategorySingleFunctor 0).app M

/-- The two native supported-Hom carriers for a nonnegative finite twist coincide.
Source: the ordinary finite Tate multiplication in the supported cup
(blueprint: def-pur-regular-immersion-class-data).
Proof: unfold functorialCupTwist in the true branch and frameTwist. Both are inverse
image of the same finite signed Tate sheaf. Their single functors and supports agree. -/
theorem regularNaturalCupHom_eq (P : PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) (a : ℤ) (c : ℕ) :
    ProEtale.cupSupportedHom P i
        ((ProEtale.cupSingle P X).obj (P.functorialCupTwist true X c)) a =
      ProEtale.cupSupportedHom P i
        ((ProEtale.cupSingle P X).obj (P.frameTwist X c)) a := by
  sorry

/-- The two native supported-Hom carriers for addition of nonnegative twists coincide.
Source: finite Tate multiplication, used by the supported cup
(blueprint: def-pur-regular-immersion-class-data).
Proof: unfold the two finite twists and use Int.natCast_add; all other objects and
canonical localization data are identical. This is transport of carriers only. -/
theorem regularNaturalCupSumHom_eq (P : PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) (a : ℤ) (c d : ℕ) :
    ProEtale.cupSupportedHom P i
        ((ProEtale.cupSingle P X).obj (P.functorialCupTwist true X ((c : ℤ) + d))) a =
      ProEtale.cupSupportedHom P i
        ((ProEtale.cupSingle P X).obj (P.frameTwist X (c + d))) a := by
  sorry

/-- The actual published cup with its native nonnegative-twist carriers. It transports
only identical carriers, retaining the same coefficient multiplication and shift signs.
Source: the supported cup, finite Tate multiplication
(blueprint: def-pur-regular-immersion-class-data). -/
def regularNaturalCup (P : PurityFiniteSetting.{u}) {C D X : Scheme.{u}}
    (aX : X ⟶ Spec (.of P.field.k)) (i : C ⟶ X) (j : D ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] (a b : ℤ) (c d : ℕ)
    (α : ProEtale.cupSupportedHom P i
      ((ProEtale.cupSingle P X).obj (P.frameTwist X c)) a)
    (β : ProEtale.cupSupportedHom P j
      ((ProEtale.cupSingle P X).obj (P.frameTwist X d)) b) :
    ProEtale.cupSupportedHom P (ProEtale.cupIntersection i j)
      ((ProEtale.cupSingle P X).obj (P.frameTwist X (c + d))) (a + b) :=
  cast (P.regularNaturalCupSumHom_eq (ProEtale.cupIntersection i j) (a + b) c d)
    (P.regularCup aX i j a b c d
      (cast (P.regularNaturalCupHom_eq i a c).symm α)
      (cast (P.regularNaturalCupHom_eq j b d).symm β))


/-- The closed-support coefficient comparison before specializing coefficients.
Source: sk-thm-regular(a), proper pushforward and its exact single comparison
(blueprint: def-pur-regular-immersion-class-data). -/
@[no_expose]
def regularClosedCoefficientGeneral (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] [HasCompactification i]
    [PreservesFiniteColimits (lowerStar A i)] (M : Sheaf (Scheme.ProEt.topology Z) A) :=
  (rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar A i).app
      ((_root_.DerivedCategory.singleFunctor _ 0).obj M) ≪≫
    regularRightDerivedSingle (lowerStar A i) M

/-- Assemble the actual exceptional Hom equivalence with a specified coefficient
source comparison before specializing the coefficient category.
Source: the exceptional adjunction in sk-thm-regular(a)
(blueprint: def-pur-regular-immersion-class-data). -/
@[no_expose]
def regularSupportedEquivGeneral (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [HasCompactification i]
    [Etale.HasBoundedBelowUpperShriek A i]
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Z) A))
    (L H : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (hK : ProEtale.DerivedCategory.plusEtaleOrigin A Z K)
    (hL : _root_.DerivedCategory.TStructure.t.plus L)
    (e : (rightDerivedLowerShriek A i).obj K ≅ H) :=
  (e.symm.homFromEquiv (Z := L)).trans (rightDerivedUpperShriekHomEquiv i hK hL)

/-- The native derived pullback comparison type, before coefficient specialization.
Source: signed Tate pullback in sk-thm-regular(c)
(blueprint: def-pur-regular-immersion-class-data). -/
def regularExactPullbackShiftHom (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    {Z X : Scheme.{u}} (i : Z ⟶ X)
    (M : Sheaf (Scheme.ProEt.topology X) A)
    (N : Sheaf (Scheme.ProEt.topology Z) A) (r : ℤ) : Type _ :=
  (upperStar A i).leftDerivedFunctor.obj
      (((_root_.DerivedCategory.singleFunctor _ 0).obj M)⟦r⟧) ≅
    ((_root_.DerivedCategory.singleFunctor _ 0).obj N)⟦r⟧

/-- Exact inverse image of a shifted sheaf using the existing derived/single and
shift comparisons, with arbitrary ordinary sheaf categories.
Source: inverse Tate pullback in sk-thm-regular(c)
(blueprint: def-pur-regular-immersion-class-data). -/
@[no_expose]
def regularExactPullbackShift (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    {Z X : Scheme.{u}} (i : Z ⟶ X)
    (M : Sheaf (Scheme.ProEt.topology X) A)
    (N : Sheaf (Scheme.ProEt.topology Z) A) (e : (upperStar A i).obj M ≅ N) (r : ℤ) :
    regularExactPullbackShiftHom A i M N r :=
  (leftDerivedUpperStarIsoMapDerivedCategory A i).app
      (((_root_.DerivedCategory.singleFunctor _ 0).obj M)⟦r⟧) ≪≫
    ((upperStar A i).mapDerivedCategory.commShiftIso r).app
      ((_root_.DerivedCategory.singleFunctor _ 0).obj M) ≪≫
    (shiftFunctor (_root_.DerivedCategory _) r).mapIso
      (((upperStar A i).mapDerivedCategorySingleFunctor 0).app M ≪≫
        (_root_.DerivedCategory.singleFunctor _ 0).mapIso e)

/-- The native shifted-evaluation Hom, named before coefficient specialization.
Source: the tensor evaluation in sk-thm-regular(c)
(blueprint: def-pur-regular-immersion-class-data). -/
def regularEvaluationHom {C : Type u'} [Category.{u} C] [Abelian C]
    [HasDerivedCategory.{u} C] [IsGrothendieckAbelian.{u} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C] (F G U : C) (a b : ℤ) : Type _ :=
  ((_root_.DerivedCategory.singleFunctor C 0).obj F)⟦a⟧ ⊗
    ((_root_.DerivedCategory.singleFunctor C 0).obj G)⟦b⟧ ⟶
      (_root_.DerivedCategory.singleFunctor C 0).obj U

/-- The canonical shifted evaluation in its shared native Hom carrier.
Source: sk-thm-regular(c) (blueprint: def-pur-regular-immersion-class-data). -/
@[no_expose]
def regularEvaluationCanonical {C : Type u'} [Category.{u} C] [Abelian C]
    [HasDerivedCategory.{u} C] [IsGrothendieckAbelian.{u} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C]
    (F G U : C) (a b : ℤ) (hab : a + b = 0) (e : F ⊗ G ⟶ U) :
    regularEvaluationHom F G U a b :=
  regularEvaluationGeneral F G U a b hab e

/-- The native shifted-action Hom, named before coefficient specialization.
Source: the tensor unit action in sk-thm-regular(c)
(blueprint: def-pur-regular-immersion-class-data). -/
def regularActionHom {C : Type u'} [Category.{u} C] [Abelian C]
    [HasDerivedCategory.{u} C] [IsGrothendieckAbelian.{u} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C] (F G : C) (b : ℤ) : Type _ :=
  (_root_.DerivedCategory.singleFunctor C 0).obj F ⊗
    ((_root_.DerivedCategory.singleFunctor C 0).obj G)⟦b⟧ ⟶
      ((_root_.DerivedCategory.singleFunctor C 0).obj G)⟦b⟧

/-- The canonical shifted unit action in its shared native Hom carrier.
Source: sk-thm-regular(c) (blueprint: def-pur-regular-immersion-class-data). -/
@[no_expose]
def regularActionCanonical {C : Type u'} [Category.{u} C] [Abelian C]
    [HasDerivedCategory.{u} C] [IsGrothendieckAbelian.{u} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C]
    (F G : C) (b : ℤ) (e : F ⊗ G ⟶ G) : regularActionHom F G b :=
  regularShiftedActionGeneral F G b e


/-- The existing degree-zero embedding with its native canonical localization instance.
Source: the supported-cohomology adjunction
(blueprint: def-pur-regular-immersion-class-data). -/
def regularSingle (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) :=
  _root_.DerivedCategory.singleFunctor
    (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)) 0

/-- The existing shifted finite Tate line A(r)[2r] on the small pro-etale site.
Source: the displayed purity isomorphism
(blueprint: def-pur-regular-immersion-class-data). -/
def regularTate (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) (r : ℤ) :
    _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} P.Coefficient)) :=
  ((P.regularSingle X).obj ((comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).obj
    (Scheme.finiteEtaleTateSheaf P.Coefficient P.diagonalExponent X
      P.diagonalExponent_annihilates r)))⟦2 * r⟧

/-- The chosen Cartesian identification associated with an actual pullback square.
Source: etale base change in sk-thm-regular(d)
(blueprint: def-pur-regular-immersion-class-data). -/
def regularSquare {Z X D Y : Scheme.{u}} {i : Z ⟶ X} {j : D ⟶ Y}
    {v : Y ⟶ X} {g : D ⟶ Z} (sq : IsPullback g j i v) :
    ChosenCartesianSquare g j i v where
  w := sq.w
  isoPullback := sq.isoPullback
  hom_fst := sq.isoPullback_hom_fst
  hom_snd := sq.isoPullback_hom_snd

/-- The two published names for the identical pro-etale supported-Hom carrier.
Source: the supported-cohomology identification in sk-thm-regular
(blueprint: def-pur-regular-immersion-class-data).
Proof: unfold the Boolean true branch, the common degree-zero embedding, and the
finite Tate sheaf. Both sides are the same Hom in the same canonical localization.
This equality transports carriers only and changes no class or normalization. -/
theorem regularSupportedHom_eq (P : PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) (c : ℕ) :
    P.FunctorialCupH true i (2 * (c : ℤ)) c =
      cupSupportedHom P i ((cupSingle P X).obj (P.frameTwist X c)) (2 * (c : ℤ)) := by
  sorry

/-- Canonical pullback of a supported class, using the actual exact inverse image,
closed coefficient exchange and the root-normalized Tate-line pullback.
Source: the restriction of a fundamental class to a frame
(blueprint: def-pur-regular-immersion-class-data). -/
def regularSupportedPullback (P : PurityFiniteSetting.{u})
    {Z X D Y : Scheme.{u}} (i : Z ⟶ X) (j : D ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] (v : Y ⟶ X) (g : D ⟶ Z)
    (sq : IsPullback g j i v) (aX : X ⟶ Spec (.of P.field.k)) (c : ℕ)
    (γ : cupSupportedHom P i ((cupSingle P X).obj (P.frameTwist X c)) (2 * (c : ℤ))) :
    cupSupportedHom P j ((cupSingle P Y).obj (P.frameTwist Y c)) (2 * (c : ℤ)) :=
  cast (P.regularSupportedHom_eq j c)
    (P.functorialCupPullback true i j v g (regularSquare sq) aX (2 * (c : ℤ)) c
      (cast (P.regularSupportedHom_eq i c).symm γ))

/-- The precise frame normalization of a global supported class. The boundary fold
is definitionally the frameClass of def-pur-frame-class wherever its smooth-dimension
binders apply; that fold itself is defined for every k-scheme and ordered tuple.
Source: the fundamental-class paragraph
(blueprint: def-pur-regular-immersion-class-data). -/
def RegularFrameNormalization (P : PurityFiniteSetting.{u}) {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (aX : X ⟶ Spec (.of P.field.k)) (c : ℕ)
    (γ : cupSupportedHom P i ((cupSingle P X).obj (P.frameTwist X c)) (2 * (c : ℤ))) : Prop :=
  ∀ F : i.EtaleFrame c,
    P.regularSupportedPullback i (F.U.zeroLocusSubschemeι (Set.range F.f)) F.e F.toZ
      F.isPullback aX c γ =
        P.frameBoundaryProduct F.U (F.e ≫ aX) c F.f

/-- The frame classes glue uniquely, including the empty-frame unit at c=0.
Source: blueprint main-20261015, def-pur-regular-immersion-class-data, fundamental class
(blueprint: def-pur-regular-immersion-class-data).
Proof: sk-thm-regular applies smooth purity to the structure morphisms of X and Z,
cancels their Tate lines using the co-projection, and identifies supported cohomology
with sections of the resulting degree-zero sheaf. Regularity over the perfect base
makes Z smooth; split into the finitely many clopen constant-dimension loci when needed.
Regular equations give local frames. Lem-pur-frame-independence identifies their ordered
boundary products on overlaps. The sheaf axiom then gives existence and uniqueness.
At c=0 these are the unit sections; empty components contribute the zero category. -/
theorem regularFundamentalClass_existsUnique (P : PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (aX : X ⟶ Spec (.of P.field.k)) [IsSeparated aX] [QuasiCompact aX] [Smooth aX]
    (c : ℕ) (hi : PurityConventions.IsRegularOfPureCodimension i c)
    (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z)) :
    ∃! γ : cupSupportedHom P i ((cupSingle P X).obj (P.frameTwist X c)) (2 * (c : ℤ)),
      P.RegularFrameNormalization i aX c γ := by
  sorry

/-- The fundamental class is the unique class with the specified local boundary products.
Source: the fundamental-class paragraph
(blueprint: def-pur-regular-immersion-class-data). -/
def regularFundamentalClass (P : PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (aX : X ⟶ Spec (.of P.field.k)) [IsSeparated aX] [QuasiCompact aX] [Smooth aX]
    (c : ℕ) (hi : PurityConventions.IsRegularOfPureCodimension i c)
    (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z)) :
    cupSupportedHom P i ((cupSingle P X).obj (P.frameTwist X c)) (2 * (c : ℤ)) :=
  (P.regularFundamentalClass_existsUnique i aX c hi hZ).exists.choose

/-- The published proper compact-support comparison, specialized to a closed immersion.
Source: sk-thm-regular (blueprint: def-pur-regular-immersion-class-data). -/
def regularProperComparison (P : PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [HasCompactification i] :
    rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) i ≅
      (lowerStar (ModuleCat.{u + 1} P.Coefficient) i).rightDerivedFunctor :=
  rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar (ModuleCat.{u + 1} P.Coefficient) i

/-- The actual finite coefficient quotient is Noetherian, as required by the
published flat inverse-image instance. Source: the fixed finite coefficient setting
(blueprint: def-pur-regular-immersion-class-data).
Proof: Padic.finite_coefficientExtensionRing gives finiteness at the positive level.
ULift preserves finiteness. Every ideal of a finite ring is a finite set, hence is
finitely generated by its elements; this is the Noetherian ring condition. -/
@[instance]
theorem regularCoefficient_noetherian (P : PurityFiniteSetting.{u}) :
    IsNoetherianRing P.Coefficient := by
  sorry

/-- The canonical identification Ri_! A_Z = i_* A_Z[0]. It uses the published closed
compact-support comparison and the exact derived/single comparisons.
Source: the supported-cohomology adjunction in sk-thm-regular, Step 2b
(blueprint: def-pur-regular-immersion-class-data). -/
def regularClosedCoefficient (P : PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [HasCompactification i] [IsNoetherian X] :=
  letI := preservesFiniteColimits_lowerStar_of_isCompl (R := P.Coefficient)
    i i.openComplement.ι
      (i.range_eq_compl_range_openComplement_ι.symm ▸
        (isCompl_compl (x := Set.range i.openComplement.ι)).symm)
  regularClosedCoefficientGeneral (ModuleCat.{u + 1} P.Coefficient) i (P.constant Z)

/-- The coefficient unit is bounded below of etale origin.
Source: finite coefficient conventions and exact comparison
(blueprint: def-pur-regular-immersion-class-data).
Proof: the constant pro-etale sheaf is comparison inverse image of the etale constant
sheaf. The single-complex comparison identifies their degree-zero embeddings; the
etale object is concentrated in degree zero, so is bounded below. -/
theorem regularConstantOrigin (P : PurityFiniteSetting.{u}) (Z : Scheme.{u}) :
    ProEtale.DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} P.Coefficient) Z
      ((P.regularSingle Z).obj (P.constant Z)) := by
  sorry

/-- The shifted line is bounded below for every signed twist.
Source: finite coefficient twists (blueprint: def-pur-regular-immersion-class-data).
Proof: its sheaf is placed in degree zero and shifted by the finite integer 2r.
It is therefore concentrated in degree -2r and is bounded below. -/
theorem regularTatePlus (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) (r : ℤ) :
    _root_.DerivedCategory.TStructure.t.plus (P.regularTate X r) := by
  sorry

/-- The published finite exceptional composite in the actual coefficient ring.
The finite instance is the existing quotient-finiteness theorem, transported by ULift.
Source: the finite exceptional functor in sk-thm-regular
(blueprint: def-pur-regular-immersion-class-data). -/
def regularExceptional (P : PurityFiniteSetting.{u}) {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i]
    (_aX : X ⟶ Spec (.of P.field.k)) :
    _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} P.Coefficient)) ⥤
      _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Z)
        (ModuleCat.{u + 1} P.Coefficient)) :=
  letI : Finite P.Ring := Padic.finite_coefficientExtensionRing P.coefficients.l
    P.extension P.level P.level_pos
  rightDerivedUpperShriek (ModuleCat.{u + 1} P.Coefficient) i

/-- The published finite exceptional counit with compactness deduced from the structure map.
Source: the adjunction in sk-thm-regular
(blueprint: def-pur-regular-immersion-class-data). -/
def regularCounit (P : PurityFiniteSetting.{u}) {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i]
    (aX : X ⟶ Spec (.of P.field.k)) [QuasiCompact aX]
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} P.Coefficient))) (hK : _root_.DerivedCategory.TStructure.t.plus K) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) i).obj
      ((P.regularExceptional i aX).obj K) ⟶ K :=
  letI : Finite P.Ring := Padic.finite_coefficientExtensionRing P.coefficients.l
    P.extension P.level P.level_pos
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  rightDerivedUpperShriekCounit (A := ModuleCat.{u + 1} P.Coefficient) i K hK

/-- The actual exceptional adjunction, with its closed coefficient source comparison.
Its inverse sends f to Ri_!(f) followed by the published counit, precomposed by the
inverse closed coefficient comparison. Thus it sends a class to the map taking 1 to it.
Source: sk-thm-regular, supported-cohomology identification
(blueprint: def-pur-regular-immersion-class-data). -/
def regularSupportedEquivNative (P : PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (aX : X ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aX] [QuasiCompact aX] (c : ℕ) :=
  letI : Finite P.Ring := Padic.finite_coefficientExtensionRing P.coefficients.l
    P.extension P.level P.level_pos
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian aX
  letI : IsNoetherian X := {}
  regularSupportedEquivGeneral (ModuleCat.{u + 1} P.Coefficient) i
    ((P.regularSingle Z).obj (P.constant Z)) (P.regularTate X c)
    ((P.regularSingle X).obj ((lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj
      (P.constant Z)))
    (P.regularConstantOrigin Z) (P.regularTatePlus X c) (P.regularClosedCoefficient i)

/-- The native exceptional adjunction has exactly the supported-cohomology source
and the displayed exceptional target. Source: sk-thm-regular(a)
(blueprint: def-pur-regular-immersion-class-data).
Proof: unfold cupSupportedHom, regularTate and both names for the degree-zero embedding.
The source is the same closed-pushforward Hom, and the target is the exceptional Hom;
all localization instances are the same canonical instance. -/
theorem regularSupportedEquiv_type (P : PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (aX : X ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aX] [QuasiCompact aX] (c : ℕ) :
    (type_of% (P.regularSupportedEquivNative i aX c)) =
      (cupSupportedHom P i ((cupSingle P X).obj (P.frameTwist X c)) (2 * (c : ℤ)) ≃
        ((P.regularSingle Z).obj (P.constant Z) ⟶
          (P.regularExceptional i aX).obj (P.regularTate X c))) := by
  sorry

/-- The actual exceptional adjunction in the supported-class carrier; the cast identifies
only the two names for the same canonical degree-zero embedding.
Source: sk-thm-regular(a) (blueprint: def-pur-regular-immersion-class-data). -/
def regularSupportedEquiv (P : PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (aX : X ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aX] [QuasiCompact aX] (c : ℕ) :=
  cast (P.regularSupportedEquiv_type i aX c) (P.regularSupportedEquivNative i aX c)

/-- The specified morphism cl_i, the adjunction transpose of the normalized class.
Source: the displayed map 1 to [Z subset X]
(blueprint: def-pur-regular-immersion-class-data). -/
def regularFundamentalClassMap (P : PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (aX : X ⟶ Spec (.of P.field.k)) [IsSeparated aX] [QuasiCompact aX] [Smooth aX]
    (c : ℕ) (hi : PurityConventions.IsRegularOfPureCodimension i c)
    (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z)) :=
  P.regularSupportedEquiv i aX c (P.regularFundamentalClass i aX c hi hZ)


end WeilConjectures.PurityFiniteSetting
