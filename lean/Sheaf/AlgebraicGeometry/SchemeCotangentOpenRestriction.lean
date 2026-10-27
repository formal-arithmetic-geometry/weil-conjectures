/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q70
-/
module

public import Sheaf.AlgebraicGeometry.SchemeLiftClassificationData
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import WeilConjectures.AlgebraicGeometry.OpenRestrictedTensorComplexIso

/-! # Cotangent Ext classification of marked scheme lifts

Source: Stacks Project, Deformation Theory, Tags 0D14, 0GPZ, 0GQ0--0GQ2;
Cotangent Complex, Tags 08UW and 08UZ; More on Morphisms, Tag 0D0I
(blueprint: def-sfb-scheme-cotangent-open-restriction).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option genSizeOfSpec false
set_option genInjectivity false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite
open Algebra.CotangentResolution Simplicial

namespace AlgebraicGeometry.SchemeDeformation

variable [∀ B : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} B)]
  [∀ X : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf)]

/-- Exactness of ordinary restriction, transported through the recorded localized-site
comparison. Source: Stacks 08BW (blueprint: def-sfb-scheme-cotangent-open-restriction). -/
instance restrictionExact {X : Scheme.{u}} (U : X.Opens) :
    PreservesFiniteLimits (Scheme.Modules.restrictFunctor U.ι) :=
  letI := moduleOverFunctor_limits X.toRingedSpace U
  preservesFiniteLimits_of_natIso (Scheme.Modules.overFunctorEquiv U)

/-- Ordinary restriction in the recorded raw module category. Source: Stacks 08BW
(blueprint: def-sfb-scheme-cotangent-open-restriction). -/
abbrev restrictionFunctor {X : Scheme.{u}} (U : X.Opens) :
    SheafOfModules.{u} X.ringCatSheaf ⥤ SheafOfModules.{u} U.toScheme.ringCatSheaf :=
  Scheme.Modules.restrictFunctor U.ι

/-- The sectionwise restriction of the standard cotangent model, retaining the canonical
ring square and its formula on the generating local sections. Source: Stacks 08SV
(blueprint: def-sfb-scheme-cotangent-open-restriction). -/
structure OpenComparison (C : Coherence.{u}) (D : TopCat.SheafCotangent.Comparison C)
    {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens) where
  square : CotangentPresentation.BaseSquare f (U.ι ≫ f) U.ι (𝟙 S)
  comparison : ((restrictionFunctor U).mapHomologicalComplex (.up ℤ)).obj
    (cotangentComplex C D f) ≅ cotangentComplex C D (U.ι ≫ f)
  sections (V : X.Opens) (n : ℤ)
    (x : (standardComplex C (TopCat.SheafCotangent.sectionArrow
      (Arrow.mk (Scheme.Modules.tensorPullbackRingMap f)) (op V))).X n) :
    (comparison.hom.f n).val.app (op (U.ι ⁻¹ᵁ V))
      (((SingleComplexBaseChange.openTensorRestrictionIso U.ι).hom.app
        ((cotangentComplex C D f).X n)).app (U.ι ⁻¹ᵁ V)
        (Scheme.Modules.tensorPullbackSection U.ι _ V
          (TopCat.SheafCotangent.sectionElement
            (D.sheaves X.carrier (Arrow.mk (Scheme.Modules.tensorPullbackRingMap f))).sections
            (op V) n x))) =
      TopCat.SheafCotangent.sectionElement
        (D.sheaves U.toScheme.carrier
          (Arrow.mk (Scheme.Modules.tensorPullbackRingMap (U.ι ≫ f)))).sections
        (op (U.ι ⁻¹ᵁ V)) n ((standardComplexMap C (square.sectionSquare V)).f n x)

/-- Restriction on derived Hom: apply the exact restriction functor, use its shift and
single-object comparisons, and the normalized cotangent comparison. Source: Stacks 0GQ1
(blueprint: def-sfb-scheme-cotangent-open-restriction). -/
def OpenComparison.ext {C : Coherence.{u}} {D : TopCat.SheafCotangent.Comparison C}
    {X S : Scheme.{u}} {f : X ⟶ S} {U : X.Opens} (o : OpenComparison C D f U)
    (G : X.Modules) (n : ℤ) (ξ : Ext C D f G n) :
    Ext C D (U.ι ≫ f) ((restrictionFunctor U).obj G) n :=
  ((DerivedCategory.Q (C := SheafOfModules.{u} U.toScheme.ringCatSheaf)).mapIso
    o.comparison).inv ≫
    (restrictionFunctor U).mapDerivedCategoryFactors.inv.app _ ≫
    (restrictionFunctor U).mapDerivedCategory.map ξ ≫
    ((restrictionFunctor U).mapDerivedCategory.commShiftIso n).hom.app _ ≫
    ((restrictionFunctor U).mapDerivedCategorySingleFunctor 0).hom.app G⟦n⟧'

/-- Ordinary coefficient restriction; the unit normalization determines the isomorphism.
Source: Stacks 0097, 0D14 (blueprint: def-sfb-scheme-cotangent-open-restriction). -/
def coefficientRestriction {X S S' : Scheme.{u}} (f : X ⟶ S) (i : S ⟶ S')
    (U : X.Opens) : (Scheme.Modules.restrictFunctor U.ι).obj (coefficient f i) ≅
      coefficient (U.ι ≫ f) i :=
  ((SingleComplexBaseChange.openTensorRestrictionIso U.ι).app (coefficient f i)).symm ≪≫
    ((Scheme.Modules.tensorPullbackSectionComp U.ι f).app _).symm

/-- Restriction of the actual split coefficient sheaf, with the pullback-composition
normalization. Source: Stacks 0GQ1
(blueprint: def-sfb-scheme-cotangent-open-restriction). -/
def directionRestriction {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (M : ModuleCat.{u} k) (U : X.Opens) :
    (restrictionFunctor U).obj (directionModule f M) ≅ directionModule (U.ι ≫ f) M :=
  ((SingleComplexBaseChange.openTensorRestrictionIso U.ι).app (directionModule f M)).symm ≪≫
    ((Scheme.Modules.tensorPullbackSectionComp U.ι f).app _).symm

end AlgebraicGeometry.SchemeDeformation
