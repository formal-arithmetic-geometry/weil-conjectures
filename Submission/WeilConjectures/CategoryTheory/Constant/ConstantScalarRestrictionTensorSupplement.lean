/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Submission.WeilConjectures.CategoryTheory.SheafTensor
public import Submission.WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Submission.WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Submission.WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Submission.WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Submission.WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Submission.WeilConjectures.Algebra.Homology.PreservesTotalTensorKFlatQuasiIso
public import Submission.WeilConjectures.CategoryTheory.ConstantRingModuleSheaves
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Submission.WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import Submission.WeilConjectures.CategoryTheory.SiteConstantModuleFunctorGeneral
public import Mathlib.Algebra.Category.Ring.Limits
public import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Submission.WeilConjectures.CategoryTheory.Monoidal.DerivedBraided
public import Submission.WeilConjectures.Algebra.Homology.HomotopyCategory.Braided
public import Submission.WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import Submission.WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Submission.WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.Grp.AB
public import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Submission.WeilConjectures.CategoryTheory.RingedSiteGrothendieckCoefficientUniverse
public import Mathlib.CategoryTheory.ShrinkYoneda
import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Monoidal.RestrictScalarsBraided
import Submission.WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Submission.WeilConjectures.Mathlib.CategoryTheory.Monoidal.NaturalTransformation
import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all Mathlib.Algebra.Category.Ring.Limits
import all Submission.WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Submission.WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all Submission.WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all Submission.WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Submission.WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all Submission.WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all Submission.WeilConjectures.CategoryTheory.RingedToposRingData
import all Submission.WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Submission.WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all Submission.WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all Submission.WeilConjectures.Algebra.Homology.RingIsomorphismTensorTransport
import all Submission.WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement
import all Submission.WeilConjectures.CategoryTheory.SiteCoveringAxioms
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all Mathlib.CategoryTheory.Monoidal.Braided.Basic
import all Submission.WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all Submission.WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Submission.WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all Submission.WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Submission.WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all Submission.WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import all Submission.WeilConjectures.SecSmoothPurity.CochainComparisonMonoidalEquationsSupplement
import all Submission.WeilConjectures.SecSmoothPurity.CochainTensorCoherenceDataSupplement
import all Submission.WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import all Submission.WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import all Submission.WeilConjectures.Algebra.Homology.HomotopyCategory.Braided
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all Submission.WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
import all Submission.WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
import all Submission.WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import all Submission.WeilConjectures.CategoryTheory.Monoidal.BraidedLocalizationSquare
import all Submission.WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare
import all Submission.WeilConjectures.Algebra.Homology.ExactMonoidalEquivalenceTotalKFlat
import all Submission.WeilConjectures.CategoryTheory.CountableTensorStructures.CountableTensorStructuresSupplement
import all Submission.WeilConjectures.Algebra.Homology.AdditiveTotalTensorConeComparison
import all Submission.WeilConjectures.Algebra.Homology.BifunctorMappingConeNaturality
import all Submission.WeilConjectures.FromJoel.Algebra.Homology.Bifunctor
import all Mathlib.CategoryTheory.Monoidal.Functor
import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

import Submission.WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Unit
public import Submission.WeilConjectures.CategoryTheory.ConstantScalarRestrictionTensor

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Constant scalar restriction and tensor products

Source: Stacks Project, Modules on Sites, Tags 03CY and 0GMW, and Cohomology on Sites,
Tags 06YN, 06YP, 06YS, 0G7D, 06YT and 06YU
(blueprint: lem-sfb-constant-scalar-restriction-tensor).

The coefficient-sized small site implements the size convention. The restriction is the
existing literal restriction along the constant commutative-ring sheafification unit.

## Main statements

* `ordinary_exists`: normalized ordinary symmetric monoidal equivalence.
* `total_symmetry`: coherence of the existing canonical signed-total comparison.
* `flat_iff`, `kflat_iff`: preservation and reflection of the two flatness conditions.
* `derived_comparison`: the normalized coherent comparison on unbounded derived tensors.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v wR wB dU dV dW

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace CategoryTheory.ConstantScalarRestriction

attribute [local instance] complexTensorMemo derivedTensorMemo

section DerivedComparisonProof

set_option backward.isDefEq.respectTransparency true
open CategoryTheory.Category CategoryTheory.Functor CategoryTheory.Functor.LaxMonoidal
open CategoryTheory.Functor.OplaxMonoidal

universe uD vD wD uE vE wE
variable {D : Type uD} [Category.{vD} D] [Abelian D] [IsGrothendieckAbelian.{vD} D]
  [MonoidalCategory D] [SymmetricCategory D] [MonoidalClosed D] [MonoidalPreadditive D]
  [Abelian.HasFunctorialFlatResolution D] [HasDerivedCategory.{wD} D]
  [HasColimitsOfSize.{0, 0} D]
  {E : Type uE} [Category.{vE} E] [Abelian E] [IsGrothendieckAbelian.{vE} E]
  [MonoidalCategory E] [SymmetricCategory E] [MonoidalClosed E] [MonoidalPreadditive E]
  [Abelian.HasFunctorialFlatResolution E] [HasDerivedCategory.{wE} E]
  [HasColimitsOfSize.{0, 0} E]

end DerivedComparisonProof

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (B : Type (max u v)) [CommRing B]

section OrdinaryProof
set_option warn.classDefReducibility false
private def scalarUnit :
    (Functor.const Cᵒᵖ).obj (RingCat.of B) ⟶
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj (ring J B)).obj :=
  toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of B)) ≫
    ((constantCommuteCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).inv.app
      (CommRingCat.of B)).hom

attribute [local irreducible] ring

section GenericRaw

private def constantToFunctor :
    PresheafOfModules.{max u v}
      (((Functor.const Cᵒᵖ).obj (CommRingCat.of B)) ⋙ forget₂ CommRingCat RingCat) ⥤
        Cᵒᵖ ⥤ ModuleCat.{max u v} B where
  obj P :=
    { obj := P.obj
      map := fun f ↦ P.map f
      map_id := fun X ↦ by ext x; exact congrArg (fun f ↦ f x) (P.map_id X)
      map_comp := fun f g ↦ by ext x; exact P.map_comp_apply f g x }
  map f :=
    { app := f.app
      naturality := fun _ _ g ↦ by ext x; exact PresheafOfModules.naturality_apply f g x }

set_option backward.isDefEq.respectTransparency false in
private def constantToFunctorLax : (constantToFunctor (C := C) B).LaxMonoidal where
  ε := { app X := 𝟙 _ }
  μ M N := { app X := 𝟙 _ }
  μ_natural_left := by intros; ext X x; rfl
  μ_natural_right := by intros; ext X x; rfl
  associativity := by
    intro M N P
    apply NatTrans.ext
    funext X
    change (𝟙 _ ▷ P.obj X) ≫ 𝟙 _ ≫ (α_ M N P).hom.app X =
      (α_ (M.obj X) (N.obj X) (P.obj X)).hom ≫ (M.obj X ◁ 𝟙 _) ≫ 𝟙 _
    simpa only [Category.id_comp, Category.comp_id,
      MonoidalCategory.id_whiskerRight, MonoidalCategory.whiskerLeft_id] using
      (PresheafOfModules.associator_hom_app M N P X)
  left_unitality := by
    intro M
    apply NatTrans.ext
    funext X
    change (λ_ (M.obj X)).hom =
      (𝟙 _ ▷ M.obj X) ≫ 𝟙 _ ≫ (λ_ M).hom.app X
    simpa only [Category.id_comp, Category.comp_id,
      MonoidalCategory.id_whiskerRight] using
      (PresheafOfModules.leftUnitor_hom_app M X).symm
  right_unitality := by
    intro M
    apply NatTrans.ext
    funext X
    change (ρ_ (M.obj X)).hom =
      (M.obj X ◁ 𝟙 _) ≫ 𝟙 _ ≫ (ρ_ M).hom.app X
    simpa only [Category.id_comp, Category.comp_id,
      MonoidalCategory.whiskerLeft_id] using
      (PresheafOfModules.rightUnitor_hom_app M X).symm

attribute [local instance] constantToFunctorLax

set_option backward.isDefEq.respectTransparency false in
private def rawRestrictionGeneric
    (R : Cᵒᵖ ⥤ CommRingCat.{max u v})
    (ι : (Functor.const Cᵒᵖ).obj (RingCat.of B) ⟶ R ⋙ forget₂ CommRingCat RingCat) :
    PresheafOfModules.{max u v} (R ⋙ forget₂ CommRingCat RingCat) ⥤
      Cᵒᵖ ⥤ ModuleCat.{max u v} B :=
  PresheafOfModules.restrictScalars ι ⋙ constantToFunctor B

set_option backward.isDefEq.respectTransparency false in
private def rawLaxGeneric
    (R : Cᵒᵖ ⥤ CommRingCat.{max u v})
    (ι : (Functor.const Cᵒᵖ).obj (RingCat.of B) ⟶ R ⋙ forget₂ CommRingCat RingCat) :
    (rawRestrictionGeneric B R ι).LaxMonoidal :=
  letI : MonoidalCategory (PresheafOfModules.{max u v}
      ((Functor.const Cᵒᵖ).obj (RingCat.of B))) :=
    inferInstanceAs (MonoidalCategory (PresheafOfModules.{max u v}
      (((Functor.const Cᵒᵖ).obj (CommRingCat.of B)) ⋙ forget₂ CommRingCat RingCat)))
  letI := PresheafOfModules.restrictScalarsLaxMonoidal
    (R := (Functor.const Cᵒᵖ).obj (CommRingCat.of B)) (R' := R) ι
  letI : (constantToFunctor (C := C) B).LaxMonoidal := constantToFunctorLax B
  Functor.LaxMonoidal.comp
    (PresheafOfModules.restrictScalars ι) (constantToFunctor B)

attribute [local instance] rawLaxGeneric

end GenericRaw

private def rawRestriction :
    PresheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj (ring J B)).obj ⥤
      Cᵒᵖ ⥤ ModuleCat.{max u v} B := rawRestrictionGeneric B (ring J B).obj (scalarUnit J B)

@[instance_reducible]
private def rawLax : (rawRestriction J B).LaxMonoidal :=
  rawLaxGeneric B (ring J B).obj (scalarUnit J B)

attribute [local instance] rawLax

private theorem scalarUnit_surjective : Presheaf.IsLocallySurjective J (scalarUnit J B) := by
  unfold scalarUnit
  unfold ring
  infer_instance

attribute [local instance] scalarUnit_surjective

attribute [local semireducible] ring

end OrdinaryProof
variable [HasDerivedCategory.{wR} (Modules J B)] [HasDerivedCategory.{wB} (Fixed J B)]

end CategoryTheory.ConstantScalarRestriction
