/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
import WeilConjectures.Algebra.Category.ModuleCat.DerivedBaseChange
import WeilConjectures.CategoryTheory.Sites.ReductionFlat
import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat

/-! # Normalized ordinary coefficient scalar representatives

Source: Stacks 03EK, 03EL, 06YY and 07A4; the scalar and comparison constructions
in the finite-coefficient paragraph of scalar-six direct image
(blueprint: def-sp-coefficient-scalar-representatives).

These are the ordinary unbounded derived categories of module-valued sheaves.
The chosen scalar left adjoint is determined by actual derived restriction.
The representative arrow is defined by transposing the ordinary scalar unit.
The scalar adjunction is built in this module from the upstream K-flat derived
adjunctions; the module imports only upstream and Mathlib modules.
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u v₁ v₂

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.CoefficientScalarRepresentatives

set_option Elab.async false


section Site

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C)
  {A B : Type (u + 1)} [CommRing A] [CommRing B] (a : A →+* B)

attribute [local irreducible] scalarDerivedAdjunctionData

attribute [local irreducible] scalarDerivedAdjunction ordinaryExtension ordinaryAdjunction

/-- Sheafified sectionwise extension of scalars.
Source: Stacks 03EK (blueprint: def-sp-coefficient-scalar-representatives). -/
def ordinaryExtension : Sheaf J (ModuleCat.{u + 1} A) ⥤
    Sheaf J (ModuleCat.{u + 1} B) :=
  Sheaf.composeAndSheafify J (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} a)

/-- The actual ordinary extension/restriction adjunction, normalized by its tensor unit.
Source: Stacks 03EK (blueprint: def-sp-coefficient-scalar-representatives). -/
def ordinaryAdjunction : ordinaryExtension J a ⊣ Sheaf.restrictScalars J a :=
  Sheaf.adjunction J (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} a)

/-- Countable coproducts in the ordinary module-sheaf category, with the same
chosen construction used by the native scalar derived adjunction.
Source: Stacks 06YY (blueprint: def-sp-coefficient-scalar-representatives). -/
instance sheaf_countableCoproducts (R : Type (u + 1)) [CommRing R] :
    HasCountableCoproducts (Sheaf J (ModuleCat.{u + 1} R)) :=
  haveI : HasColimitsOfSize.{u + 1, u + 1} (Sheaf J (ModuleCat.{u + 1} R)) :=
    IsGrothendieckAbelian.hasColimits _
  haveI : HasColimitsOfSize.{0, 0} (Sheaf J (ModuleCat.{u + 1} R)) :=
    hasColimitsOfSizeShrink.{0, 0, u + 1, u + 1} _
  ⟨fun K _ ↦ HasColimitsOfSize.has_colimits_of_shape (Discrete K)⟩

private instance ordinaryExtension_preservesKFlat {R S : Type (u + 1)}
    [CommRing R] [CommRing S] (φ : R →+* S) :
    (ordinaryExtension J φ).PreservesKFlatQuasiIso := by
  classical
  let E := ordinaryExtension J φ
  let U := Sheaf.restrictScalars J φ
  let adj : E ⊣ U :=
    Sheaf.adjunction J (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ)
  have : E.Additive := adj.left_adjoint_additive
  let B := (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} φ).obj (ModuleCat.of S S)
  let X := (Functor.const Cᵒᵖ).obj B
  let a := presheafToSheaf J (ModuleCat.{u + 1} R)
  let a' := presheafToSheaf J (ModuleCat.{u + 1} S)
  let F := sheafToPresheaf J (ModuleCat.{u + 1} R)
  let W := (Functor.whiskeringRight Cᵒᵖ _ _).obj
    (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ)
  have : J.PreservesSheafification (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} φ) :=
    Sheaf.preservesSheafification_of_adjunction J
      (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ)
  let e : E ⋙ U ≅ MonoidalCategory.tensorRight (a.obj X) :=
    Functor.associator F (W ⋙ a') U ≪≫
      Functor.isoWhiskerLeft F (Functor.associator W a' U) ≪≫
      Functor.isoWhiskerLeft F (Functor.isoWhiskerLeft W
        (sheafComposeNatIso J (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} φ)
          (sheafificationAdjunction J (ModuleCat.{u + 1} S))
          (sheafificationAdjunction J (ModuleCat.{u + 1} R))).symm) ≪≫
      Functor.isoWhiskerLeft F (Functor.associator W _ a).symm ≪≫
      Functor.isoWhiskerLeft F (Functor.isoWhiskerRight
        (Functor.whiskeringRightObjCompIso _ _ ≪≫
          (Functor.whiskeringRight _ _ _).mapIso
            (ModuleCat.extendScalarsCompRestrictScalarsIso.{u + 1} φ) ≪≫
          whiskeringRightTensorRightIso _) a) ≪≫
      Functor.isoWhiskerLeft F (Sheaf.presheafToSheafCompTensorRightIso X).symm ≪≫
      (Functor.associator F a (MonoidalCategory.tensorRight (a.obj X))).symm ≪≫
      Functor.isoWhiskerRight
        (asIso (sheafificationAdjunction J (ModuleCat.{u + 1} R)).counit)
        (MonoidalCategory.tensorRight (a.obj X)) ≪≫ Functor.leftUnitor _
  have hU : U.Faithful := inferInstance
  have : HasColimitsOfSize.{u + 1, u + 1} (Sheaf J (ModuleCat.{u + 1} R)) :=
    IsGrothendieckAbelian.hasColimits _
  have : HasColimitsOfSize.{0, 0} (Sheaf J (ModuleCat.{u + 1} R)) :=
    hasColimitsOfSizeShrink.{0, 0, u + 1, u + 1} _
  have : HasCountableCoproducts (Sheaf J (ModuleCat.{u + 1} R)) :=
    ⟨fun K _ ↦ HasColimitsOfSize.has_colimits_of_shape (Discrete K)⟩
  have : E.PreservesKFlatQuasiIso := by
    apply CategoryTheory.Functor.PreservesKFlatQuasiIso.mk'
    intro K hK hKa
    have ht := CochainComplex.acyclic_tensorRight_of_kFlat K hK hKa (a.obj X)
    have hEU := ht.of_iso
      ((NatIso.mapHomologicalComplex e (.up ℤ)).app K).symm
    have hUK : ((U.mapHomologicalComplex (.up ℤ)).obj
        ((E.mapHomologicalComplex (.up ℤ)).obj K)).Acyclic :=
      hEU.of_iso ((CategoryTheory.Functor.mapHomologicalComplexCompIso
        (Iso.refl (E ⋙ U)) (.up ℤ)).app K)
    intro n
    exact (ShortComplex.exact_map_iff_of_faithful _ U).1 (hUK n)
  infer_instance

/-- Ordinary scalar extension preserves K-flat quasi-isomorphisms without flatness
of the coefficient map. Source: Stacks 06YY, 07A4
(blueprint: def-sp-coefficient-scalar-representatives).
Proof: restrict the extended complex; it is tensor with the target-ring sheaf.
K-flat acyclicity gives acyclicity after this tensor. Exact faithful restriction
reflects acyclicity, hence reflects the resulting quasi-isomorphism. -/
instance ordinaryExtension_preservesKFlat {R S : Type (u + 1)}
    [CommRing R] [CommRing S] (φ : R →+* S) :
    (ordinaryExtension J φ).PreservesKFlatQuasiIso := by
  classical
  let E := ordinaryExtension J φ
  let U := Sheaf.restrictScalars J φ
  let adj : E ⊣ U :=
    Sheaf.adjunction J (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ)
  have : E.Additive := adj.left_adjoint_additive
  let B := (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} φ).obj (ModuleCat.of S S)
  let X := (Functor.const Cᵒᵖ).obj B
  let a := presheafToSheaf J (ModuleCat.{u + 1} R)
  let a' := presheafToSheaf J (ModuleCat.{u + 1} S)
  let F := sheafToPresheaf J (ModuleCat.{u + 1} R)
  let W := (Functor.whiskeringRight Cᵒᵖ _ _).obj
    (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ)
  have : J.PreservesSheafification (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} φ) :=
    Sheaf.preservesSheafification_of_adjunction J
      (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ)
  let e : E ⋙ U ≅ MonoidalCategory.tensorRight (a.obj X) :=
    Functor.associator F (W ⋙ a') U ≪≫
      Functor.isoWhiskerLeft F (Functor.associator W a' U) ≪≫
      Functor.isoWhiskerLeft F (Functor.isoWhiskerLeft W
        (sheafComposeNatIso J (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} φ)
          (sheafificationAdjunction J (ModuleCat.{u + 1} S))
          (sheafificationAdjunction J (ModuleCat.{u + 1} R))).symm) ≪≫
      Functor.isoWhiskerLeft F (Functor.associator W _ a).symm ≪≫
      Functor.isoWhiskerLeft F (Functor.isoWhiskerRight
        (Functor.whiskeringRightObjCompIso _ _ ≪≫
          (Functor.whiskeringRight _ _ _).mapIso
            (ModuleCat.extendScalarsCompRestrictScalarsIso.{u + 1} φ) ≪≫
          whiskeringRightTensorRightIso _) a) ≪≫
      Functor.isoWhiskerLeft F (Sheaf.presheafToSheafCompTensorRightIso X).symm ≪≫
      (Functor.associator F a (MonoidalCategory.tensorRight (a.obj X))).symm ≪≫
      Functor.isoWhiskerRight
        (asIso (sheafificationAdjunction J (ModuleCat.{u + 1} R)).counit)
        (MonoidalCategory.tensorRight (a.obj X)) ≪≫ Functor.leftUnitor _
  have hU : U.Faithful := inferInstance
  have : HasColimitsOfSize.{u + 1, u + 1} (Sheaf J (ModuleCat.{u + 1} R)) :=
    IsGrothendieckAbelian.hasColimits _
  have : HasColimitsOfSize.{0, 0} (Sheaf J (ModuleCat.{u + 1} R)) :=
    hasColimitsOfSizeShrink.{0, 0, u + 1, u + 1} _
  have : HasCountableCoproducts (Sheaf J (ModuleCat.{u + 1} R)) :=
    ⟨fun K _ ↦ HasColimitsOfSize.has_colimits_of_shape (Discrete K)⟩
  have : E.PreservesKFlatQuasiIso := by
    apply CategoryTheory.Functor.PreservesKFlatQuasiIso.mk'
    intro K hK hKa
    have ht := CochainComplex.acyclic_tensorRight_of_kFlat K hK hKa (a.obj X)
    have hEU := ht.of_iso
      ((NatIso.mapHomologicalComplex e (.up ℤ)).app K).symm
    have hUK : ((U.mapHomologicalComplex (.up ℤ)).obj
        ((E.mapHomologicalComplex (.up ℤ)).obj K)).Acyclic :=
      hEU.of_iso ((CategoryTheory.Functor.mapHomologicalComplexCompIso
        (Iso.refl (E ⋙ U)) (.up ℤ)).app K)
    intro n
    exact (ShortComplex.exact_map_iff_of_faithful _ U).1 (hUK n)
  infer_instance

private noncomputable def scalarDerivedAdjunctionData
    {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (K : GrothendieckTopology C) (φ : R →+* S) :=
  normalizedDerivedAdjunction
    (A := Sheaf K (ModuleCat.{u + 1} R)) (B := Sheaf K (ModuleCat.{u + 1} S))
    (E := ordinaryExtension K φ) (U := Sheaf.restrictScalars K φ)
    (ordinaryAdjunction K φ)

/-- The normalized native scalar derived adjunction. Its unit is the derived
ordinary scalar unit, as fixed by scalarDerivedAdjunctionData.
Source: Stacks 06YY, 07A4
(blueprint: def-sp-coefficient-scalar-representatives). -/
noncomputable def scalarDerivedAdjunction
    {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (K : GrothendieckTopology C) (φ : R →+* S) :
    (ordinaryExtension K φ).leftDerivedFunctor ⊣ Sheaf.derivedRestrictScalars K φ := by
  letI : PreservesFiniteLimits (Sheaf.restrictScalars K φ) := by
    have : PreservesLimitsOfSize.{0, 0} (Sheaf.restrictScalars K φ) :=
      (ordinaryAdjunction K φ).rightAdjoint_preservesLimits
    infer_instance
  letI : PreservesFiniteColimits (Sheaf.restrictScalars K φ) := by
    have : PreservesColimitsOfSize.{0, 0} (Sheaf.restrictScalars K φ) :=
      (Sheaf.restrictCoextendScalarsAdj K φ).leftAdjoint_preservesColimits
    infer_instance
  exact (ordinaryAdjunction K φ).derivedAdjunction.ofNatIsoRight
    (Sheaf.restrictScalars K φ).rightDerivedFunctorIsoMapDerivedCategory

/-- The fixed derived scalar extension, selected by its uniquely determined adjunction.
Source: Stacks 06YY (blueprint: def-sp-coefficient-scalar-representatives). -/
def extension : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A)) ⥤
    DerivedCategory (Sheaf J (ModuleCat.{u + 1} B)) :=
  (Sheaf.derivedRestrictScalars J a).leftAdjoint

/-- The specified scalar adjunction to actual exact derived restriction.
Source: Stacks 06YY (blueprint: def-sp-coefficient-scalar-representatives). -/
def adjunction : extension J a ⊣ Sheaf.derivedRestrictScalars J a :=
  Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars J a)

/-- The canonical representative arrow: transpose the localized ordinary scalar unit.
Source: Stacks 03EK and 06YY (blueprint: def-sp-coefficient-scalar-representatives). -/
def representative
    (P : CochainComplex (Sheaf J (ModuleCat.{u + 1} A)) ℤ) :
    (extension J a).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj (((ordinaryExtension J a).mapHomologicalComplex (.up ℤ)).obj P) :=
  let PE : CochainComplex (Sheaf J (ModuleCat.{u + 1} B)) ℤ :=
    ((ordinaryExtension J a).mapHomologicalComplex (.up ℤ)).obj P
  ((adjunction J a).homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj PE)).symm
    (DerivedCategory.Q.map
      (show P ⟶ ((Sheaf.restrictScalars J a).mapHomologicalComplex (.up ℤ)).obj PE from
        (Functor.mapHomologicalComplexIdIso
          (Sheaf J (ModuleCat.{u + 1} A)) (.up ℤ)).inv.app P ≫
          (NatTrans.mapHomologicalComplex (ordinaryAdjunction J a).unit (.up ℤ)).app P ≫
          (Functor.mapHomologicalComplexCompIso
            (F := ordinaryExtension J a) (G := Sheaf.restrictScalars J a)
            (Iso.refl _) (.up ℤ)).inv.app P) ≫
      (Sheaf.restrictScalars J a).mapDerivedCategoryFactors.inv.app PE)

/-- Scalar composition is the uniqueness comparison conjugate to restriction composition.
Source: Stacks 06YY (blueprint: def-sp-coefficient-scalar-representatives). -/
def composition {D : Type (u + 1)} [CommRing D] (b : B →+* D) :
    extension J a ⋙ extension J b ≅ extension J (b.comp a) :=
  Adjunction.leftAdjointCompIso (adjunction J a) (adjunction J b)
    (adjunction J (b.comp a)) (Sheaf.derivedRestrictScalarsCompIso J rfl)

end Site

section Comparison

open AlgebraicGeometry.ProEtale

variable (T : Scheme.{u}) {A B : Type (u + 1)} [CommRing A] [CommRing B]
  (a : A →+* B)

/-- Ordinary restriction/site comparison, conjugate to the sectionwise coextension square.
Source: Stacks 03D2 and 03EL (blueprint: def-sp-coefficient-scalar-representatives). -/
def comparisonRestriction :
    ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) T ⋙
        Sheaf.restrictScalars (Scheme.ProEt.topology T) a ≅
      Sheaf.restrictScalars T.smallEtaleTopology a ⋙
        ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T :=
  ((conjugateIsoEquiv
    ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} B) T).comp
      (Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology T) a))
    ((Sheaf.restrictCoextendScalarsAdj T.smallEtaleTopology a).comp
      (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T))).symm (Iso.refl _)).symm

/-- Exact termwise localization of the ordinary restriction/site comparison.
Source: Stacks 06YY and 07A4 (blueprint: def-sp-coefficient-scalar-representatives). -/
def derivedComparisonRestriction :
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) T).mapDerivedCategory ⋙
        Sheaf.derivedRestrictScalars (Scheme.ProEt.topology T) a ≅
      Sheaf.derivedRestrictScalars T.smallEtaleTopology a ⋙
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory :=
  Functor.mapDerivedCategorySquareIso (comparisonRestriction T a)

/-- The canonical scalar/site comparison is the inverse mate of restriction comparison.
Source: Stacks 07A4 (blueprint: def-sp-coefficient-scalar-representatives). -/
def comparisonMap :
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory ⋙
        extension (Scheme.ProEt.topology T) a ⟶
      extension T.smallEtaleTopology a ⋙
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) T).mapDerivedCategory :=
  ((mateEquiv (adjunction T.smallEtaleTopology a)
    (adjunction (Scheme.ProEt.topology T) a)).symm
      (TwoSquare.mk _ _ _ _ (derivedComparisonRestriction T a).inv)).natTrans

private theorem comparison_restrict_mate (φ : R →+* S) :
    (mateEquiv (comparisonAdjunction (ModuleCat.{u + 1} S) T)
      (comparisonAdjunction (ModuleCat.{u + 1} R) T)
      (TwoSquare.mk _ _ _ _ (comparisonRestriction T φ).inv)).natTrans = 𝟙 _ := by
  exact mate_of_conjugate
    (comparisonAdjunction (ModuleCat.{u + 1} S) T)
    (comparisonAdjunction (ModuleCat.{u + 1} R) T)
    (Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology T) φ)
    (Sheaf.restrictCoextendScalarsAdj T.smallEtaleTopology φ)
    (Iso.refl _) (𝟙 _) (restrict_coextend_mate T φ)

private theorem ordinary_scalar_mate_isIso (φ : R →+* S) :
    IsIso (((mateEquiv (ordinaryAdjunction T.smallEtaleTopology φ)
      (ordinaryAdjunction (Scheme.ProEt.topology T) φ)).symm
      (TwoSquare.mk _ _ _ _ (comparisonRestriction T φ).inv)).natTrans) := by
  apply isIso_left_mate_of_iterated
    (ordinaryAdjunction T.smallEtaleTopology φ)
    (ordinaryAdjunction (Scheme.ProEt.topology T) φ)
    (comparisonAdjunction (ModuleCat.{u + 1} R) T)
    (comparisonAdjunction (ModuleCat.{u + 1} S) T)
  rw [comparison_restrict_mate]
  infer_instance

private theorem computed_comparison_mate_isIso (φ : R →+* S) :
    IsIso (((mateEquiv
      (G := (comparisonUpperStar (ModuleCat.{u + 1} R) T).mapDerivedCategory)
      (H := (comparisonUpperStar (ModuleCat.{u + 1} S) T).mapDerivedCategory)
      (scalarDerivedAdjunctionData T.smallEtaleTopology φ).adjunction
      (scalarDerivedAdjunctionData (Scheme.ProEt.topology T) φ).adjunction).symm
      (TwoSquare.mk _ _ _ _ (derivedComparisonRestriction T φ).inv)).natTrans) := by
  have := comparison_preservesFlat T R
  have := ordinary_scalar_mate_isIso T φ
  exact derived_mate_isIso_of_flat
    (A := Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R))
    (B := Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} S))
    (C := Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} R))
    (D := Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} S))
    (E₁ := ordinaryExtension T.smallEtaleTopology φ)
    (E₂ := ordinaryExtension (Scheme.ProEt.topology T) φ)
    (U₁ := Sheaf.restrictScalars T.smallEtaleTopology φ)
    (U₂ := Sheaf.restrictScalars (Scheme.ProEt.topology T) φ)
    (ordinaryAdjunction T.smallEtaleTopology φ)
    (ordinaryAdjunction (Scheme.ProEt.topology T) φ)
    (scalarDerivedAdjunctionData T.smallEtaleTopology φ)
    (scalarDerivedAdjunctionData (Scheme.ProEt.topology T) φ)
    (comparisonUpperStar (ModuleCat.{u + 1} R) T)
    (comparisonUpperStar (ModuleCat.{u + 1} S) T)
    (comparisonRestriction T φ)

/-- The specified scalar/site arrow is invertible; no different arrow is chosen.
Source: Stacks 07A4 and 0G7E (blueprint: def-sp-coefficient-scalar-representatives).

Proof: the ordinary restriction square is conjugate to the sectionwise
coextension/direct-image identity. Iterated mates identify its inverse scalar
mate with the ordinary tensor/site comparison. Inverse image preserves flat-term
K-flat resolutions by the local relation criterion and commutes with tensor
products. On those representatives the displayed derived mate, computed with
the scalar unit used in representative, is therefore invertible. Localization
and the unique unit-compatible scalar adjoint comparison give invertibility
for the specified fixed functors, on all unbounded objects. -/
@[instance] theorem comparisonMap_isIso : IsIso (comparisonMap T a) := by
  have := computed_comparison_mate_isIso T a
  exact isIso_left_mate_change_adjunction
    (F := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory)
    (G := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) T).mapDerivedCategory)
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars T.smallEtaleTopology a))
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology T) a))
    (scalarDerivedAdjunctionData T.smallEtaleTopology a).adjunction
    (scalarDerivedAdjunctionData (Scheme.ProEt.topology T) a).adjunction
    (derivedComparisonRestriction T a).inv

section ComparisonProof

variable {R S : Type (u + 1)} [CommRing R] [CommRing S]

attribute [local irreducible] comparisonRestriction

end ComparisonProof

/-- Regard that very mate as the tensor/site isomorphism.
Source: Stacks 07A4 (blueprint: def-sp-coefficient-scalar-representatives). -/
def comparisonIso :
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory ⋙
        extension (Scheme.ProEt.topology T) a ≅
      extension T.smallEtaleTopology a ⋙
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) T).mapDerivedCategory :=
  asIso (comparisonMap T a)

end Comparison

end AlgebraicGeometry.CoefficientScalarRepresentatives
