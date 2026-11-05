/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
import WeilConjectures.Algebra.Category.ModuleCat.DerivedBaseChange
import WeilConjectures.CategoryTheory.Sites.ReductionFlat

/-! # The retained scalar adjunction independently of quotient parameters

Source: Stacks 07A6, 0B65 and 0DV0
(blueprint: def-weil-pbc-constant-coefficient-scalar-extension).
The ordinary construction and the fixed left adjoint are relocated from
Sheaf.Paper.WitnessCompatibility, which keeps private aliases of the ordinary helpers.
The helper facts are theorems, used here only as local instances; no global instance
other than the retained `pbcRestriction_isRightAdjoint` is declared.
No alternative scalar functor is selected.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale
variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C)

/-- Helper of the retained scalar adjunction, relocated with its existing proof.
Source: Stacks 07A6 (blueprint: def-weil-pbc-constant-coefficient-scalar-extension). -/
theorem pbcFixedScalarSheafCountableCoproducts (R : Type (u + 1)) [CommRing R] :
    HasCountableCoproducts (Sheaf J (ModuleCat.{u + 1} R)) :=
  haveI : HasColimitsOfSize.{u + 1, u + 1} (Sheaf J (ModuleCat.{u + 1} R)) :=
    IsGrothendieckAbelian.hasColimits _
  haveI : HasColimitsOfSize.{0, 0} (Sheaf J (ModuleCat.{u + 1} R)) :=
    hasColimitsOfSizeShrink.{0, 0, u + 1, u + 1} _
  ⟨fun K _ ↦ HasColimitsOfSize.has_colimits_of_shape (Discrete K)⟩

attribute [local instance] pbcFixedScalarSheafCountableCoproducts

/-- Helper of the retained scalar adjunction, relocated with its existing proof.
Source: Stacks 07A6 (blueprint: def-weil-pbc-constant-coefficient-scalar-extension). -/
noncomputable def pbcFixedScalarSheafExtension {R S : Type (u + 1)}
    [CommRing R] [CommRing S] (φ : R →+* S) :
    Sheaf J (ModuleCat.{u + 1} R) ⥤ Sheaf J (ModuleCat.{u + 1} S) :=
  Sheaf.composeAndSheafify J (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ)

/-- Helper of the retained scalar adjunction, relocated with its existing proof.
Source: Stacks 07A6 (blueprint: def-weil-pbc-constant-coefficient-scalar-extension). -/
noncomputable def pbcFixedScalarSheafAdjunction {R S : Type (u + 1)}
    [CommRing R] [CommRing S] (φ : R →+* S) :
    pbcFixedScalarSheafExtension J φ ⊣ Sheaf.restrictScalars J φ :=
  Sheaf.adjunction J (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ)

/-- Helper of the retained scalar adjunction, relocated with its existing proof.
Source: Stacks 07A6 (blueprint: def-weil-pbc-constant-coefficient-scalar-extension). -/
theorem pbcFixedScalarRestriction_preservesFiniteLimits {R S : Type (u + 1)}
    [CommRing R] [CommRing S] (φ : R →+* S) :
    PreservesFiniteLimits (Sheaf.restrictScalars J φ) := by
  have : PreservesLimitsOfSize.{0, 0} (Sheaf.restrictScalars J φ) :=
    (pbcFixedScalarSheafAdjunction J φ).rightAdjoint_preservesLimits
  infer_instance

attribute [local instance] pbcFixedScalarRestriction_preservesFiniteLimits

omit [EssentiallySmall.{u + 1} C] in
/-- Helper of the retained scalar adjunction, relocated with its existing proof.
Source: Stacks 07A6 (blueprint: def-weil-pbc-constant-coefficient-scalar-extension). -/
theorem pbcFixedScalarRestriction_preservesFiniteColimits {R S : Type (u + 1)}
    [CommRing R] [CommRing S] (φ : R →+* S) :
    PreservesFiniteColimits (Sheaf.restrictScalars J φ) := by
  have : PreservesColimitsOfSize.{0, 0} (Sheaf.restrictScalars J φ) :=
    (Sheaf.restrictCoextendScalarsAdj J φ).leftAdjoint_preservesColimits
  infer_instance

attribute [local instance] pbcFixedScalarRestriction_preservesFiniteColimits

/-- Helper of the retained scalar adjunction, relocated with its existing proof.
Source: Stacks 07A6 (blueprint: def-weil-pbc-constant-coefficient-scalar-extension). -/
theorem pbcFixedScalarSheafExtension_additive {R S : Type (u + 1)}
    [CommRing R] [CommRing S] (φ : R →+* S) : (pbcFixedScalarSheafExtension J φ).Additive :=
  (pbcFixedScalarSheafAdjunction J φ).left_adjoint_additive

attribute [local instance] pbcFixedScalarSheafExtension_additive

/-- Helper of the retained scalar adjunction, relocated with its existing proof.
Source: Stacks 07A6 (blueprint: def-weil-pbc-constant-coefficient-scalar-extension). -/
theorem pbcFixedScalarSheafExtension_preservesKFlat {R S : Type (u + 1)}
    [CommRing R] [CommRing S] (φ : R →+* S) :
    (pbcFixedScalarSheafExtension J φ).PreservesKFlatQuasiIso := by
  classical
  let E := pbcFixedScalarSheafExtension J φ
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

attribute [local instance] pbcFixedScalarSheafExtension_preservesKFlat

/-- Actual exact derived restriction admits its retained scalar left adjoint.
Source: Stacks 07A6 (blueprint: def-weil-pbc-constant-coefficient-scalar-extension).
Proof: the previously proved K-flat preservation for sheafified scalar extension
allows its ordinary adjunction to descend; exactness identifies the right derived
functor with restriction applied termwise and localized. This is the existing proof
with the unused representative-normalization wrapper removed. -/
@[instance] theorem pbcRestriction_isRightAdjoint {R S : Type (u + 1)}
    [CommRing R] [CommRing S] (φ : R →+* S) :
    (Sheaf.derivedRestrictScalars J φ).IsRightAdjoint := by
  exact ((pbcFixedScalarSheafAdjunction J φ).derivedAdjunction.ofNatIsoRight
    (Sheaf.restrictScalars J φ).rightDerivedFunctorIsoMapDerivedCategory).isRightAdjoint

end AlgebraicGeometry.ProEtale
