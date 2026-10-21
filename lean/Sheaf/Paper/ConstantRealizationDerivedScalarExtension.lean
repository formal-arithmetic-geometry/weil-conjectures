/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q73
-/
module

public import Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Homology.PreservesTotalTensorKFlatQuasiIso
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all Sheaf.RingTheory.DerivedModuleScalarAdjunction
import all Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor
import all Sheaf.CategoryTheory.DerivedExactSquareComposition
import Sheaf.CategoryTheory.ConstantModuleFlat
import Sheaf.CategoryTheory.ConstantModuleKFlat
import Sheaf.CategoryTheory.ExactRightDerivedAdjointKFlatRepresentative
import WeilConjectures.Algebra.Homology.ExtensionKFlatQuasiIso
import Mathlib.Algebra.Category.ModuleCat.AB
import all Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
/-!
# Derived constant realization and scalar extension

Source: Stacks Project, Cohomology on Sites, Tags 0G7E and 0D6D; Modules on Sites,
Tags 093J, 0GMW and 03CY (blueprint: lem-sfb-constant-realization-derived-scalar-extension).
Scalar extension is the left adjoint to actual restriction; its universal property
fixes the construction up to the unique unit-preserving isomorphism. The comparison
below is its mate, not a choice of an unspecified natural isomorphism.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 512

universe u v wR wS wT dR dS dT r
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped ChangeOfRings

namespace CategoryTheory.ConstantScalarRealization

-- Chosen left adjoints are used through their adjunction, without reducing the choice.
attribute [local irreducible] Functor.leftAdjoint

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable {R S : Type (max u v)} [CommRing R] [CommRing S] (q : R →+* S)

/-- Actual restriction along the constant coefficient map.
Source: Stacks 03DA (blueprint: lem-sfb-constant-realization-derived-scalar-extension). -/
def restriction : realizationModules J S ⥤ realizationModules J R :=
  SheafOfModules.restrictScalars ((sheafCompose J
    (forget₂ CommRingCat.{max u v} RingCat.{max u v})).map
      ((constantSheaf J CommRingCat.{max u v}).map (CommRingCat.ofHom q)))

/-- Actual restriction is additive.
Source: Stacks 03DA (blueprint: lem-sfb-constant-realization-derived-scalar-extension). -/
instance restriction_additive : (restriction J q).Additive := by
  unfold restriction
  infer_instance

/-- Restriction is exact and has the ordinary sheafified tensor as left adjoint.
Source: Stacks 03DA and 07A6
(blueprint: lem-sfb-constant-realization-derived-scalar-extension).
Proof: restriction retains the underlying abelian sheaf, so kernels and sheafified
cokernels are unchanged. Its left adjoint is sectionwise scalar tensor followed by
module sheafification; the tensor and sheafification universal properties give the
adjunction. This is the identity-site specialization of derived change of rings. -/
theorem restriction_properties :
    PreservesFiniteLimits (restriction J q) ∧
      PreservesFiniteColimits (restriction J q) ∧ (restriction J q).IsRightAdjoint := by
  let φ := (constantSheaf J CommRingCat.{max u v}).map (CommRingCat.ofHom q)
  have : PreservesFiniteLimits (restriction J q ⋙ SheafOfModules.toSheaf _) :=
    inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj (realizationRing J S))))
  have : PreservesFiniteColimits (restriction J q ⋙ SheafOfModules.toSheaf _) :=
    inferInstanceAs (PreservesFiniteColimits (SheafOfModules.toSheaf
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj (realizationRing J S))))
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves _ (SheafOfModules.toSheaf _),
    preservesFiniteColimits_of_reflects_of_preserves _ (SheafOfModules.toSheaf _),
    (SheafOfModules.CoefficientOrdinaryProof.tensorAdjunction φ).isRightAdjoint⟩

/-- Exactness of actual restriction.
Source: Stacks 03DA (blueprint: lem-sfb-constant-realization-derived-scalar-extension). -/
instance restriction_limits : PreservesFiniteLimits (restriction J q) :=
  (restriction_properties J q).1

/-- Exactness of actual restriction.
Source: Stacks 03DA (blueprint: lem-sfb-constant-realization-derived-scalar-extension). -/
instance restriction_colimits : PreservesFiniteColimits (restriction J q) :=
  (restriction_properties J q).2.1

/-- The ordinary scalar adjunction exists by its tensor universal property.
Source: Stacks 03DA (blueprint: lem-sfb-constant-realization-derived-scalar-extension). -/
instance restriction_rightAdjoint : (restriction J q).IsRightAdjoint :=
  (restriction_properties J q).2.2

/-- Actual ordinary extension, determined by the tensor universal property.
Source: Stacks 03DA (blueprint: lem-sfb-constant-realization-derived-scalar-extension). -/
abbrev extension := (restriction J q).leftAdjoint

/-- The scalar tensor/restriction adjunction.
Source: Stacks 03DA (blueprint: lem-sfb-constant-realization-derived-scalar-extension). -/
def adjunction : extension J q ⊣ restriction J q := Adjunction.ofIsRightAdjoint _

/-- Tensor extension is additive since restriction is additive.
Source: Stacks 03DA (blueprint: lem-sfb-constant-realization-derived-scalar-extension). -/
instance extension_additive : (extension J q).Additive :=
  (adjunction J q).left_adjoint_additive

/-- Additivity of ordinary module scalar extension.
Source: Stacks 03DA (blueprint: lem-sfb-constant-realization-derived-scalar-extension). -/
instance moduleExtension_additive {A B : Type r} [CommRing A] [CommRing B] (f : A →+* B) :
    (ModuleCat.extendScalars.{r, r, r} f).Additive :=
  (ModuleCat.extendRestrictScalarsAdj f).left_adjoint_additive

/-- A constant section, from the module-sheafification unit.
Source: Stacks 03CY (blueprint: lem-sfb-constant-realization-derived-scalar-extension). -/
def constantSection (M : ModuleCat.{max u v} R) (V : Cᵒᵖ) (x : M) :
    ((commutativeSiteConstantModuleFunctor J R).obj M).val.obj V :=
  letI := (realizationRingUnit_locallyBijective J R).1
  letI := (realizationRingUnit_locallyBijective J R).2
  (((PresheafOfModules.sheafificationAdjunction (realizationRingUnit J R)).unit.app
    ((siteConstantModulePresheafGeneral (C := C) R).obj M)).app V) x

private theorem constantSection_eq (M : ModuleCat.{max u v} R) (V : Cᵒᵖ) (x : M) :
    constantSection J M V x =
      (toSheafify J ((siteConstantModulePresheafGeneral (C := C) R).obj M).presheaf).app V x := by
  let := (realizationRingUnit_locallyBijective J R).1
  let := (realizationRingUnit_locallyBijective J R).2
  exact ConcreteCategory.congr_hom
    (congr_app (PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app
      (realizationRingUnit J R) ((siteConstantModulePresheafGeneral (C := C) R).obj M)) V) x

private theorem realizationRingUnit_naturality (V : Cᵒᵖ) (a : R) :
    (((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).map
      ((constantSheaf J CommRingCat.{max u v}).map (CommRingCat.ofHom q))).hom.app V)
        ((realizationRingUnit J R).app V a) =
      (realizationRingUnit J S).app V (q a) := by
  have h := toSheafify_naturality (D := CommRingCat.{max u v}) J
    ((Functor.const Cᵒᵖ).map (CommRingCat.ofHom q))
  exact (ConcreteCategory.congr_hom (congr_app h V) a).symm

private def restrictionSeed (M : ModuleCat.{max u v} S) :
    (siteConstantModulePresheafGeneral (C := C) R).obj
        ((ModuleCat.restrictScalars q).obj M) ⟶
      (PresheafOfModules.restrictScalars (realizationRingUnit J R)).obj
        ((restriction J q).obj ((commutativeSiteConstantModuleFunctor J S).obj M)).val := by
  let := (realizationRingUnit_locallyBijective J S).1
  let := (realizationRingUnit_locallyBijective J S).2
  let P := (siteConstantModulePresheafGeneral (C := C) S).obj M
  let τ := PresheafOfModules.toSheafify (realizationRingUnit J S)
    (toSheafify J P.presheaf)
  refine PresheafOfModules.homMk (toSheafify J P.presheaf) ?_
  intro V a x
  refine ((τ.app V).hom.map_smul (q a) x).trans ?_
  exact congrArg
    (fun t : (realizationRing J S).obj.obj V ↦
      t • (show ((commutativeSiteConstantModuleFunctor J S).obj M).val.obj V
        from τ.app V x))
    (realizationRingUnit_naturality J q V a).symm

private theorem restrictionSeed_toPresheaf (M : ModuleCat.{max u v} S) :
    (PresheafOfModules.toPresheaf _).map (restrictionSeed J q M) =
      toSheafify J ((siteConstantModulePresheafGeneral (C := C) R).obj
        ((ModuleCat.restrictScalars q).obj M)).presheaf := by
  ext V x
  rfl

attribute [local irreducible] restrictionSeed


private def restrictionComparison (M : ModuleCat.{max u v} S) :
    (commutativeSiteConstantModuleFunctor J R).obj ((ModuleCat.restrictScalars q).obj M) ⟶
      (restriction J q).obj ((commutativeSiteConstantModuleFunctor J S).obj M) :=
  letI := (realizationRingUnit_locallyBijective J R).1
  letI := (realizationRingUnit_locallyBijective J R).2
  (PresheafOfModules.sheafificationHomEquiv (realizationRingUnit J R)).symm
    (restrictionSeed J q M)

attribute [local irreducible] restrictionComparison

private theorem restrictionComparison_transpose (M : ModuleCat.{max u v} S) :
    letI := (realizationRingUnit_locallyBijective J R).1
    letI := (realizationRingUnit_locallyBijective J R).2
    (PresheafOfModules.sheafificationHomEquiv (realizationRingUnit J R))
      (restrictionComparison J q M) = restrictionSeed J q M := by
  unfold restrictionComparison
  exact Equiv.apply_symm_apply _ _

private theorem restrictionComparison_fac (M : ModuleCat.{max u v} S) :
    toSheafify J ((siteConstantModulePresheafGeneral (C := C) R).obj
        ((ModuleCat.restrictScalars q).obj M)).presheaf ≫
      ((SheafOfModules.toSheaf _).map (restrictionComparison J q M)).hom =
        (PresheafOfModules.toPresheaf _).map (restrictionSeed J q M) := by
  let := (realizationRingUnit_locallyBijective J R).1
  let := (realizationRingUnit_locallyBijective J R).2
  change toSheafify J ((siteConstantModulePresheafGeneral (C := C) R).obj
      ((ModuleCat.restrictScalars q).obj M)).presheaf ≫
    (PresheafOfModules.toPresheaf _).map (restrictionComparison J q M).val = _
  rw [← PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def]
  exact congrArg (PresheafOfModules.toPresheaf _).map
    (restrictionComparison_transpose J q M)

private theorem isIso_of_local_generators
    {P : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}} {A B : Sheaf J AddCommGrpCat.{max u v}}
    (f : P ⟶ A.obj) [Presheaf.IsLocallyInjective J f]
    [Presheaf.IsLocallySurjective J f]
    (g : P ⟶ B.obj) [Presheaf.IsLocallyInjective J g]
    [Presheaf.IsLocallySurjective J g] (h : A ⟶ B) (fac : f ≫ h.hom = g) :
    IsIso h := by
  apply (Sheaf.isLocallyBijective_iff_isIso h).mp
  have hi : Presheaf.IsLocallyInjective J (f ≫ h.hom) := by
    rw [fac]
    infer_instance
  have hs : Presheaf.IsLocallySurjective J (f ≫ h.hom) := by
    rw [fac]
    infer_instance
  exact ⟨(Presheaf.comp_isLocallyInjective_iff J f h.hom).mp hi,
    (Presheaf.comp_isLocallySurjective_iff J f h.hom).mp hs⟩

private theorem restrictionComparison_isIso (M : ModuleCat.{max u v} S) :
    IsIso (restrictionComparison J q M) := by
  let P := (siteConstantModulePresheafGeneral (C := C) R).obj
    ((ModuleCat.restrictScalars q).obj M)
  have hi : Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf _).map (restrictionSeed J q M)) := by
    rw [restrictionSeed_toPresheaf]
    exact (J.W_toSheafify _).isLocallyInjective
  have hs : Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf _).map (restrictionSeed J q M)) := by
    rw [restrictionSeed_toPresheaf]
    exact (J.W_toSheafify _).isLocallySurjective
  let := hi
  let := hs
  have : IsIso ((SheafOfModules.toSheaf _).map (restrictionComparison J q M)) :=
    isIso_of_local_generators J (toSheafify J P.presheaf)
      ((PresheafOfModules.toPresheaf _).map (restrictionSeed J q M))
      ((SheafOfModules.toSheaf _).map (restrictionComparison J q M))
      (restrictionComparison_fac J q M)
  exact isIso_of_reflects_iso (restrictionComparison J q M) (SheafOfModules.toSheaf _)

private theorem constantSection_naturality {M N : ModuleCat.{max u v} R}
    (f : M ⟶ N) (V : Cᵒᵖ) (x : M) :
    ((commutativeSiteConstantModuleFunctor J R).map f).val.app V
      (constantSection J M V x) = constantSection J N V (f x) := by
  let := (realizationRingUnit_locallyBijective J R).1
  let := (realizationRingUnit_locallyBijective J R).2
  have h := (PresheafOfModules.sheafificationAdjunction
    (realizationRingUnit J R)).unit.naturality
      ((siteConstantModulePresheafGeneral (C := C) R).map f)
  exact (congrArg (fun t ↦ t.app V x) h).symm

private theorem constantSection_ext {M : ModuleCat.{max u v} R}
    {N : realizationModules J R}
    {f g : (commutativeSiteConstantModuleFunctor J R).obj M ⟶ N}
    (h : ∀ (V : Cᵒᵖ) (x : M),
      f.val.app V (constantSection J M V x) = g.val.app V (constantSection J M V x)) :
    f = g := by
  let := (realizationRingUnit_locallyBijective J R).1
  let := (realizationRingUnit_locallyBijective J R).2
  apply (PresheafOfModules.sheafificationHomEquiv (realizationRingUnit J R)).injective
  ext V x
  exact h V x

private theorem restrictionComparison_constantSection (M : ModuleCat.{max u v} S)
    (V : Cᵒᵖ) (x : M) :
    (restrictionComparison J q M).val.app V
        (constantSection J ((ModuleCat.restrictScalars q).obj M) V x) =
      constantSection J M V x := by
  have h := ConcreteCategory.congr_hom
    (congr_app (restrictionComparison_fac J q M) V) x
  change (restrictionComparison J q M).val.app V
      ((toSheafify J ((siteConstantModulePresheafGeneral (C := C) R).obj
        ((ModuleCat.restrictScalars q).obj M)).presheaf).app V x) =
      (restrictionSeed J q M).app V x at h
  rw [constantSection_eq, constantSection_eq]
  exact h.trans (by unfold restrictionSeed; rfl)

/-- Restricting constant realization commutes canonically with restricting modules.
The equation fixes the comparison on constant presheaf sections.
Source: Stacks 03CY (blueprint: lem-sfb-constant-realization-derived-scalar-extension).
Proof: the two sheafifications have the same underlying abelian sheaf and the same
restricted R-action on constant sections. The universal property of sheafification
extends the identity to a unique linear isomorphism; the same uniqueness gives
naturality in M. Constant sections locally generate, so the equation gives uniqueness. -/
theorem restrictionIso_existsUnique :
    ∃! e : commutativeSiteConstantModuleFunctor J S ⋙ restriction J q ≅
        ModuleCat.restrictScalars q ⋙ commutativeSiteConstantModuleFunctor J R,
      ∀ (M : ModuleCat.{max u v} S) (V : Cᵒᵖ) (x : M),
        (e.hom.app M).val.app V (constantSection J M V x) =
          constantSection J ((ModuleCat.restrictScalars q).obj M) V x := by
  have hIso (M : ModuleCat.{max u v} S) : IsIso (restrictionComparison J q M) :=
    restrictionComparison_isIso J q M
  let e : ModuleCat.restrictScalars q ⋙ commutativeSiteConstantModuleFunctor J R ≅
      commutativeSiteConstantModuleFunctor J S ⋙ restriction J q :=
    NatIso.ofComponents (fun M ↦ asIso (restrictionComparison J q M)) (by
      intro M N f
      apply constantSection_ext J
      intro V x
      change (restrictionComparison J q N).val.app V
          (((commutativeSiteConstantModuleFunctor J R).map
            ((ModuleCat.restrictScalars q).map f)).val.app V
              (constantSection J ((ModuleCat.restrictScalars q).obj M) V x)) =
        ((commutativeSiteConstantModuleFunctor J S).map f).val.app V
          ((restrictionComparison J q M).val.app V
            (constantSection J ((ModuleCat.restrictScalars q).obj M) V x))
      rw [constantSection_naturality, restrictionComparison_constantSection,
        restrictionComparison_constantSection, constantSection_naturality]
      rfl)
  have he (M : ModuleCat.{max u v} S) (V : Cᵒᵖ) (x : M) :
      (e.inv.app M).val.app V (constantSection J M V x) =
        constantSection J ((ModuleCat.restrictScalars q).obj M) V x := by
    rw [← restrictionComparison_constantSection J q M V x]
    exact congrArg (fun t ↦ t.val.app V
      (constantSection J ((ModuleCat.restrictScalars q).obj M) V x)) (e.hom_inv_id_app M)
  refine ⟨e.symm, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply (cancel_epi (e.hom.app M)).mp
  change restrictionComparison J q M ≫ e'.hom.app M =
    restrictionComparison J q M ≫ e.inv.app M
  apply constantSection_ext J
  intro V x
  change (e'.hom.app M).val.app V
      ((restrictionComparison J q M).val.app V
        (constantSection J ((ModuleCat.restrictScalars q).obj M) V x)) =
    (e.inv.app M).val.app V
      ((restrictionComparison J q M).val.app V
        (constantSection J ((ModuleCat.restrictScalars q).obj M) V x))
  rw [restrictionComparison_constantSection, he', he]

/-- The identity-on-constant-sections restriction comparison.
Source: Stacks 03CY (blueprint: lem-sfb-constant-realization-derived-scalar-extension). -/
def restrictionIso :
    commutativeSiteConstantModuleFunctor J S ⋙ restriction J q ≅
      ModuleCat.restrictScalars q ⋙ commutativeSiteConstantModuleFunctor J R :=
  Classical.choose (restrictionIso_existsUnique J q)


/-- The ordinary comparison, defined by the scalar adjunction mate.
Source: Stacks 0GMW (blueprint: lem-sfb-constant-realization-derived-scalar-extension). -/
def moduleComparison (M : ModuleCat.{max u v} R) :
    (extension J q).obj ((commutativeSiteConstantModuleFunctor J R).obj M) ⟶
      (commutativeSiteConstantModuleFunctor J S).obj ((ModuleCat.extendScalars q).obj M) :=
  ((adjunction J q).homEquiv _ _).symm
    ((commutativeSiteConstantModuleFunctor J R).map
      ((ModuleCat.extendRestrictScalarsAdj q).unit.app M) ≫
        (restrictionIso J q).inv.app ((ModuleCat.extendScalars q).obj M))

/-- Naturality of the ordinary mate.
Source: Stacks 0GMW (blueprint: lem-sfb-constant-realization-derived-scalar-extension).
Proof: transpose both sides; naturality of the ordinary unit and of restrictionIso
identifies their transposes, and the adjunction Hom equivalence is injective. -/
theorem moduleComparison_naturality {M N : ModuleCat.{max u v} R} (f : M ⟶ N) :
    (extension J q).map ((commutativeSiteConstantModuleFunctor J R).map f) ≫
        moduleComparison J q N =
      moduleComparison J q M ≫
        (commutativeSiteConstantModuleFunctor J S).map ((ModuleCat.extendScalars q).map f) := by
  apply ((adjunction J q).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left]
  rw [Adjunction.homEquiv_naturality_right]
  simp only [moduleComparison, Equiv.apply_symm_apply]
  rw [← Category.assoc]
  rw [← (commutativeSiteConstantModuleFunctor J R).map_comp]
  rw [← (ModuleCat.extendRestrictScalarsAdj q).unit_naturality]
  rw [Functor.map_comp]
  simp only [Category.assoc]
  congr 1
  exact (restrictionIso J q).inv.naturality ((ModuleCat.extendScalars q).map f)

private theorem constantSection_smul (M : ModuleCat.{max u v} R)
    (V : Cᵒᵖ) (a : R) (x : M) :
    constantSection J M V (a • x) =
      (realizationRingUnit J R).app V a • constantSection J M V x := by
  let := (realizationRingUnit_locallyBijective J R).1
  let := (realizationRingUnit_locallyBijective J R).2
  exact (((PresheafOfModules.sheafificationAdjunction (realizationRingUnit J R)).unit.app
    ((siteConstantModulePresheafGeneral (C := C) R).obj M)).app V).hom.map_smul a x

private theorem constantSection_add (M : ModuleCat.{max u v} R)
    (V : Cᵒᵖ) (x y : M) :
    constantSection J M V (x + y) = constantSection J M V x + constantSection J M V y := by
  let := (realizationRingUnit_locallyBijective J R).1
  let := (realizationRingUnit_locallyBijective J R).2
  exact (((PresheafOfModules.sheafificationAdjunction (realizationRingUnit J R)).unit.app
    ((siteConstantModulePresheafGeneral (C := C) R).obj M)).app V).hom.map_add x y

private theorem constantSection_map (M : ModuleCat.{max u v} R)
    {V W : Cᵒᵖ} (i : V ⟶ W) (x : M) :
    ((commutativeSiteConstantModuleFunctor J R).obj M).val.map i
      (constantSection J M V x) = constantSection J M W x := by
  let := (realizationRingUnit_locallyBijective J R).1
  let := (realizationRingUnit_locallyBijective J R).2
  exact (PresheafOfModules.naturality_apply
    ((PresheafOfModules.sheafificationAdjunction (realizationRingUnit J R)).unit.app
      ((siteConstantModulePresheafGeneral (C := C) R).obj M)) i x).symm

private def transposeGenerator {M : ModuleCat.{max u v} R} {N : realizationModules J S}
    (f : (commutativeSiteConstantModuleFunctor J R).obj M ⟶ (restriction J q).obj N)
    (V : Cᵒᵖ) :
    M ⟶ (ModuleCat.restrictScalars q).obj
      ((ModuleCat.restrictScalars ((realizationRingUnit J S).app V).hom).obj (N.val.obj V)) :=
  ModuleCat.ofHom
    (X := M) (Y := (ModuleCat.restrictScalars q).obj
      ((ModuleCat.restrictScalars ((realizationRingUnit J S).app V).hom).obj (N.val.obj V)))
    { toFun := fun x ↦ f.val.app V (constantSection J M V x)
      map_add' := fun x y ↦ by rw [constantSection_add, map_add]
      map_smul' := fun a x ↦ by
        rw [constantSection_smul, map_smul]
        exact congrArg (fun t : (realizationRing J S).obj.obj V ↦
          t • (show N.val.obj V from f.val.app V (constantSection J M V x)))
          (realizationRingUnit_naturality J q V a) }


private def tensorSection {M : ModuleCat.{max u v} R} {N : realizationModules J S}
    (f : (commutativeSiteConstantModuleFunctor J R).obj M ⟶ (restriction J q).obj N)
    (V : Cᵒᵖ) :
    (ModuleCat.extendScalars q).obj M ⟶
      (ModuleCat.restrictScalars ((realizationRingUnit J S).app V).hom).obj (N.val.obj V) :=
  ((ModuleCat.extendRestrictScalarsAdj q).homEquiv _ _).symm (transposeGenerator J q f V)

private theorem tensorSection_one {M : ModuleCat.{max u v} R} {N : realizationModules J S}
    (f : (commutativeSiteConstantModuleFunctor J R).obj M ⟶ (restriction J q).obj N)
    (V : Cᵒᵖ) (x : M) :
    tensorSection J q f V ((1 : S) ⊗ₜ[R, q] x) =
      f.val.app V (constantSection J M V x) := by
  have h := ((ModuleCat.extendRestrictScalarsAdj q).homEquiv _ _).apply_symm_apply
    (transposeGenerator J q f V)
  have hx := congrArg (fun t ↦ t x) h
  rw [ModuleCat.extendRestrictScalarsAdj_homEquiv_apply] at hx
  exact hx

private def tensorLiftPresheaf {M : ModuleCat.{max u v} R} {N : realizationModules J S}
    (f : (commutativeSiteConstantModuleFunctor J R).obj M ⟶ (restriction J q).obj N) :
    (siteConstantModulePresheafGeneral (C := C) S).obj ((ModuleCat.extendScalars q).obj M) ⟶
      (PresheafOfModules.restrictScalars (realizationRingUnit J S)).obj N.val where
  app V := tensorSection J q f V
  naturality {V W} i := by
    let T := (PresheafOfModules.restrictScalars (realizationRingUnit J S)).obj N.val
    change tensorSection J q f W = tensorSection J q f V ≫ T.map i
    apply ((ModuleCat.extendRestrictScalarsAdj q).homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_right]
    ext x
    change tensorSection J q f W ((1 : S) ⊗ₜ[R, q] x) =
      T.map i (tensorSection J q f V ((1 : S) ⊗ₜ[R, q] x))
    rw [tensorSection_one, tensorSection_one]
    exact (congrArg (fun t ↦ f.val.app W t) (constantSection_map J M i x)).symm.trans
      (PresheafOfModules.naturality_apply f.val i (constantSection J M V x))

private def tensorLift {M : ModuleCat.{max u v} R} {N : realizationModules J S}
    (f : (commutativeSiteConstantModuleFunctor J R).obj M ⟶ (restriction J q).obj N) :
    (commutativeSiteConstantModuleFunctor J S).obj ((ModuleCat.extendScalars q).obj M) ⟶ N :=
  letI := (realizationRingUnit_locallyBijective J S).1
  letI := (realizationRingUnit_locallyBijective J S).2
  (PresheafOfModules.sheafificationHomEquiv (realizationRingUnit J S)).symm
    (tensorLiftPresheaf J q f)


private theorem tensorLift_constantSection
    {M : ModuleCat.{max u v} R} {N : realizationModules J S}
    (f : (commutativeSiteConstantModuleFunctor J R).obj M ⟶ (restriction J q).obj N)
    (V : Cᵒᵖ) (z : (ModuleCat.extendScalars q).obj M) :
    (tensorLift J q f).val.app V
        (constantSection J ((ModuleCat.extendScalars q).obj M) V z) =
      tensorSection J q f V z := by
  let := (realizationRingUnit_locallyBijective J S).1
  let := (realizationRingUnit_locallyBijective J S).2
  have h := (PresheafOfModules.sheafificationHomEquiv
    (realizationRingUnit J S)).apply_symm_apply (tensorLiftPresheaf J q f)
  exact congrArg (fun t ↦ t.app V z) h

private theorem restrictionIso_inv_constantSection (M : ModuleCat.{max u v} S)
    (V : Cᵒᵖ) (x : M) :
    ((restrictionIso J q).inv.app M).val.app V
        (constantSection J ((ModuleCat.restrictScalars q).obj M) V x) =
      constantSection J M V x := by
  have h := (Classical.choose_spec (restrictionIso_existsUnique J q)).1 M V x
  change ((restrictionIso J q).hom.app M).val.app V (constantSection J M V x) = _ at h
  rw [← h]
  exact congrArg (fun t ↦ t.val.app V (constantSection J M V x))
    ((restrictionIso J q).hom_inv_id_app M)

private theorem moduleComparison_unit_section (M : ModuleCat.{max u v} R)
    (V : Cᵒᵖ) (x : M) :
    (moduleComparison J q M).val.app V
      (((adjunction J q).unit.app
        ((commutativeSiteConstantModuleFunctor J R).obj M)).val.app V
          (constantSection J M V x)) =
      constantSection J ((ModuleCat.extendScalars q).obj M) V ((1 : S) ⊗ₜ[R, q] x) := by
  have h : (adjunction J q).unit.app
        ((commutativeSiteConstantModuleFunctor J R).obj M) ≫
      (restriction J q).map (moduleComparison J q M) =
    (commutativeSiteConstantModuleFunctor J R).map
      ((ModuleCat.extendRestrictScalarsAdj q).unit.app M) ≫
      (restrictionIso J q).inv.app ((ModuleCat.extendScalars q).obj M) := by
    exact ((adjunction J q).homEquiv_unit _ _ (moduleComparison J q M)).symm.trans
      (Equiv.apply_symm_apply _ _)
  have hx := congrArg (fun t ↦ t.val.app V (constantSection J M V x)) h
  change (moduleComparison J q M).val.app V
      (((adjunction J q).unit.app
        ((commutativeSiteConstantModuleFunctor J R).obj M)).val.app V
          (constantSection J M V x)) =
    ((restrictionIso J q).inv.app ((ModuleCat.extendScalars q).obj M)).val.app V
      (((commutativeSiteConstantModuleFunctor J R).map
        ((ModuleCat.extendRestrictScalarsAdj q).unit.app M)).val.app V
          (constantSection J M V x)) at hx
  refine hx.trans ?_
  refine (congrArg
    (fun z ↦ ((restrictionIso J q).inv.app ((ModuleCat.extendScalars q).obj M)).val.app V z)
    (constantSection_naturality J
      ((ModuleCat.extendRestrictScalarsAdj q).unit.app M) V x)).trans ?_
  exact (restrictionIso_inv_constantSection J q ((ModuleCat.extendScalars q).obj M) V
    (((ModuleCat.extendRestrictScalarsAdj q).unit.app M) x)).trans
      (congrArg (constantSection J ((ModuleCat.extendScalars q).obj M) V)
        (ModuleCat.extendRestrictScalarsAdj_unit_app_apply q M x))


private theorem tensorSection_tmul {M : ModuleCat.{max u v} R} {N : realizationModules J S}
    (f : (commutativeSiteConstantModuleFunctor J R).obj M ⟶ (restriction J q).obj N)
    (V : Cᵒᵖ) (x : M) (s : S) :
    tensorSection J q f V (s ⊗ₜ[R, q] x) =
      (realizationRingUnit J S).app V s •
        (show N.val.obj V from f.val.app V (constantSection J M V x)) := by
  have ht : s ⊗ₜ[R, q] x = s • ((1 : S) ⊗ₜ[R, q] x :
      (ModuleCat.extendScalars q).obj M) := by
    rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]
  rw [ht, map_smul, tensorSection_one]
  rfl

private theorem moduleComparison_formula (M : ModuleCat.{max u v} R)
    (V : Cᵒᵖ) (x : M) (s : S) :
    (moduleComparison J q M).val.app V
      ((realizationRingUnit J S).app V s •
        (show ((extension J q).obj
          ((commutativeSiteConstantModuleFunctor J R).obj M)).val.obj V from
          ((adjunction J q).unit.app
            ((commutativeSiteConstantModuleFunctor J R).obj M)).val.app V
              (constantSection J M V x))) =
      constantSection J ((ModuleCat.extendScalars q).obj M) V (s ⊗ₜ[R, q] x) := by
  rw [map_smul, moduleComparison_unit_section]
  have h := constantSection_smul J ((ModuleCat.extendScalars q).obj M) V s
    ((1 : S) ⊗ₜ[R, q] x)
  rw [ModuleCat.ExtendScalars.smul_tmul, mul_one] at h
  exact h.symm

private theorem constantSection_zero (M : ModuleCat.{max u v} R) (V : Cᵒᵖ) :
    constantSection J M V 0 = 0 := by
  let := (realizationRingUnit_locallyBijective J R).1
  let := (realizationRingUnit_locallyBijective J R).2
  exact (((PresheafOfModules.sheafificationAdjunction (realizationRingUnit J R)).unit.app
    ((siteConstantModulePresheafGeneral (C := C) R).obj M)).app V).hom.map_zero

private theorem moduleComparison_isIso (M : ModuleCat.{max u v} R) :
    IsIso (moduleComparison J q M) := by
  let X := (commutativeSiteConstantModuleFunctor J R).obj M
  let η := (adjunction J q).unit.app X
  let g := tensorLift J q η
  have h₁ : moduleComparison J q M ≫ g = 𝟙 _ := by
    apply ((adjunction J q).homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    simp only [Functor.map_id]
    apply constantSection_ext J
    intro V x
    change g.val.app V ((moduleComparison J q M).val.app V
      (η.val.app V (constantSection J M V x))) = η.val.app V (constantSection J M V x)
    rw [moduleComparison_unit_section, tensorLift_constantSection, tensorSection_one]
    rfl
  have h₂ : g ≫ moduleComparison J q M = 𝟙 _ := by
    apply constantSection_ext J
    intro V z
    change (moduleComparison J q M).val.app V
      (g.val.app V (constantSection J ((ModuleCat.extendScalars q).obj M) V z)) =
        constantSection J ((ModuleCat.extendScalars q).obj M) V z
    induction z using TensorProduct.induction_on with
    | zero => rw [constantSection_zero, map_zero, map_zero]
    | tmul s x =>
      rw [tensorLift_constantSection, tensorSection_tmul]
      exact moduleComparison_formula J q M V x s
    | add z w hz hw => rw [constantSection_add, map_add, map_add, hz, hw]
  exact ⟨⟨g, h₁, h₂⟩⟩


/-- The ordinary comparison is an isomorphism, with the identity-on-tensors formula.
Scalar-first tensors in Lean are the paper's m tensor s with factors interchanged.
Source: Stacks 0GMW and 03CY
(blueprint: lem-sfb-constant-realization-derived-scalar-extension).
Proof: sheafify the identity of constant presheaves with value S tensor_R M.
The tensor and sheafification universal properties identify its map with the mate
moduleComparison. The inverse is induced by the same pure tensors, so both composites
are identities. The displayed equation is the value on each constant generator. -/
theorem moduleComparison_tensor (M : ModuleCat.{max u v} R) :
    IsIso (moduleComparison J q M) ∧
      ∀ (V : Cᵒᵖ) (x : M) (s : S),
        (moduleComparison J q M).val.app V
          (((realizationRingUnit J S).app V s) •
            (@id (((extension J q).obj
                ((commutativeSiteConstantModuleFunctor J R).obj M)).val.obj V)
              (((adjunction J q).unit.app
                ((commutativeSiteConstantModuleFunctor J R).obj M)).val.app V
                  (constantSection J M V x)))) =
          constantSection J ((ModuleCat.extendScalars q).obj M) V
            (s ⊗ₜ[R, q] x) := by
  exact ⟨moduleComparison_isIso J q M, moduleComparison_formula J q M⟩

/-- The genuine chain map of termwise constant tensor comparisons.
Source: Stacks 0GMW (blueprint: lem-sfb-constant-realization-derived-scalar-extension). -/
def complexComparison (P : CochainComplex (ModuleCat.{max u v} R) ℤ) :
    ((extension J q).mapHomologicalComplex (.up ℤ)).obj
        (((commutativeSiteConstantModuleFunctor J R).mapHomologicalComplex (.up ℤ)).obj P) ⟶
      ((commutativeSiteConstantModuleFunctor J S).mapHomologicalComplex (.up ℤ)).obj
        (((ModuleCat.extendScalars q).mapHomologicalComplex (.up ℤ)).obj P) where
  f n := moduleComparison J q (P.X n)
  comm' i j _ := (moduleComparison_naturality J q (P.d i j)).symm

section SheafDerivedExistence

variable [HasDerivedCategory.{dR} (realizationModules J R)]
  [HasDerivedCategory.{dS} (realizationModules J S)]

/-- Exact derived restriction of module sheaves.
Source: Stacks 07A6 (blueprint: lem-sfb-constant-realization-derived-scalar-extension). -/
abbrev derivedRestriction := (restriction J q).mapDerivedCategory

/-- Unbounded scalar extension is left adjoint to exact restriction on module sheaves.
Source: Stacks 06YY and 07A6
(blueprint: lem-sfb-constant-realization-derived-scalar-extension).
Proof: derived change of rings supplies an everywhere defined left derived tensor
functor computed by K-flat resolutions. The derived adjunction theorem identifies
its right adjoint with exact restriction. Transport along the canonical equivalences
of localization universes gives the independently sized source and target. -/
theorem derivedRestriction_isRightAdjoint :
    (derivedRestriction.{u, v, dR, dS} J q).IsRightAdjoint := by
  let Ft := derivedRestriction.{u, v, dR, dS} J q
  let QAR := @DerivedCategory.Q (realizationModules J R) _ _
    (inferInstance : HasDerivedCategory.{dR} (realizationModules J R))
  let QBS := @DerivedCategory.Q (realizationModules J S) _ _
    (inferInstance : HasDerivedCategory.{dS} (realizationModules J S))
  let hA := HasDerivedCategory.standard (realizationModules J R)
  let hB := HasDerivedCategory.standard (realizationModules J S)
  let := hA
  let := hB
  let QA := @DerivedCategory.Q _ _ _ hA
  let QB := @DerivedCategory.Q _ _ _ hB
  let WA := HomologicalComplex.quasiIso (realizationModules J R) (.up ℤ)
  let WB := HomologicalComplex.quasiIso (realizationModules J S) (.up ℤ)
  let eA := Localization.uniq QA (QAR) WA
  let eB := Localization.uniq QB (QBS) WB
  let F := @Functor.mapDerivedCategory _ _ _ hB _ _ _ hA
    (restriction J q) _ _ _
  have : F.IsRightAdjoint := by
    let φ := (constantSheaf J CommRingCat.{max u v}).map (CommRingCat.ofHom q)
    obtain ⟨_, _, h⟩ := SheafOfModules.sheafRingDerivedCoefficientAdjunction φ
    obtain ⟨E, hobj, hmap, hadd, _, _, LF, ε, hLF, _⟩ :=
      SheafOfModules.derivedChangeOfRingsIndependentCoefficients φ
    let := hadd
    obtain ⟨_, _, hd⟩ := h E hobj hmap
    obtain ⟨d, _⟩ := hd LF ε hLF
    exact d.isRightAdjoint
  let G := (eB.inverse ⋙ F) ⋙ eA.functor
  have : G.IsRightAdjoint := inferInstance
  let H := (restriction J q).mapHomologicalComplex (.up ℤ)
  let e : QBS ⋙ G ≅ H ⋙ QAR :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (Localization.compUniqInverse QB
          (QBS) WB) F) eA.functor ≪≫
      Functor.isoWhiskerRight
        (@Functor.mapDerivedCategoryFactors _ _ _ hB _ _ _ hA
          (restriction J q) _ _ _) eA.functor ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft H
        (Localization.compUniqFunctor QA (QAR) WA)
  let : Localization.Lifting QBS WB
      (H ⋙ QAR) G := ⟨e⟩
  let i : Ft ≅ G :=
    Localization.liftNatIso QBS WB (H ⋙ QAR) (H ⋙ QAR) Ft G (Iso.refl _)
  exact Functor.isRightAdjoint_of_iso i.symm

/-- The sheaf scalar adjunction instance, supplied by the named existence theorem.
Source: Stacks 07A6 (blueprint: lem-sfb-constant-realization-derived-scalar-extension). -/
instance derivedRestriction_rightAdjoint :
    (derivedRestriction.{u, v, dR, dS} J q).IsRightAdjoint :=
  derivedRestriction_isRightAdjoint J q

end SheafDerivedExistence

section Derived

variable [HasDerivedCategory.{wR} (ModuleCat.{max u v} R)]
  [HasDerivedCategory.{wS} (ModuleCat.{max u v} S)]
  [HasDerivedCategory.{dR} (realizationModules J R)]
  [HasDerivedCategory.{dS} (realizationModules J S)]

/-- Exact derived restriction of ordinary modules at independent localization sizes.
Source: Stacks 07A6 (blueprint: lem-sfb-constant-realization-derived-scalar-extension). -/
abbrev moduleDerivedRestriction {A B : Type r} [CommRing A] [CommRing B] (f : A →+* B)
    [HasDerivedCategory.{wR} (ModuleCat.{r} A)]
    [HasDerivedCategory.{wS} (ModuleCat.{r} B)] :=
  (ModuleCat.restrictScalars.{r} f).mapDerivedCategory

/-- Unbounded scalar extension is left adjoint to exact restriction on modules.
Source: Stacks 06YY and 07A6
(blueprint: lem-sfb-constant-realization-derived-scalar-extension).
Proof: apply derived change of rings on the one-object identity-covering site,
whose module category is ordinary modules. K-flat resolutions compute its everywhere
defined left derived functor. The derived adjunction theorem identifies exact
restriction as its right adjoint, for any independently chosen localization sizes. -/
theorem moduleDerivedRestriction_isRightAdjoint
    {A B : Type r} [CommRing A] [CommRing B] (f : A →+* B)
    [HasDerivedCategory.{wR} (ModuleCat.{r} A)]
    [HasDerivedCategory.{wS} (ModuleCat.{r} B)] :
    (moduleDerivedRestriction.{wR, wS, r} f).IsRightAdjoint := by
  let Ft := moduleDerivedRestriction.{wR, wS, r} f
  let QAR := @DerivedCategory.Q (ModuleCat.{r} A) _ _
    (inferInstance : HasDerivedCategory.{wR} (ModuleCat.{r} A))
  let QBS := @DerivedCategory.Q (ModuleCat.{r} B) _ _
    (inferInstance : HasDerivedCategory.{wS} (ModuleCat.{r} B))
  let hA := HasDerivedCategory.standard (ModuleCat.{r} A)
  let hB := HasDerivedCategory.standard (ModuleCat.{r} B)
  let := hA
  let := hB
  let QA := @DerivedCategory.Q _ _ _ hA
  let QB := @DerivedCategory.Q _ _ _ hB
  let WA := HomologicalComplex.quasiIso (ModuleCat.{r} A) (.up ℤ)
  let WB := HomologicalComplex.quasiIso (ModuleCat.{r} B) (.up ℤ)
  let eA := Localization.uniq QA (QAR) WA
  let eB := Localization.uniq QB (QBS) WB
  let F := @Functor.mapDerivedCategory _ _ _ hB _ _ _ hA
    (ModuleCat.restrictScalars f) _ _ _
  have : F.IsRightAdjoint := ModuleCat.derivedRestrictScalars_isRightAdjoint f
  let G := (eB.inverse ⋙ F) ⋙ eA.functor
  have : G.IsRightAdjoint := inferInstance
  let H := (ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)
  let e : QBS ⋙ G ≅ H ⋙ QAR :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (Localization.compUniqInverse QB
          (QBS) WB) F) eA.functor ≪≫
      Functor.isoWhiskerRight
        (@Functor.mapDerivedCategoryFactors _ _ _ hB _ _ _ hA
          (ModuleCat.restrictScalars f) _ _ _) eA.functor ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft H
        (Localization.compUniqFunctor QA (QAR) WA)
  let : Localization.Lifting QBS WB
      (H ⋙ QAR) G := ⟨e⟩
  let i : Ft ≅ G :=
    Localization.liftNatIso QBS WB (H ⋙ QAR) (H ⋙ QAR) Ft G (Iso.refl _)
  exact Functor.isRightAdjoint_of_iso i.symm

/-- The module scalar adjunction instance, supplied by the named existence theorem.
Source: Stacks 07A6 (blueprint: lem-sfb-constant-realization-derived-scalar-extension). -/
instance moduleDerivedRestriction_rightAdjoint
    {A B : Type r} [CommRing A] [CommRing B] (f : A →+* B)
    [HasDerivedCategory.{wR} (ModuleCat.{r} A)]
    [HasDerivedCategory.{wS} (ModuleCat.{r} B)] :
    (moduleDerivedRestriction.{wR, wS, r} f).IsRightAdjoint :=
  moduleDerivedRestriction_isRightAdjoint f

/-- Derived scalar tensor of ordinary modules, fixed by its adjunction.
Source: Stacks 06YY (blueprint: lem-sfb-constant-realization-derived-scalar-extension). -/
def moduleDerivedExtension {A B : Type r} [CommRing A] [CommRing B] (f : A →+* B)
    [HasDerivedCategory.{wR} (ModuleCat.{r} A)]
    [HasDerivedCategory.{wS} (ModuleCat.{r} B)] :
    DerivedCategory (ModuleCat.{r} A) ⥤ DerivedCategory (ModuleCat.{r} B) :=
  (moduleDerivedRestriction.{wR, wS, r} f).leftAdjoint

/-- Derived scalar tensor of module sheaves, fixed by its adjunction.
Source: Stacks 06YY (blueprint: lem-sfb-constant-realization-derived-scalar-extension). -/
def derivedExtension :
    DerivedCategory (realizationModules J R) ⥤ DerivedCategory (realizationModules J S) :=
  (derivedRestriction.{u, v, dR, dS} J q).leftAdjoint

/-- The unbounded scalar adjunction for ordinary modules.
Source: Stacks 07A6 (blueprint: lem-sfb-constant-realization-derived-scalar-extension). -/
def moduleDerivedAdjunction {A B : Type r} [CommRing A] [CommRing B] (f : A →+* B)
    [HasDerivedCategory.{wR} (ModuleCat.{r} A)]
    [HasDerivedCategory.{wS} (ModuleCat.{r} B)] :
    moduleDerivedExtension.{wR, wS, r} f ⊣ moduleDerivedRestriction.{wR, wS, r} f :=
  Adjunction.ofIsRightAdjoint _

/-- The unbounded scalar adjunction for sheaves.
Source: Stacks 07A6 (blueprint: lem-sfb-constant-realization-derived-scalar-extension). -/
def derivedAdjunction : derivedExtension.{u, v, dR, dS} J q ⊣
    derivedRestriction.{u, v, dR, dS} J q := Adjunction.ofIsRightAdjoint _

/-- Localize the exact ordinary restriction comparison.
Source: Stacks 07A6 (blueprint: lem-sfb-constant-realization-derived-scalar-extension). -/
def derivedRestrictionIso :
    commutativeSiteDerivedConstantModuleFunctor.{u, v, wS, dS} J S ⋙
        derivedRestriction.{u, v, dR, dS} J q ≅
      moduleDerivedRestriction.{wR, wS, max u v} q ⋙
        commutativeSiteDerivedConstantModuleFunctor.{u, v, wR, dR} J R :=
  letI := comp_preservesFiniteLimits
    (commutativeSiteConstantModuleFunctor J S) (restriction J q)
  letI := comp_preservesFiniteColimits
    (commutativeSiteConstantModuleFunctor J S) (restriction J q)
  letI := comp_preservesFiniteLimits
    (ModuleCat.restrictScalars q) (commutativeSiteConstantModuleFunctor J R)
  letI := comp_preservesFiniteColimits
    (ModuleCat.restrictScalars q) (commutativeSiteConstantModuleFunctor J R)
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (restrictionIso J q) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

/-- The comparison map is the mate of the realized scalar-extension unit.
Source: Stacks 0G7E and 07A6
(blueprint: lem-sfb-constant-realization-derived-scalar-extension). -/
def comparison (M : DerivedCategory (ModuleCat.{max u v} R)) :
    (derivedExtension.{u, v, dR, dS} J q).obj
        ((commutativeSiteDerivedConstantModuleFunctor.{u, v, wR, dR} J R).obj M) ⟶
      (commutativeSiteDerivedConstantModuleFunctor.{u, v, wS, dS} J S).obj
        ((moduleDerivedExtension.{wR, wS, max u v} q).obj M) :=
  ((derivedAdjunction.{u, v, dR, dS} J q).homEquiv _ _).symm
    ((commutativeSiteDerivedConstantModuleFunctor.{u, v, wR, dR} J R).map
      ((moduleDerivedAdjunction.{wR, wS, max u v} q).unit.app M) ≫
        (derivedRestrictionIso.{u, v, wR, wS, dR, dS} J q).inv.app
          ((moduleDerivedExtension.{wR, wS, max u v} q).obj M))

/-- Canonical ordinary-module representative map, the transpose of the localized unit.
Source: Stacks 06YY and 07A6
(blueprint: lem-sfb-constant-realization-derived-scalar-extension). -/
def moduleRepresentative {A B : Type r} [CommRing A] [CommRing B] (f : A →+* B)
    [HasDerivedCategory.{wR} (ModuleCat.{r} A)]
    [HasDerivedCategory.{wS} (ModuleCat.{r} B)] (P : CochainComplex (ModuleCat.{r} A) ℤ) :
    (moduleDerivedExtension.{wR, wS, r} f).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj P) :=
  ((moduleDerivedAdjunction.{wR, wS, r} f).homEquiv _ _).symm
    (DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexIdIso _ (.up ℤ)).inv.app P ≫
          (NatTrans.mapHomologicalComplex
            (ModuleCat.extendRestrictScalarsAdj f).unit (.up ℤ)).app P ≫
          (Functor.mapHomologicalComplexCompIso
            (Iso.refl (ModuleCat.extendScalars f ⋙ ModuleCat.restrictScalars f))
              (.up ℤ)).inv.app P) ≫
      (ModuleCat.restrictScalars f).mapDerivedCategoryFactors.inv.app
        (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj P))

/-- Canonical sheaf representative map, the transpose of the localized ordinary unit.
Source: Stacks 06YY and 07A6
(blueprint: lem-sfb-constant-realization-derived-scalar-extension). -/
def sheafRepresentative (P : CochainComplex (realizationModules J R) ℤ) :
    (derivedExtension.{u, v, dR, dS} J q).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj (((extension J q).mapHomologicalComplex (.up ℤ)).obj P) :=
  ((derivedAdjunction.{u, v, dR, dS} J q).homEquiv _ _).symm
    (DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexIdIso _ (.up ℤ)).inv.app P ≫
          (NatTrans.mapHomologicalComplex (adjunction J q).unit (.up ℤ)).app P ≫
          (Functor.mapHomologicalComplexCompIso
            (Iso.refl (extension J q ⋙ restriction J q)) (.up ℤ)).inv.app P) ≫
      (restriction J q).mapDerivedCategoryFactors.inv.app
        (((extension J q).mapHomologicalComplex (.up ℤ)).obj P))

/-- Naturality of the derived mate.
Source: Stacks 0D6D (blueprint: lem-sfb-constant-realization-derived-scalar-extension).
Proof: transpose the two sides using derivedAdjunction. Naturality of the module
unit and derivedRestrictionIso makes them equal; the transpose bijection is injective. -/
theorem comparison_naturality
    {M N : DerivedCategory (ModuleCat.{max u v} R)} (f : M ⟶ N) :
    (derivedExtension.{u, v, dR, dS} J q).map
        ((commutativeSiteDerivedConstantModuleFunctor.{u, v, wR, dR} J R).map f) ≫
        comparison.{u, v, wR, wS, dR, dS} J q N =
      comparison.{u, v, wR, wS, dR, dS} J q M ≫
        (commutativeSiteDerivedConstantModuleFunctor.{u, v, wS, dS} J S).map
          ((moduleDerivedExtension.{wR, wS, max u v} q).map f) := by
  apply ((derivedAdjunction.{u, v, dR, dS} J q).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left]
  rw [Adjunction.homEquiv_naturality_right]
  simp only [comparison, Equiv.apply_symm_apply]
  rw [← Category.assoc, ← Functor.map_comp]
  rw [← (moduleDerivedAdjunction.{wR, wS, max u v} q).unit_naturality]
  rw [Functor.map_comp]
  simp only [Category.assoc]
  congr 1
  exact (derivedRestrictionIso J q).inv.naturality
    ((moduleDerivedExtension.{wR, wS, max u v} q).map f)

/-- The canonical derived comparison as a natural transformation.
Source: Stacks 0D6D (blueprint: lem-sfb-constant-realization-derived-scalar-extension). -/
def comparisonTransformation :
    commutativeSiteDerivedConstantModuleFunctor.{u, v, wR, dR} J R ⋙
        derivedExtension.{u, v, dR, dS} J q ⟶
      moduleDerivedExtension.{wR, wS, max u v} q ⋙
        commutativeSiteDerivedConstantModuleFunctor.{u, v, wS, dS} J S where
  app := comparison.{u, v, wR, wS, dR, dS} J q
  naturality _ _ f := comparison_naturality J q f

-- Keep chosen adjoints abstract while proving their universal-property identities.
attribute [local irreducible] adjunction derivedExtension moduleDerivedExtension
  derivedAdjunction moduleDerivedAdjunction

/-- The scalar-extension unit is compatible with constant realization.
Source: Stacks 0D6D and 07A6 (blueprint: lem-sfb-constant-realization-derived-scalar-extension).
Proof: transpose both sides under the derived adjunction; the two transposes are the
realized ordinary scalar-extension unit followed by the restriction comparison. -/
private theorem comparison_unit :
    (∀ M : DerivedCategory (ModuleCat.{max u v} R),
      (derivedAdjunction.{u, v, dR, dS} J q).unit.app
          ((commutativeSiteDerivedConstantModuleFunctor.{u, v, wR, dR} J R).obj M) ≫
          (derivedRestriction.{u, v, dR, dS} J q).map
            (comparison.{u, v, wR, wS, dR, dS} J q M) ≫
          (derivedRestrictionIso.{u, v, wR, wS, dR, dS} J q).hom.app
            ((moduleDerivedExtension.{wR, wS, max u v} q).obj M) =
        (commutativeSiteDerivedConstantModuleFunctor.{u, v, wR, dR} J R).map
          ((moduleDerivedAdjunction.{wR, wS, max u v} q).unit.app M))  := by
  intro M
  have h : (derivedAdjunction.{u, v, dR, dS} J q).unit.app
        ((commutativeSiteDerivedConstantModuleFunctor.{u, v, wR, dR} J R).obj M) ≫
      (derivedRestriction.{u, v, dR, dS} J q).map
        (comparison.{u, v, wR, wS, dR, dS} J q M) =
    (commutativeSiteDerivedConstantModuleFunctor.{u, v, wR, dR} J R).map
      ((moduleDerivedAdjunction.{wR, wS, max u v} q).unit.app M) ≫
      (derivedRestrictionIso.{u, v, wR, wS, dR, dS} J q).inv.app
        ((moduleDerivedExtension.{wR, wS, max u v} q).obj M) := by
    exact ((derivedAdjunction.{u, v, dR, dS} J q).homEquiv_unit _ _
      (comparison.{u, v, wR, wS, dR, dS} J q M)).symm.trans
      (Equiv.apply_symm_apply _ _)
  rw [← Category.assoc, h, Category.assoc, Iso.inv_hom_id_app]
  simp


private theorem categorical_kFlat_of_acyclic
    {A : Type*} [Category A] [Abelian A] [IsGrothendieckAbelian A]
    [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [BraidedCategory A]
    (P : CochainComplex A ℤ)
    (hP : ∀ Z : CochainComplex A ℤ, Z.Acyclic → (Z ⊗ P).Acyclic) :
    (HomologicalComplex.quasiIso A (.up ℤ)).kFlat P := by
  rw [← HomotopyCategory.kFlat_quotient_obj_iff,
    HomotopyCategory.kFlat_iff_preserves_acyclic]
  intro Z hZ
  obtain ⟨Z, rfl⟩ := Z.quotient_obj_surjective
  rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hZ
  have hr := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
    (Z ⊗ P)).2 (hP Z hZ)
  refine ⟨?_, hr⟩
  exact (HomotopyCategory.subcategoryAcyclic _).prop_of_iso (β_ _ _) hr

private theorem acyclic_tensor_of_categorical_kFlat
    {A : Type*} [Category A] [Abelian A] [IsGrothendieckAbelian A]
    [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [BraidedCategory A]
    (P : CochainComplex A ℤ)
    (hP : (HomologicalComplex.quasiIso A (.up ℤ)).kFlat P)
    (Z : CochainComplex A ℤ) (hZ : Z.Acyclic) : (Z ⊗ P).Acyclic := by
  rw [← HomotopyCategory.kFlat_quotient_obj_iff,
    HomotopyCategory.kFlat_iff_preserves_acyclic] at hP
  exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).1
    (hP ((HomotopyCategory.quotient _ _).obj Z)
      ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2 hZ)).2

private theorem moduleRepresentative_isIso
    {A B : Type r} [CommRing A] [CommRing B] (f : A →+* B)
    [HasDerivedCategory.{wR} (ModuleCat.{r} A)]
    [HasDerivedCategory.{wS} (ModuleCat.{r} B)]
    (P : CochainComplex (ModuleCat.{r} A) ℤ) (hP : P.IsKFlatForTotalTensor) :
    IsIso (moduleRepresentative.{wR, wS, r} f P) := by
  have := ModuleCat.hasFunctorialFlatResolution_sameUniverse A
  have := ModuleCat.extendScalars_preservesKFlatQuasiIso f
  have : AB5OfSize.{0, 0} (ModuleCat.{r} A) :=
    AB5OfSize_of_univLE.{0, 0, r, r} _
  have : HasExactColimitsOfShape ℤ (ModuleCat.{r} A) := inferInstance
  exact Adjunction.isIso_cochainTranspose_of_kFlat
    (ModuleCat.extendScalars f) (ModuleCat.restrictScalars f)
    (ModuleCat.extendRestrictScalarsAdj f)
    (moduleDerivedAdjunction.{wR, wS, r} f) P hP

omit [HasDerivedCategory.{wR} (ModuleCat.{max u v} R)]
    [HasDerivedCategory.{wS} (ModuleCat.{max u v} S)] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem sheafRepresentative_isIso
    (P : CochainComplex (realizationModules J R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J)
      (R := realizationRing J R) P) :
    IsIso (sheafRepresentative.{u, v, dR, dS} J q P) := by
  let O := realizationRing J R
  let A := realizationModules J R
  let φ := (constantSheaf J CommRingCat.{max u v}).map (CommRingCat.ofHom q)
  let := SheafOfModules.isMonoidal_W_independentCoefficients O
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := SheafOfModules.tensorPreadditive O
  let := SheafOfModules.monoidalClosed_kfi (R := O)
  have : IsGrothendieckAbelian.{max u v} A :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses
      J O).1
  have := SheafOfModules.hasFunctorialFlatResolution_kfi O
  have := SheafOfModules.hasExactColimits_int_kfi O
  let E : realizationModules J R ⥤ realizationModules J S :=
    SheafOfModules.CoefficientOrdinaryProof.tensorFunctor.{max u v, u, v} φ
  let a : E ⊣ restriction J q :=
    SheafOfModules.CoefficientOrdinaryProof.tensorAdjunction φ
  have : E.Additive := a.left_adjoint_additive
  let i := (adjunction J q).leftAdjointUniq a
  have : (extension J q).PreservesKFlatQuasiIso := by
    constructor
    intro K L hK hL f hf
    have hK' : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := O) K :=
      acyclic_tensor_of_categorical_kFlat K hK
    have hL' : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := O) L :=
      acyclic_tensor_of_categorical_kFlat L hL
    have he := SheafOfModules.derivedChangeOfRingsIndependentCoefficients_kflat_invariance
      φ E (fun _ ↦ rfl) (by intros; rfl) f hK' hL' hf
    exact (HomologicalComplex.quasiIso _ _).arrow_mk_iso_iff
      (Arrow.isoMk ((NatIso.mapHomologicalComplex i (.up ℤ)).app K)
        ((NatIso.mapHomologicalComplex i (.up ℤ)).app L)
        ((NatIso.mapHomologicalComplex i (.up ℤ)).hom.naturality f).symm) |>.2 he
  exact Adjunction.isIso_cochainTranspose_of_kFlat
    (extension J q) (restriction J q) (adjunction J q)
    (derivedAdjunction.{u, v, dR, dS} J q) P
    (categorical_kFlat_of_acyclic P hP)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem comparison_representative_square
    (P : CochainComplex (ModuleCat.{max u v} R) ℤ) :
    comparison.{u, v, wR, wS, dR, dS} J q (DerivedCategory.Q.obj P) ≫
        (commutativeSiteDerivedConstantModuleFunctor.{u, v, wS, dS} J S).map
          (moduleRepresentative.{wR, wS, max u v} q P) ≫
        (commutativeSiteConstantModuleFunctor J S).mapDerivedCategoryFactors.hom.app
          (((ModuleCat.extendScalars q).mapHomologicalComplex (.up ℤ)).obj P) =
      (derivedExtension.{u, v, dR, dS} J q).map
          ((commutativeSiteConstantModuleFunctor J R).mapDerivedCategoryFactors.hom.app P) ≫
        sheafRepresentative.{u, v, dR, dS} J q
          (((commutativeSiteConstantModuleFunctor J R).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map (complexComparison J q P) := by
  let cR := commutativeSiteConstantModuleFunctor J R
  let cS := commutativeSiteConstantModuleFunctor J S
  let cr := commutativeSiteDerivedConstantModuleFunctor.{u, v, wR, dR} J R
  let cs := commutativeSiteDerivedConstantModuleFunctor.{u, v, wS, dS} J S
  let U := restriction J q
  let Um := ModuleCat.restrictScalars q
  let ur := derivedRestriction.{u, v, dR, dS} J q
  let um := moduleDerivedRestriction.{wR, wS, max u v} q
  let ad := derivedAdjunction.{u, v, dR, dS} J q
  let md := moduleDerivedAdjunction.{wR, wS, max u v} q
  let E := ModuleCat.extendScalars q
  let Q := DerivedCategory.Q (C := realizationModules J R)
  let P' := (E.mapHomologicalComplex (.up ℤ)).obj P
  let cP := (cR.mapHomologicalComplex (.up ℤ)).obj P
  let e := derivedRestrictionIso.{u, v, wR, wS, dR, dS} J q
  let γ := (NatTrans.mapHomologicalComplex (restrictionIso J q).inv (.up ℤ)).app P'
  have hm : md.unit.app (DerivedCategory.Q.obj P) ≫
      um.map (moduleRepresentative.{wR, wS, max u v} q P) =
    DerivedCategory.Q.map
      (((ModuleCat.extendRestrictScalarsAdj q).mapHomologicalComplex (.up ℤ)).unit.app P) ≫
        Um.mapDerivedCategoryFactors.inv.app P' := by
    exact (md.homEquiv_unit _ _ _).symm.trans (Equiv.apply_symm_apply _ _)
  have hs : ad.unit.app (Q.obj cP) ≫
      ur.map (sheafRepresentative.{u, v, dR, dS} J q cP) =
    Q.map (((adjunction J q).mapHomologicalComplex (.up ℤ)).unit.app cP) ≫
      U.mapDerivedCategoryFactors.inv.app
        (((extension J q).mapHomologicalComplex (.up ℤ)).obj cP) := by
    exact (ad.homEquiv_unit _ _ _).symm.trans (Equiv.apply_symm_apply _ _)
  have hc : ((adjunction J q).mapHomologicalComplex (.up ℤ)).unit.app cP ≫
      (U.mapHomologicalComplex (.up ℤ)).map (complexComparison J q P) =
    (cR.mapHomologicalComplex (.up ℤ)).map
      (((ModuleCat.extendRestrictScalarsAdj q).mapHomologicalComplex (.up ℤ)).unit.app P) ≫
        γ := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact ((adjunction J q).homEquiv_unit _ _ (moduleComparison J q (P.X n))).symm.trans
      (Equiv.apply_symm_apply _ _)
  have he := Functor.exactSquare_fac (restrictionIso J q).symm P'
  rw [Functor.square_symm_hom] at he
  change e.inv.app (DerivedCategory.Q.obj P') ≫
      ur.map (cS.mapDerivedCategoryFactors.hom.app P') ≫
      U.mapDerivedCategoryFactors.hom.app ((cS.mapHomologicalComplex (.up ℤ)).obj P') =
    cr.map (Um.mapDerivedCategoryFactors.hom.app P') ≫
      cR.mapDerivedCategoryFactors.hom.app ((Um.mapHomologicalComplex (.up ℤ)).obj P') ≫
        Q.map γ at he
  apply ad.homEquiv _ _ |>.injective
  rw [Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp only [comparison, ad, Equiv.apply_symm_apply, Category.assoc]
  apply (cancel_mono (U.mapDerivedCategoryFactors.hom.app
    ((cS.mapHomologicalComplex (.up ℤ)).obj P'))).mp
  change (cr.map (md.unit.app (DerivedCategory.Q.obj P)) ≫ e.inv.app _ ≫
      ur.map (cs.map (moduleRepresentative.{wR, wS, max u v} q P) ≫
        cS.mapDerivedCategoryFactors.hom.app P')) ≫ _ =
    (cR.mapDerivedCategoryFactors.hom.app P ≫
      ad.homEquiv _ _ (sheafRepresentative.{u, v, dR, dS} J q cP) ≫
        ur.map (DerivedCategory.Q.map (complexComparison J q P))) ≫ _
  rw [Adjunction.homEquiv_unit]
  simp only [Functor.map_comp, Category.assoc]
  have hn := e.inv.naturality (moduleRepresentative.{wR, wS, max u v} q P)
  change cr.map (um.map (moduleRepresentative.{wR, wS, max u v} q P)) ≫
      e.inv.app (DerivedCategory.Q.obj P') =
    e.inv.app _ ≫ ur.map (cs.map (moduleRepresentative.{wR, wS, max u v} q P)) at hn
  rw [← reassoc_of% hn, ← Functor.map_comp_assoc, hm, Functor.map_comp, Category.assoc,
    he]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  have hnat := cR.mapDerivedCategoryFactors.hom.naturality
    (((ModuleCat.extendRestrictScalarsAdj q).mapHomologicalComplex (.up ℤ)).unit.app P)
  change cr.map (DerivedCategory.Q.map _) ≫ cR.mapDerivedCategoryFactors.hom.app _ =
    cR.mapDerivedCategoryFactors.hom.app P ≫ Q.map _ at hnat
  rw [reassoc_of% hnat, ← Q.map_comp, ← hc]
  rw [Functor.map_comp]
  have hu := U.mapDerivedCategoryFactors.hom.naturality (complexComparison J q P)
  change ur.map (DerivedCategory.Q.map (complexComparison J q P)) ≫
      U.mapDerivedCategoryFactors.hom.app _ =
    U.mapDerivedCategoryFactors.hom.app _ ≫
      Q.map ((U.mapHomologicalComplex (.up ℤ)).map (complexComparison J q P)) at hu
  erw [reassoc_of% hs]
  rw [hu]
  erw [Iso.inv_hom_id_app_assoc]

private theorem comparison_isIso (M : DerivedCategory (ModuleCat.{max u v} R)) :
    IsIso (comparison.{u, v, wR, wS, dR, dS} J q M) := by
  have := ModuleCat.hasFunctorialFlatResolution_sameUniverse R
  let P := DerivedCategory.Q.objPreimage M
  obtain ⟨L, f, hf, hflat, hL⟩ := P.exists_quasiIso_flat_kFlat
  have : QuasiIso f := hf
  have hflat' (i : ℤ) : Module.Flat R (L.X i) := (ModuleCat.flat_iff_flat _).1 (hflat i)
  have hc := isKFlat_constantModule J R L hL hflat'
  have : IsIso (moduleRepresentative.{wR, wS, max u v} q L) :=
    moduleRepresentative_isIso q L hL
  have : IsIso (sheafRepresentative.{u, v, dR, dS} J q
      (((commutativeSiteConstantModuleFunctor J R).mapHomologicalComplex (.up ℤ)).obj L)) :=
    sheafRepresentative_isIso J q _ hc
  have (n : ℤ) : IsIso ((complexComparison J q L).f n) := moduleComparison_isIso J q _
  have : IsIso (complexComparison J q L) := HomologicalComplex.Hom.isIso_of_components _
  let cs := commutativeSiteDerivedConstantModuleFunctor.{u, v, wS, dS} J S
  let cr := commutativeSiteDerivedConstantModuleFunctor.{u, v, wR, dR} J R
  let ls := derivedExtension.{u, v, dR, dS} J q
  let lm := moduleDerivedExtension.{wR, wS, max u v} q
  have hs := comparison_representative_square.{u, v, wR, wS, dR, dS} J q L
  have : IsIso (comparison.{u, v, wR, wS, dR, dS} J q (DerivedCategory.Q.obj L)) := by
    have : IsIso (comparison.{u, v, wR, wS, dR, dS} J q (DerivedCategory.Q.obj L) ≫
        (cs.map (moduleRepresentative.{wR, wS, max u v} q L) ≫
          (commutativeSiteConstantModuleFunctor J S).mapDerivedCategoryFactors.hom.app
            (((ModuleCat.extendScalars q).mapHomologicalComplex (.up ℤ)).obj L))) := by
      rw [hs]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      (cs.map (moduleRepresentative.{wR, wS, max u v} q L) ≫
        (commutativeSiteConstantModuleFunctor J S).mapDerivedCategoryFactors.hom.app
          (((ModuleCat.extendScalars q).mapHomologicalComplex (.up ℤ)).obj L))
  let e : DerivedCategory.Q.obj L ≅ M :=
    asIso (DerivedCategory.Q.map f) ≪≫ DerivedCategory.Q.objObjPreimageIso M
  have hn := comparison_naturality.{u, v, wR, wS, dR, dS} J q e.hom
  have : IsIso (cs.map (lm.map e.hom)) := by infer_instance
  have : IsIso (ls.map (cr.map e.hom)) := by infer_instance
  exact IsIso.of_isIso_fac_left hn

/-- Constant realization commutes with unbounded derived scalar extension, including
its canonical flat-term K-flat model and scalar-extension unit.
Source: Stacks 0G7E, 0D6D, 093J, 0GMW, 03CY and 07A6
(blueprint: lem-sfb-constant-realization-derived-scalar-extension).
Proof: constant realization preserves flat modules by the local relation criterion
and preserves colimits by its presheaf and sheafification construction. The flat-term
K-flat preservation theorem therefore applies. The canonical representative maps are
the transported left-derived counits of the ordinary scalar adjunctions, hence are
invertible on K-flat complexes. Transposing the representative square reduces it to
the ordinary comparison-unit identity and exact-functor localization naturality.
Every derived object admits a flat-term K-flat representative, so this square makes
the comparison invertible everywhere. The mate definition proves the unit identity.
All complexes are unbounded and no finiteness or Noetherian assumption is used. -/
theorem constantRealizationDerivedScalarExtension :
    IsIso (comparisonTransformation.{u, v, wR, wS, dR, dS} J q) ∧
    (∀ (P : CochainComplex (ModuleCat.{max u v} R) ℤ),
      P.IsKFlatForTotalTensor → (∀ n : ℤ, Module.Flat R (P.X n)) →
      let cP := ((commutativeSiteConstantModuleFunctor J R).mapHomologicalComplex (.up ℤ)).obj P
      CochainComplex.IsKFlatIndependentCoefficients.{u, v, max u v}
        (J := J) (R := realizationRing J R) cP ∧
      (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u, v, max u v, max u v}
        (J := J) (R := realizationRing J R) (cP.X n)) ∧
      IsIso (moduleRepresentative.{wR, wS, max u v} q P) ∧
      IsIso (sheafRepresentative.{u, v, dR, dS} J q cP) ∧
      comparison.{u, v, wR, wS, dR, dS} J q (DerivedCategory.Q.obj P) ≫
          (commutativeSiteDerivedConstantModuleFunctor.{u, v, wS, dS} J S).map
            (moduleRepresentative.{wR, wS, max u v} q P) ≫
          (commutativeSiteConstantModuleFunctor J S).mapDerivedCategoryFactors.hom.app
            (((ModuleCat.extendScalars q).mapHomologicalComplex (.up ℤ)).obj P) =
        (derivedExtension.{u, v, dR, dS} J q).map
            ((commutativeSiteConstantModuleFunctor J R).mapDerivedCategoryFactors.hom.app P) ≫
          sheafRepresentative.{u, v, dR, dS} J q cP ≫
          DerivedCategory.Q.map (complexComparison J q P)) ∧
    (∀ M : DerivedCategory (ModuleCat.{max u v} R),
      (derivedAdjunction.{u, v, dR, dS} J q).unit.app
          ((commutativeSiteDerivedConstantModuleFunctor.{u, v, wR, dR} J R).obj M) ≫
          (derivedRestriction.{u, v, dR, dS} J q).map
            (comparison.{u, v, wR, wS, dR, dS} J q M) ≫
          (derivedRestrictionIso.{u, v, wR, wS, dR, dS} J q).hom.app
            ((moduleDerivedExtension.{wR, wS, max u v} q).obj M) =
        (commutativeSiteDerivedConstantModuleFunctor.{u, v, wR, dR} J R).map
          ((moduleDerivedAdjunction.{wR, wS, max u v} q).unit.app M)) := by
  refine ⟨?_, ?_, comparison_unit J q⟩
  · exact (NatTrans.isIso_iff_isIso_app _).2 (comparison_isIso J q)
  · intro P hP hf
    have hc := isKFlat_constantModule J R P hP hf
    exact ⟨hc, fun n ↦ isFlatOnSite_constantModule J R (P.X n) (hf n),
      moduleRepresentative_isIso q P hP, sheafRepresentative_isIso J q _ hc,
      comparison_representative_square J q P⟩

/-- The canonical natural isomorphism, with the preceding representative normalization.
Source: Stacks 0D6D (blueprint: lem-sfb-constant-realization-derived-scalar-extension). -/
def comparisonIso :
    commutativeSiteDerivedConstantModuleFunctor.{u, v, wR, dR} J R ⋙
        derivedExtension.{u, v, dR, dS} J q ≅
      moduleDerivedExtension.{wR, wS, max u v} q ⋙
        commutativeSiteDerivedConstantModuleFunctor.{u, v, wS, dS} J S :=
  letI := (constantRealizationDerivedScalarExtension.{u, v, wR, wS, dR, dS} J q).1
  asIso (comparisonTransformation.{u, v, wR, wS, dR, dS} J q)

end Derived
section Tower

variable {T : Type (max u v)} [CommRing T] (b : S →+* T)

/-- Ordinary sheaf restriction composes by the identity on the underlying sections.
Source: Stacks 03DA (blueprint: lem-sfb-constant-realization-derived-scalar-extension).
Proof: the ring functor sends the composite ring map to the composite constant-sheaf
map. Both restricted scalar actions and all section restrictions therefore coincide.
The identity section maps are linear and natural; they give the unique such isomorphism. -/
theorem restrictionComposition_existsUnique :
    ∃! e : restriction J b ⋙ restriction J q ≅ restriction J (b.comp q),
      ∀ (M : realizationModules J T) (V : Cᵒᵖ) (x : M.val.obj V),
        (e.hom.app M).val.app V x = x := by
  let α := ((sheafCompose J
    (forget₂ CommRingCat.{max u v} RingCat.{max u v})).map
      ((constantSheaf J CommRingCat.{max u v}).map (CommRingCat.ofHom q)))
  let β := ((sheafCompose J
    (forget₂ CommRingCat.{max u v} RingCat.{max u v})).map
      ((constantSheaf J CommRingCat.{max u v}).map (CommRingCat.ofHom b)))
  let γ := ((sheafCompose J
    (forget₂ CommRingCat.{max u v} RingCat.{max u v})).map
      ((constantSheaf J CommRingCat.{max u v}).map (CommRingCat.ofHom (b.comp q))))
  have hγ : γ = α ≫ β := by
    dsimp [γ, α, β]
    rw [← Functor.map_comp, ← Functor.map_comp]
  let eM (M : realizationModules J T) :
      (restriction J b ⋙ restriction J q).obj M ≅ (restriction J (b.comp q)).obj M :=
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun V ↦
        (ModuleCat.restrictScalarsComp'App (α.hom.app V).hom (β.hom.app V).hom
          (γ.hom.app V).hom
          (by simpa using congrArg (fun f ↦ (f.hom.app V).hom) hγ)
          (M.val.obj V)).symm) (by intros; ext x; rfl))
  let e := NatIso.ofComponents eM (by intros; ext V x; rfl)
  refine ⟨e, ?_, ?_⟩
  · dsimp only
    intro M V x
    rfl
  · intro e' he'
    apply Iso.ext
    apply NatTrans.ext
    funext M
    ext V x
    exact he' M V x

/-- The normalized ordinary restriction composition isomorphism.
Source: Stacks 03DA (blueprint: lem-sfb-constant-realization-derived-scalar-extension). -/
def restrictionComposition : restriction J b ⋙ restriction J q ≅ restriction J (b.comp q) :=
  Classical.choose (restrictionComposition_existsUnique J q b)

private theorem restrictionComposition_inv_section (M : realizationModules J T)
    (V : Cᵒᵖ) (x : M.val.obj V) :
    ((restrictionComposition J q b).inv.app M).val.app V x = x := by
  have h := (Classical.choose_spec (restrictionComposition_existsUnique J q b)).1 M V
    (((restrictionComposition J q b).inv.app M).val.app V x)
  have h' := congrArg (fun f ↦ f.val.app V x)
    ((restrictionComposition J q b).inv_hom_id_app M)
  exact h.symm.trans h'

set_option backward.isDefEq.respectTransparency false in
private theorem restrictionIso_comp (M : ModuleCat.{max u v} T) :
    (commutativeSiteConstantModuleFunctor J R).map
        ((ModuleCat.restrictScalarsComp' q b (b.comp q) rfl).hom.app M) ≫
      (restrictionIso J q).inv.app ((ModuleCat.restrictScalars b).obj M) ≫
      (restriction J q).map ((restrictionIso J b).inv.app M) =
    (restrictionIso J (b.comp q)).inv.app M ≫
      (restrictionComposition J q b).inv.app
        ((commutativeSiteConstantModuleFunctor J T).obj M) := by
  apply constantSection_ext J
  intro V x
  change ((restrictionIso J b).inv.app M).val.app V
      (((restrictionIso J q).inv.app ((ModuleCat.restrictScalars b).obj M)).val.app V
        (((commutativeSiteConstantModuleFunctor J R).map
          ((ModuleCat.restrictScalarsComp' q b (b.comp q) rfl).hom.app M)).val.app V
            (constantSection J ((ModuleCat.restrictScalars (b.comp q)).obj M) V x))) =
    ((restrictionComposition J q b).inv.app
      ((commutativeSiteConstantModuleFunctor J T).obj M)).val.app V
        (((restrictionIso J (b.comp q)).inv.app M).val.app V
          (constantSection J ((ModuleCat.restrictScalars (b.comp q)).obj M) V x))
  rw [constantSection_naturality]
  erw [restrictionIso_inv_constantSection, restrictionIso_inv_constantSection,
    restrictionIso_inv_constantSection, restrictionComposition_inv_section]
  rfl

variable [HasDerivedCategory.{wR} (ModuleCat.{max u v} R)]
  [HasDerivedCategory.{wS} (ModuleCat.{max u v} S)]
  [HasDerivedCategory.{wT} (ModuleCat.{max u v} T)]
  [HasDerivedCategory.{dR} (realizationModules J R)]
  [HasDerivedCategory.{dS} (realizationModules J S)]
  [HasDerivedCategory.{dT} (realizationModules J T)]

/-- Canonical transitivity of exact derived restriction on the site.
Source: Stacks 0D6D (blueprint: lem-sfb-constant-realization-derived-scalar-extension). -/
def derivedRestrictionComposition :
    derivedRestriction.{u, v, dS, dT} J b ⋙ derivedRestriction.{u, v, dR, dS} J q ≅
      derivedRestriction.{u, v, dR, dT} J (b.comp q) :=
  letI := comp_preservesFiniteLimits (restriction J b) (restriction J q)
  letI := comp_preservesFiniteColimits (restriction J b) (restriction J q)
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (restrictionComposition J q b)

/-- Canonical derived scalar transitivity, fixed by the scalar-extension units.
Source: Stacks 0D6D (blueprint: lem-sfb-constant-realization-derived-scalar-extension). -/
def transitivity :
    derivedExtension.{u, v, dR, dS} J q ⋙ derivedExtension.{u, v, dS, dT} J b ≅
      derivedExtension.{u, v, dR, dT} J (b.comp q) :=
  (((derivedAdjunction.{u, v, dR, dS} J q).comp
      (derivedAdjunction.{u, v, dS, dT} J b)).ofNatIsoRight
        (derivedRestrictionComposition.{u, v, dR, dS, dT} J q b)).leftAdjointUniq
    (derivedAdjunction.{u, v, dR, dT} J (b.comp q))

/-- Canonical transitivity of exact module restriction.
Source: Stacks 0D6D (blueprint: lem-sfb-constant-realization-derived-scalar-extension). -/
def moduleDerivedRestrictionComposition
    {A B D : Type r} [CommRing A] [CommRing B] [CommRing D]
    (f : A →+* B) (g : B →+* D)
    [HasDerivedCategory.{wR} (ModuleCat.{r} A)]
    [HasDerivedCategory.{wS} (ModuleCat.{r} B)]
    [HasDerivedCategory.{wT} (ModuleCat.{r} D)] :
    moduleDerivedRestriction.{wS, wT, r} g ⋙ moduleDerivedRestriction.{wR, wS, r} f ≅
      moduleDerivedRestriction.{wR, wT, r} (g.comp f) :=
  letI := comp_preservesFiniteLimits
    (ModuleCat.restrictScalars g) (ModuleCat.restrictScalars f)
  letI := comp_preservesFiniteColimits
    (ModuleCat.restrictScalars g) (ModuleCat.restrictScalars f)
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (ModuleCat.restrictScalarsComp' f g (g.comp f) rfl).symm

set_option backward.isDefEq.respectTransparency false in
private theorem derivedRestrictionIso_comp
    (N : DerivedCategory (ModuleCat.{max u v} T)) :
    (commutativeSiteDerivedConstantModuleFunctor.{u, v, wR, dR} J R).map
        ((moduleDerivedRestrictionComposition.{wR, wS, wT, max u v} q b).inv.app N) ≫
      (derivedRestrictionIso.{u, v, wR, wS, dR, dS} J q).inv.app
        ((moduleDerivedRestriction.{wS, wT, max u v} b).obj N) ≫
      (derivedRestriction.{u, v, dR, dS} J q).map
        ((derivedRestrictionIso.{u, v, wS, wT, dS, dT} J b).inv.app N) =
    (derivedRestrictionIso.{u, v, wR, wT, dR, dT} J (b.comp q)).inv.app N ≫
      (derivedRestrictionComposition.{u, v, dR, dS, dT} J q b).inv.app
        ((commutativeSiteDerivedConstantModuleFunctor.{u, v, wT, dT} J T).obj N) := by
  have h := Functor.exactSquare_comp_forward
    (ModuleCat.restrictScalars b) (ModuleCat.restrictScalars q)
    (ModuleCat.restrictScalars (b.comp q))
    (restriction J b) (restriction J q) (restriction J (b.comp q))
    (commutativeSiteConstantModuleFunctor J T)
    (commutativeSiteConstantModuleFunctor J S)
    (commutativeSiteConstantModuleFunctor J R)
    (restrictionIso J b).symm (restrictionIso J q).symm
    (restrictionIso J (b.comp q)).symm
    (ModuleCat.restrictScalarsComp' q b (b.comp q) rfl)
    (restrictionComposition J q b).symm (restrictionIso_comp J q b) N
  simpa only [derivedRestrictionIso, moduleDerivedRestrictionComposition,
    derivedRestrictionComposition, Functor.mapDerivedCategorySquareIso,
    ← Functor.mapDerivedCategoryNatIso_symm, Iso.symm_symm_eq,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    NatTrans.comp_app, Category.assoc,
    commutativeSiteDerivedConstantModuleFunctor, derivedRestriction,
    moduleDerivedRestriction] using h

/-- The unit-preserving module derived tensor associator.
Source: Stacks 0D6D (blueprint: lem-sfb-constant-realization-derived-scalar-extension). -/
def moduleTransitivity
    {A B D : Type r} [CommRing A] [CommRing B] [CommRing D]
    (f : A →+* B) (g : B →+* D)
    [HasDerivedCategory.{wR} (ModuleCat.{r} A)]
    [HasDerivedCategory.{wS} (ModuleCat.{r} B)]
    [HasDerivedCategory.{wT} (ModuleCat.{r} D)] :
    moduleDerivedExtension.{wR, wS, r} f ⋙ moduleDerivedExtension.{wS, wT, r} g ≅
      moduleDerivedExtension.{wR, wT, r} (g.comp f) :=
  (((moduleDerivedAdjunction.{wR, wS, r} f).comp
      (moduleDerivedAdjunction.{wS, wT, r} g)).ofNatIsoRight
        (moduleDerivedRestrictionComposition.{wR, wS, wT, r} f g)).leftAdjointUniq
    (moduleDerivedAdjunction.{wR, wT, r} (g.comp f))

/-- The three comparisons for R to S, S to T, and R to T commute with both
canonical derived transitivity isomorphisms.
Source: Stacks 0D6D and 0G7E
(blueprint: lem-sfb-constant-realization-derived-scalar-extension).
Proof: the ordinary restriction comparisons compose, as checked on constant sections
using the sheafification universal property. Exact-square composition transports this
identity to the independently sized derived categories. Transpose the required
identity under the composite derived adjunction. Naturality of the restriction
comparison and the scalar units identifies its left side with the composite unit;
the unit equation for left-adjoint uniqueness identifies its right side with that
same unit. This proves coherence for every derived object directly. -/
theorem constantRealizationDerivedScalarExtension_transitivity
    (M : DerivedCategory (ModuleCat.{max u v} R)) :
    (derivedExtension.{u, v, dS, dT} J b).map
        (comparison.{u, v, wR, wS, dR, dS} J q M) ≫
      comparison.{u, v, wS, wT, dS, dT} J b
        ((moduleDerivedExtension.{wR, wS, max u v} q).obj M) ≫
      (commutativeSiteDerivedConstantModuleFunctor.{u, v, wT, dT} J T).map
        ((moduleTransitivity.{wR, wS, wT, max u v} q b).hom.app M) =
    (transitivity.{u, v, dR, dS, dT} J q b).hom.app
        ((commutativeSiteDerivedConstantModuleFunctor.{u, v, wR, dR} J R).obj M) ≫
      comparison.{u, v, wR, wT, dR, dT} J (b.comp q) M := by
  let cR := commutativeSiteDerivedConstantModuleFunctor.{u, v, wR, dR} J R
  let cS := commutativeSiteDerivedConstantModuleFunctor.{u, v, wS, dS} J S
  let cT := commutativeSiteDerivedConstantModuleFunctor.{u, v, wT, dT} J T
  let aq := derivedAdjunction.{u, v, dR, dS} J q
  let ab := derivedAdjunction.{u, v, dS, dT} J b
  let mq := moduleDerivedAdjunction.{wR, wS, max u v} q
  let mb := moduleDerivedAdjunction.{wS, wT, max u v} b
  let mt := moduleDerivedAdjunction.{wR, wT, max u v} (b.comp q)
  let rq := derivedRestriction.{u, v, dR, dS} J q
  let rb := derivedRestriction.{u, v, dS, dT} J b
  let rt := derivedRestriction.{u, v, dR, dT} J (b.comp q)
  let rmq := moduleDerivedRestriction.{wR, wS, max u v} q
  let rmb := moduleDerivedRestriction.{wS, wT, max u v} b
  let rmt := moduleDerivedRestriction.{wR, wT, max u v} (b.comp q)
  let eq := derivedRestrictionIso.{u, v, wR, wS, dR, dS} J q
  let eb := derivedRestrictionIso.{u, v, wS, wT, dS, dT} J b
  let et := derivedRestrictionIso.{u, v, wR, wT, dR, dT} J (b.comp q)
  let ds := derivedRestrictionComposition.{u, v, dR, dS, dT} J q b
  let dm := moduleDerivedRestrictionComposition.{wR, wS, wT, max u v} q b
  let tm := moduleTransitivity.{wR, wS, wT, max u v} q b
  let N := (moduleDerivedExtension.{wR, wS, max u v} q).obj M
  let P := (moduleDerivedExtension.{wS, wT, max u v} b).obj N
  have hcoh : eq.inv.app (rmb.obj P) ≫ rq.map (eb.inv.app P) =
      cR.map (dm.hom.app P) ≫ et.inv.app P ≫ ds.inv.app (cT.obj P) := by
    have h := congrArg (fun f ↦ cR.map (dm.hom.app P) ≫ f)
      (derivedRestrictionIso_comp.{u, v, wR, wS, wT, dR, dS, dT} J q b P)
    simpa only [cR, dm, eq, eb, et, ds, cT, rq, rmb,
      ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
      Functor.map_id, Category.id_comp, Category.assoc] using h
  apply (((aq.comp ab).ofNatIsoRight ds).homEquiv _ _).injective
  conv_rhs =>
    rw [Adjunction.homEquiv_naturality_right]
    unfold transitivity
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app,
      ← Adjunction.homEquiv_unit]
    simp only [comparison, Equiv.apply_symm_apply]
  change ((aq.comp ab).ofNatIsoRight ds).homEquiv _ _
      ((derivedExtension J b).map (comparison J q M) ≫
        comparison J b N ≫ cT.map (tm.hom.app M)) =
    cR.map (mt.unit.app M) ≫ et.inv.app _
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
  change aq.homEquiv _ _ (ab.homEquiv _ _
      ((derivedExtension J b).map (comparison J q M) ≫
        comparison J b N ≫ cT.map (tm.hom.app M))) ≫ ds.hom.app _ = _
  rw [Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_naturality_right]
  rw [Adjunction.homEquiv_naturality_right]
  simp only [comparison, aq, ab, N, Equiv.apply_symm_apply]
  rw [Category.assoc]
  change (cR.map (mq.unit.app M) ≫ eq.inv.app N) ≫
      rq.map ((cS.map (mb.unit.app N) ≫ eb.inv.app P) ≫
        rb.map (cT.map (tm.hom.app M))) ≫ ds.hom.app _ = _
  simp only [Functor.map_comp, Category.assoc]
  have hn : eq.inv.app N ≫ rq.map (cS.map (mb.unit.app N)) =
      cR.map (rmq.map (mb.unit.app N)) ≫ eq.inv.app (rmb.obj P) :=
    (eq.inv.naturality (mb.unit.app N)).symm
  rw [reassoc_of% hn, reassoc_of% hcoh]
  have hd : ds.inv.app (cT.obj P) ≫ rq.map (rb.map (cT.map (tm.hom.app M))) =
      rt.map (cT.map (tm.hom.app M)) ≫ ds.inv.app _ :=
    (ds.inv.naturality (cT.map (tm.hom.app M))).symm
  rw [reassoc_of% hd]
  simp only [Iso.inv_hom_id_app]
  have he : et.inv.app P ≫ rt.map (cT.map (tm.hom.app M)) =
      cR.map (rmt.map (tm.hom.app M)) ≫ et.inv.app _ :=
    (et.inv.naturality (tm.hom.app M)).symm
  rw [reassoc_of% he]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc,
    ← Functor.map_comp_assoc]
  congr 1
  · apply congrArg cR.map
    simpa only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
      Functor.whiskerLeft_app, Adjunction.comp_unit_app, tm, moduleTransitivity,
      mq, mb, mt, N, P, rmq, rmt, Functor.comp_obj] using
      (Adjunction.unit_leftAdjointUniq_hom_app ((mq.comp mb).ofNatIsoRight dm) mt M)
  · exact Category.comp_id _



end Tower
end CategoryTheory.ConstantScalarRealization
