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
import Sheaf.RingTheory.DerivedModuleScalarAdjunction

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization
import Sheaf.CategoryTheory.SiteConstantModuleFunctorGeneral
import Sheaf.Paper.KFlatRingedToposPullback
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
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace CategoryTheory.ConstantScalarRealization

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
  let := HasDerivedCategory.standard (realizationModules J R)
  let := HasDerivedCategory.standard (realizationModules J S)
  let φ := (constantSheaf J CommRingCat.{max u v}).map (CommRingCat.ofHom q)
  obtain ⟨hlim, hcol, h⟩ := SheafOfModules.sheafRingDerivedCoefficientAdjunction φ
  obtain ⟨E, hobj, hmap, hadd, _⟩ :=
    SheafOfModules.derivedChangeOfRingsIndependentCoefficients φ
  let := hadd
  obtain ⟨a, _⟩ := h E hobj hmap
  exact ⟨hlim, hcol, a.isRightAdjoint⟩

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
  sorry

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
  sorry

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

/-- Constant realization commutes with unbounded derived scalar extension, including
its canonical flat-term K-flat model and scalar-extension unit.
Source: Stacks 0G7E, 0D6D, 093J, 0GMW, 03CY and 07A6
(blueprint: lem-sfb-constant-realization-derived-scalar-extension).
Proof: construct the constant-sheaf geometric morphism without assuming a terminal
site object, using compatible families for its direct image. Its inverse image is
exact and its module pullback is constant realization. Tag 0G7E carries flat-term
K-flat complexes to flat-term K-flat complexes. Tag 0GMW identifies the two termwise
scalar tensors by identity on constant pure tensors, as in moduleComparison_tensor.
Derived change of rings computes both sides on these representatives. Localization
of flat-term K-flat representatives gives the natural isomorphism and the displayed
representative square. The mate definition makes the unit square commute: both
transposes are the realized module scalar unit followed by derivedRestrictionIso.inv.
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
  sorry

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
Proof: compute on a flat-term K-flat complex P. Extension carries it to a flat-term
K-flat complex over S, both on the point site and on J. Both routes send the constant
pure tensor (x tensor s) tensor t to x tensor b(s)t. Tensor generation and uniqueness
of sheafification identify the chain maps. The representative square and localization
of K-flat complexes give the equality for every M. The unit-normalized adjoint-uniqueness
isomorphisms above are exactly those tensor associators, since their representative
maps have this same balanced-tensor formula. This also covers identity maps and T = 0. -/
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
  sorry

end Tower
end CategoryTheory.ConstantScalarRealization
