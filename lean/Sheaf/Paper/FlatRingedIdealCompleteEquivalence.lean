/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Sheaf.Paper.RingedSiteIdeal
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Sheaf.CategoryTheory.LocallyDerivedRingedIdealComplete
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Sheaf.CategoryTheory.LocalExtendedCechDescription
public import Sheaf.CategoryTheory.RingedCompletionUnit
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Sheaf.Algebra.Homology.QuasiIsoHomComplexMap
import Sheaf.Paper.SiteRestrictionExact
import Sheaf.Paper.ExtendedCechCompletionModel
import Sheaf.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFlat
import Sheaf.Paper.FlatExtendedCechComparison
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Sheaf.Paper.RestrictionLocalCompleteness
import Sheaf.Paper.RestrictedCoefficientHomComplex
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.SiteRestrictionExact
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars
import Sheaf.Paper.RestrictedCoefficientHom

/-!
# Flat ringed-site equivalence on locally derived complete objects

Source: Stacks Project, Algebraization, Tags 099I and 0999
(blueprint: lem-weil-pbc-flat-ringed-ideal-complete-equivalence).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Restriction of scalars is exact on module sheaves.
Source: Stacks Project, Algebraization, Tag 099C
(blueprint: lem-weil-pbc-flat-ringed-ideal-complete-equivalence).
Proof: the underlying additive sheaf is unchanged. Kernels are sectionwise kernels with
restricted action; cokernels are sheafifications of the same additive presheaf cokernels.
The same description applies to finite products and coproducts. -/
theorem siteRestrictScalars_exact {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    PreservesFiniteLimits
      (SheafOfModules.restrictScalars.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)) ∧
    PreservesFiniteColimits
      (SheafOfModules.restrictScalars.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)) := by
  let F := SheafOfModules.restrictScalars.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
  have : PreservesFiniteLimits (F ⋙ SheafOfModules.toSheaf.{u} (siteModuleRings R)) :=
    inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf.{u} (siteModuleRings B)))
  have : PreservesFiniteColimits (F ⋙ SheafOfModules.toSheaf.{u} (siteModuleRings R)) :=
    inferInstanceAs (PreservesFiniteColimits (SheafOfModules.toSheaf.{u} (siteModuleRings B)))
  have : ReflectsFiniteColimits (SheafOfModules.toSheaf.{u} (siteModuleRings R)) :=
    { reflects := fun _ _ _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms }
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves F
      (SheafOfModules.toSheaf.{u} (siteModuleRings R)),
    preservesFiniteColimits_of_reflects_of_preserves F
      (SheafOfModules.toSheaf.{u} (siteModuleRings R))⟩

/-- Restriction of scalars preserves small limits, in particular the products in Hom complexes.
Source: Stacks Project, Algebraization, Tag 099I, the construction of E prime
(blueprint: lem-weil-pbc-flat-ringed-ideal-complete-equivalence).
Proof: compose with the faithful forgetful functor to additive presheaves. Both
forgetful functors preserve small limits, and this composite is the same over B.
The forgetful composite reflects isomorphisms and therefore reflects limits.
Reflection then gives preservation of limits by restriction itself. -/
theorem siteRestrictScalars_preservesLimits
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    PreservesLimitsOfSize.{u, u} (SheafOfModules.restrictScalars.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)) := by
  let F := SheafOfModules.restrictScalars.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
  let G := SheafOfModules.forget.{u} (siteModuleRings R) ⋙
    PresheafOfModules.toPresheaf.{u} (siteModuleRings R).obj
  have : PreservesLimitsOfSize.{u, u} (F ⋙ G) :=
    inferInstanceAs (PreservesLimitsOfSize.{u, u}
      (SheafOfModules.forget.{u} (siteModuleRings B) ⋙
        PresheafOfModules.toPresheaf.{u} (siteModuleRings B).obj))
  have : ReflectsLimitsOfSize.{u, u} G := reflectsLimits_of_reflectsIsomorphisms
  exact preservesLimits_of_reflects_of_preserves F G

/-- Restriction of scalars reflects isomorphisms of sheaves of modules.
Source: Stacks Project, Algebraization, Tag 099I, first paragraph
(blueprint: lem-weil-pbc-flat-ringed-ideal-complete-equivalence).
Proof: its composite with the forgetful functor to abelian sheaves is precisely the
forgetful functor over B, which reflects isomorphisms. -/
theorem siteRestrictScalars_reflectsIsomorphisms
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    (SheafOfModules.restrictScalars.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).ReflectsIsomorphisms := by
  let F := SheafOfModules.restrictScalars.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
  have : (F ⋙ SheafOfModules.toSheaf.{u} (siteModuleRings R)).ReflectsIsomorphisms :=
    inferInstanceAs ((SheafOfModules.toSheaf.{u} (siteModuleRings B)).ReflectsIsomorphisms)
  exact reflectsIsomorphisms_of_comp F (SheafOfModules.toSheaf.{u} (siteModuleRings R))

/-- Termwise restriction preserves and reflects quasi-isomorphisms.
Source: Stacks Project, Algebraization, Tag 099I, the construction of E prime
(blueprint: lem-weil-pbc-flat-ringed-ideal-complete-equivalence).
Proof: exactness identifies the restricted cohomology maps with restriction of the
original cohomology maps. Restriction reflects isomorphisms of these sheaves. -/
theorem siteRestrictScalars_quasiIso_iff
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    {K L : CochainComplex (SheafOfModules.{u} (siteModuleRings B)) ℤ} (f : K ⟶ L) :
    QuasiIso (((SheafOfModules.restrictScalars.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).mapHomologicalComplex
        (.up ℤ)).map f) ↔ QuasiIso f := by
  let := (siteRestrictScalars_exact φ).1
  let := (siteRestrictScalars_exact φ).2
  have := siteRestrictScalars_reflectsIsomorphisms φ
  exact HomologicalComplex.quasiIso_map_iff_of_preservesHomology f _

/-- Derived restriction of scalars, using Mathlib's restriction of scalars and its exact
functor localization, rather than an unspecified functor between derived categories.
Source: Stacks Project, Algebraization, Tags 099C and 099I
(blueprint: lem-weil-pbc-flat-ringed-ideal-complete-equivalence). -/
noncomputable def siteDerivedRestrictScalars {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (siteModuleRings R))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (siteModuleRings B))] :
    DerivedCategory (SheafOfModules.{u} (siteModuleRings B)) ⥤
      DerivedCategory (SheafOfModules.{u} (siteModuleRings R)) :=
  letI := (siteRestrictScalars_exact φ).1
  letI := (siteRestrictScalars_exact φ).2
  (SheafOfModules.restrictScalars.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).mapDerivedCategory


/-- Derived restriction of scalars reflects isomorphisms.
Source: Stacks Project, Algebraization, Tag 099I, first paragraph
(blueprint: lem-weil-pbc-flat-ringed-ideal-complete-equivalence).
Proof: the forgetful functor to abelian sheaves reflects isomorphisms, and its composite
with restriction is the same forgetful functor over B. Exactness commutes restriction
with every cohomology functor. Thus invertibility after restriction implies invertibility
on every cohomology sheaf, which detects isomorphisms of unbounded derived objects. -/
theorem siteDerivedRestrictScalars_reflectsIsomorphisms
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (siteModuleRings R))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (siteModuleRings B))] :
    (siteDerivedRestrictScalars φ).ReflectsIsomorphisms := by
  let F := SheafOfModules.restrictScalars.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
  let := (siteRestrictScalars_exact φ).1
  let := (siteRestrictScalars_exact φ).2
  have : F.ReflectsIsomorphisms := siteRestrictScalars_reflectsIsomorphisms φ
  constructor
  intro X Y f hf
  change IsIso (F.mapDerivedCategory.map f) at hf
  have := hf
  apply (DerivedCategory.isIso_iff _ f).mpr
  intro n
  have h : IsIso ((F.mapDerivedCategory ⋙
      DerivedCategory.homologyFunctor (SheafOfModules.{u} (siteModuleRings R)) n).map f) :=
    by
      change IsIso ((DerivedCategory.homologyFunctor _ n).map
        (F.mapDerivedCategory.map f))
      infer_instance
  have : IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (siteModuleRings B)) n ⋙ F).map f) :=
    (NatIso.isIso_map_iff (F.mapDerivedCategoryHomologyFunctorIso n) f).mpr h
  change IsIso (F.map ((DerivedCategory.homologyFunctor _ n).map f)) at this
  exact isIso_of_reflects_iso _ F

private theorem locallyDerivedRingedIdealComplete_of_iso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (I : RingedSiteIdeal R)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (siteModuleRings R))]
    [∀ U : C, HasDerivedCategory.{w}
      (SheafOfModules.{u} (siteModuleRings (R.over U)))]
    {M N : ringedSiteDerived R} (e : M ≅ N)
    (hN : IsLocallyDerivedRingedIdealComplete R I.module I.inclusion N) :
    IsLocallyDerivedRingedIdealComplete R I.module I.inclusion M := by
  intro U f hf
  exact (hN U f hf).of_iso ((derivedInternalHom (J.over U) (R.over U)).mapIso
    ((Iso.refl _).prod ((ringedDerivedRestriction R U).mapIso e)))

set_option backward.isDefEq.respectTransparency false in
/-- The specified exact derived restriction preserves and reflects local completeness.
Source: Stacks Project, Algebraization, Tag 099C
(blueprint: lem-weil-pbc-flat-ringed-ideal-complete-equivalence).
Proof: the extension ideal's unique local-membership description is the hypothesis of
restrictScalars_locallyDerivedComplete_iff. Identify its image of the chosen complex
representative with the exact derived functor using mapDerivedCategoryFactors and the
representative isomorphism. Local completeness is invariant under these isomorphisms
since each of its defining internal-Hom objects is functorial. -/
theorem siteDerivedRestrictScalars_locallyDerivedComplete_iff
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) (I : RingedSiteIdeal R)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (siteModuleRings R))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (siteModuleRings B))]
    [∀ U : C, HasDerivedCategory.{w}
      (SheafOfModules.{u} (siteModuleRings (R.over U)))]
    [∀ U : C, HasDerivedCategory.{w}
      (SheafOfModules.{u} (siteModuleRings (B.over U)))]
    (M : ringedSiteDerived B) :
    IsLocallyDerivedRingedIdealComplete R I.module I.inclusion
        ((siteDerivedRestrictScalars φ).obj M) ↔
      IsLocallyDerivedRingedIdealComplete B
        (I.extension φ).module (I.extension φ).inclusion M := by
  let F := SheafOfModules.restrictScalars.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
  let := (siteRestrictScalars_exact φ).1
  let := (siteRestrictScalars_exact φ).2
  have hIB : ∀ (U : C) (b : B.obj.obj (Opposite.op U)),
      b ∈ (I.extension φ).sections U ↔ ∃ S : Sieve U, S ∈ J U ∧
        ∀ (V : C) (g : V ⟶ U), S g →
          B.obj.map g.op b ∈ Ideal.map (φ.hom.app (Opposite.op V)).hom (I.sections V) := by
    intro U b
    have he (V : C) :
        Ideal.map (φ.hom.app (Opposite.op V)).hom (I.sections V) =
          Ideal.span (Set.range (fun a : I.sections V ↦ φ.hom.app (Opposite.op V) a)) := by
      unfold Ideal.map
      rw [Set.image_eq_range]
      rfl
    simp_rw [he]
    exact (Classical.choose_spec (I.existsUnique_extension φ).exists) U b
  have h := restrictScalars_locallyDerivedComplete_iff J R B φ I (I.extension φ) hIB M
  let e : F.mapDerivedCategory.obj M ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj
        (DerivedCategory.Q.objPreimage M)) :=
    F.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso M).symm ≪≫
      F.mapDerivedCategoryFactors.app (DerivedCategory.Q.objPreimage M)
  exact ⟨fun hM ↦ h.mp
      (locallyDerivedRingedIdealComplete_of_iso R I e.symm hM),
    fun hM ↦ locallyDerivedRingedIdealComplete_of_iso R I e (h.mpr hM)⟩


/-- Restriction of scalars on the full subcategories of locally derived complete objects.
Source: Stacks Project, Algebraization, Tag 099I, first paragraph
(blueprint: lem-weil-pbc-flat-ringed-ideal-complete-equivalence).
This is the lift of the specified exact derived restriction, with no choices of objects. -/
noncomputable def siteCompleteRestrictScalars
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) (I : RingedSiteIdeal R)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (siteModuleRings R))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (siteModuleRings B))]
    [∀ U : C, HasDerivedCategory.{w}
      (SheafOfModules.{u} (siteModuleRings (R.over U)))]
    [∀ U : C, HasDerivedCategory.{w}
      (SheafOfModules.{u} (siteModuleRings (B.over U)))] :
    ObjectProperty.FullSubcategory
        (IsLocallyDerivedRingedIdealComplete B (I.extension φ).module (I.extension φ).inclusion) ⥤
      ObjectProperty.FullSubcategory
        (IsLocallyDerivedRingedIdealComplete R I.module I.inclusion) :=
  ObjectProperty.lift (IsLocallyDerivedRingedIdealComplete R I.module I.inclusion)
    (ObjectProperty.ι
      (IsLocallyDerivedRingedIdealComplete B (I.extension φ).module (I.extension φ).inclusion) ⋙
        siteDerivedRestrictScalars φ)
    (fun M ↦ (siteDerivedRestrictScalars_locallyDerivedComplete_iff φ I M.obj).mpr M.property)

/-- Restriction on locally derived complete objects is conservative.
Source: Stacks Project, Algebraization, Tag 099I, first paragraph
(blueprint: lem-weil-pbc-flat-ringed-ideal-complete-equivalence).
Proof: compose with the fully faithful inclusion into the ambient derived category.
This composite is the ambient conservative restriction after a fully faithful inclusion,
and hence reflects isomorphisms. Reflection by the composite implies reflection by the
restriction functor itself. -/
theorem siteCompleteRestrictScalars_reflectsIsomorphisms
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) (I : RingedSiteIdeal R)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (siteModuleRings R))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (siteModuleRings B))]
    [∀ U : C, HasDerivedCategory.{w}
      (SheafOfModules.{u} (siteModuleRings (R.over U)))]
    [∀ U : C, HasDerivedCategory.{w}
      (SheafOfModules.{u} (siteModuleRings (B.over U)))] :
    (siteCompleteRestrictScalars φ I).ReflectsIsomorphisms := by
  have := siteDerivedRestrictScalars_reflectsIsomorphisms φ
  let P := IsLocallyDerivedRingedIdealComplete R I.module I.inclusion
  have : (siteCompleteRestrictScalars φ I ⋙ ObjectProperty.ι P).ReflectsIsomorphisms :=
    inferInstanceAs ((ObjectProperty.ι (IsLocallyDerivedRingedIdealComplete B
      (I.extension φ).module (I.extension φ).inclusion) ⋙
        siteDerivedRestrictScalars φ).ReflectsIsomorphisms)
  exact reflectsIsomorphisms_of_comp (siteCompleteRestrictScalars φ I)
    (ObjectProperty.ι (IsLocallyDerivedRingedIdealComplete R I.module I.inclusion))


/-- The categorical last step of the complete-restriction equivalence argument.
Source: Stacks Project, Algebraization, Tag 099I, final paragraph
(blueprint: lem-weil-pbc-flat-ringed-ideal-complete-equivalence).
Proof: reflection of isomorphisms makes every component of beta invertible.
Use beta as the unit and the inverse of alpha as the counit; the standard
adjointification of an equivalence supplies the triangle identity. Its forward
functor is the explicit complete restriction, whose ambient composite is the
specified exact derived restriction. -/
theorem siteCompleteRestrictScalars_equivalence_of_inverse
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) (I : RingedSiteIdeal R)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (siteModuleRings R))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (siteModuleRings B))]
    [∀ U : C, HasDerivedCategory.{w}
      (SheafOfModules.{u} (siteModuleRings (R.over U)))]
    [∀ U : C, HasDerivedCategory.{w}
      (SheafOfModules.{u} (siteModuleRings (B.over U)))]
    (F : ObjectProperty.FullSubcategory
        (IsLocallyDerivedRingedIdealComplete R I.module I.inclusion) ⥤
      ObjectProperty.FullSubcategory
        (IsLocallyDerivedRingedIdealComplete B (I.extension φ).module (I.extension φ).inclusion))
    (α : 𝟭 _ ≅ F ⋙ siteCompleteRestrictScalars φ I)
    (β : 𝟭 _ ⟶ siteCompleteRestrictScalars φ I ⋙ F)
    (hβ : ∀ M, IsIso ((siteCompleteRestrictScalars φ I).map (β.app M))) :
    ∃ e : ObjectProperty.FullSubcategory
        (IsLocallyDerivedRingedIdealComplete B (I.extension φ).module (I.extension φ).inclusion) ≌
        ObjectProperty.FullSubcategory
          (IsLocallyDerivedRingedIdealComplete R I.module I.inclusion),
      Nonempty (e.functor ⋙
        ObjectProperty.ι (IsLocallyDerivedRingedIdealComplete R I.module I.inclusion) ≅
        ObjectProperty.ι
          (IsLocallyDerivedRingedIdealComplete B (I.extension φ).module (I.extension φ).inclusion) ⋙
          siteDerivedRestrictScalars φ) := by
  have := siteCompleteRestrictScalars_reflectsIsomorphisms φ I
  have : ∀ M, IsIso (β.app M) := by
    intro M
    have := hβ M
    exact isIso_of_reflects_iso _ (siteCompleteRestrictScalars φ I)
  have : IsIso β := NatIso.isIso_of_isIso_app β
  let e := Equivalence.mk (siteCompleteRestrictScalars φ I) F (asIso β) α.symm
  exact ⟨e, ⟨Iso.refl _⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- An ambient coefficient-Hom construction with its augmentation comparison gives
an equivalence on complete objects.
Source: Stacks Project, Algebraization, Tag 099I, the last two paragraphs
(blueprint: lem-weil-pbc-flat-ringed-ideal-complete-equivalence).
Proof: the extended Cech reflector theorem makes the completion of every object
complete. Transport along theta and reflect completeness by restriction to lift F
to the complete subcategories. On a complete object the completion unit is invertible;
composing it with theta inverse gives the R-side natural isomorphism. Lift beta to
the B-side subcategory. Its restriction is invertible because its composite with
theta is the completion unit. Apply the conservative equivalence assembly lemma. -/
theorem siteCompleteRestrictScalars_equivalence_of_completion
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) (I : RingedSiteIdeal R)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (siteModuleRings R))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (siteModuleRings B))]
    [∀ U : C, HasDerivedCategory.{w}
      (SheafOfModules.{u} (siteModuleRings (R.over U)))]
    [∀ U : C, HasDerivedCategory.{w}
      (SheafOfModules.{u} (siteModuleRings (B.over U)))]
    (hI : SheafOfModules.IsFiniteType.{u, u, u} I.module)
    (K : ringedSiteComplex R) (ε : K ⟶ ringedSiteRingComplex R)
    (hK : HasLocalExtendedCechDescription R I.module I.inclusion K ε)
    (F : ringedSiteDerived R ⥤ ringedSiteDerived B)
    (θ : F ⋙ siteDerivedRestrictScalars φ ≅ ringedCechCompletionFunctor R K)
    (β : 𝟭 (ringedSiteDerived B) ⟶ siteDerivedRestrictScalars φ ⋙ F)
    (hβ : ∀ M : ringedSiteDerived B,
      (siteDerivedRestrictScalars φ).map (β.app M) ≫
          θ.hom.app ((siteDerivedRestrictScalars φ).obj M) =
        ringedCechCompletionUnit R K ε ((siteDerivedRestrictScalars φ).obj M)) :
    ∃ e : ObjectProperty.FullSubcategory
        (IsLocallyDerivedRingedIdealComplete B (I.extension φ).module (I.extension φ).inclusion) ≌
        ObjectProperty.FullSubcategory
          (IsLocallyDerivedRingedIdealComplete R I.module I.inclusion),
      Nonempty (e.functor ⋙
        ObjectProperty.ι (IsLocallyDerivedRingedIdealComplete R I.module I.inclusion) ≅
        ObjectProperty.ι
          (IsLocallyDerivedRingedIdealComplete B (I.extension φ).module (I.extension φ).inclusion) ⋙
          siteDerivedRestrictScalars φ) := by
  let := hI
  have : Mono I.inclusion := by
    constructor
    intro Z f g h
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    exact congrArg (fun k ↦ k.val.app X z) h
  let P : ObjectProperty (ringedSiteDerived R) :=
    IsLocallyDerivedRingedIdealComplete R I.module I.inclusion
  let Q : ObjectProperty (ringedSiteDerived B) := IsLocallyDerivedRingedIdealComplete B
    (I.extension φ).module (I.extension φ).inclusion
  let r := siteDerivedRestrictScalars φ
  let s := siteCompleteRestrictScalars φ I
  obtain ⟨hcomplete, hnatural, _, hunit⟩ :=
    ringedExtendedCech_reflector_properties J R I.module I.inclusion K ε hK
  have hF (E : ringedSiteDerived R) : Q (F.obj E) :=
    (siteDerivedRestrictScalars_locallyDerivedComplete_iff φ I (F.obj E)).mp
      (locallyDerivedRingedIdealComplete_of_iso R I (θ.app E) (hcomplete E))
  let G : P.FullSubcategory ⥤ Q.FullSubcategory :=
    ObjectProperty.lift Q (ObjectProperty.ι P ⋙ F) (fun E ↦ hF E.obj)
  have hη (E : P.FullSubcategory) :
      IsIso (ringedCechCompletionUnit R K ε E.obj) := hunit E.obj E.property
  let α : 𝟭 P.FullSubcategory ≅ G ⋙ s :=
    NatIso.ofComponents (fun E ↦ ObjectProperty.isoMk P
      (asIso (ringedCechCompletionUnit R K ε E.obj) ≪≫ (θ.app E.obj).symm)) (by
        intro E E' f
        apply ObjectProperty.hom_ext
        change f.hom ≫ (ringedCechCompletionUnit R K ε E'.obj ≫ θ.inv.app E'.obj) =
          (ringedCechCompletionUnit R K ε E.obj ≫ θ.inv.app E.obj) ≫
            r.map (F.map f.hom)
        rw [← Category.assoc, ← hnatural E.obj E'.obj f.hom, Category.assoc]
        rw [θ.inv.naturality f.hom]
        exact (Category.assoc _ _ _).symm)
  let β' : 𝟭 Q.FullSubcategory ⟶ s ⋙ G :=
    { app M := ObjectProperty.homMk (β.app M.obj)
      naturality M N f := by
        apply ObjectProperty.hom_ext
        exact β.naturality f.hom }
  apply siteCompleteRestrictScalars_equivalence_of_inverse φ I G α β'
  intro M
  apply (ObjectProperty.isIso_hom_iff _).mp
  change IsIso (r.map (β.app M.obj))
  have : IsIso (ringedCechCompletionUnit R K ε (r.obj M.obj)) :=
    hunit _ (s.obj M).property
  have : IsIso (r.map (β.app M.obj) ≫ θ.hom.app (r.obj M.obj)) := by
    rw [hβ]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (θ.hom.app (r.obj M.obj))

/-- Restriction of scalars along a flat ring-sheaf map which is an isomorphism modulo a
locally finitely generated ideal induces an equivalence of the locally derived complete
full subcategories. The natural isomorphism in the conclusion identifies the equivalence
with the specified derived restriction functor on the ambient categories.

Source: Stacks Project, Algebraization, Tags 099I and 0999
(blueprint: lem-weil-pbc-flat-ringed-ideal-complete-equivalence).

Proof:
1. Restriction of scalars is exact and conservative, since its underlying additive sheaf
is unchanged. It therefore induces the stated derived functor. By
`lem-weil-pbc-restriction-local-completeness`, it preserves and reflects local completeness.
2. Choose the augmented extended Cech model `K → R[0]` from
`lem-weil-pbc-extended-cech-completion-model`. Flatness makes termwise tensoring with `B`
exact, giving `K_B → B[0]` and `u : K → r K_B`. On every generating slice, localization
commutes with tensor: `(a/f^n) ⊗ b ↦ φ(a)b/φ(f)^n` with inverse
`b/φ(f)^n ↦ (1/f^n) ⊗ b`. Finite products in this model are finite direct sums.
Slice restriction is exact (`lem-weil-pbc-site-restriction-exact`) and preserves quotients;
flatness restricts (`lem-weil-pbc-slice-restriction-flat`). Apply
`lem-weil-pbc-flat-extended-cech-comparison` locally to deduce that `u` is a quasi-isomorphism.
3. Define `F(E)` by the Hom complex from `r K_B` into the functorial K-injective replacement
of a representative of `E`, with action `(b h)(k) = h(bk)`. This action commutes with the
Hom differential and with restrictions. Naturality and two-out-of-three show replacement
maps preserve quasi-isomorphisms; `lem-pur-rhom-well-defined` then makes the Hom maps
quasi-isomorphisms. Thus the construction descends to a functor `D(R) → D(B)`.
4. Precomposition with `u` identifies `r F(E)` with `RHom_R(K,E)`. For complete `E`, the
completion unit identifies this with `E`, naturally. Completeness is reflected by `r`,
so `F` also restricts to the complete subcategories.
5. For complete `M` over `B`, send a homogeneous `m` to the cochain
`k ↦ q(ε_B(k)m)`, zero off degree zero of `k`. This is a chain map because `ε_B d_K = 0`
and `q` is a chain map. It is `B`-linear under the action in step 3, and natural. After
precomposition with `u`, it is exactly the completion unit of `r M`. Hence its restriction
is an isomorphism by step 4; conservativity of restriction makes it an isomorphism over
`B`. These two natural isomorphisms exhibit the equivalence asserted here. -/
theorem flat_ringed_ideal_complete_equivalence
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) (I : RingedSiteIdeal R)
    [HasDerivedCategory.{w} (ringedSiteModules.{u} (siteModuleRings R))]
    [HasDerivedCategory.{w} (ringedSiteModules.{u} (siteModuleRings B))]
    [∀ U : C, HasDerivedCategory.{w}
      (ringedSiteModules.{u} (siteModuleRings (R.over U)))]
    [∀ U : C, HasDerivedCategory.{w}
      (ringedSiteModules.{u} (siteModuleRings (B.over U)))]
    (hI : SheafOfModules.IsFiniteType.{u, u, u} I.module)
    (hflat : SheafOfModules.IsFlat
      ((SheafOfModules.restrictScalars.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
          (SheafOfModules.unit (siteModuleRings B))))
    (hquot : I.IsQuotientIso φ) :
    ∃ e : ObjectProperty.FullSubcategory
        (IsLocallyDerivedRingedIdealComplete B (I.extension φ).module (I.extension φ).inclusion) ≌
        ObjectProperty.FullSubcategory
          (IsLocallyDerivedRingedIdealComplete R I.module I.inclusion),
      Nonempty (e.functor ⋙
        ObjectProperty.ι (IsLocallyDerivedRingedIdealComplete R I.module I.inclusion) ≅
        ObjectProperty.ι
          (IsLocallyDerivedRingedIdealComplete B (I.extension φ).module (I.extension φ).inclusion) ⋙
          siteDerivedRestrictScalars φ) := by
  sorry

end CategoryTheory
