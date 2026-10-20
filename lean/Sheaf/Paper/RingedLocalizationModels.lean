/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.CategoryTheory.RingedSectionLocalization
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.Algebra.Homology.RingedInternalHomExactRestriction
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree
public import Sheaf.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Sheaf.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatCoproduct
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Mathlib.RingTheory.Localization.BaseChange
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor
import Mathlib.RingTheory.Flat.Localization

/-!
# Localization complexes and derived internal Hom on a ringed site

Source: Stacks Project, Cohomology on Sites, Tags 08J9 and 08JB;
Algebraization of Formal Spaces, Tag 0996
(blueprint: lem-weil-pbc-ringed-localization-rhom-calculus).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}

/-- Transparent size convention for the existing module category.
Source: Stacks 08J9 (blueprint: lem-weil-pbc-ringed-localization-rhom-calculus). -/
abbrev localizationModules (R : Sheaf J CommRingCat.{u}) :=
  ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)

/-- The existing unbounded derived category, at its standard localization size.
Source: Stacks 08J9 (blueprint: lem-weil-pbc-ringed-localization-rhom-calculus). -/
abbrev localizationDerived (R : Sheaf J CommRingCat.{u}) :=
  @DerivedCategory (localizationModules R) _ _
    (HasDerivedCategory.standard (localizationModules R))

/-- The existing localization functor with the same size convention.
Source: Stacks 08J9 (blueprint: lem-weil-pbc-ringed-localization-rhom-calculus). -/
abbrev localizationQ (R : Sheaf J CommRingCat.{u}) :
    CochainComplex (localizationModules R) ℤ ⥤ localizationDerived R :=
  @DerivedCategory.Q (localizationModules R) _ _
    (HasDerivedCategory.standard (localizationModules R))

/-- The recorded derived internal Hom; this is only an explicit universe specialization.
Source: Stacks 08J9 (blueprint: lem-weil-pbc-ringed-localization-rhom-calculus). -/
abbrev localizationRHom (R : Sheaf J CommRingCat.{u}) :
    (localizationDerived R)ᵒᵖ × localizationDerived R ⥤ localizationDerived R :=
  @derivedInternalHom C _ J R (HasDerivedCategory.standard (localizationModules R))

/-- Termwise slice restriction using the recorded exact restriction functor.
Source: Stacks 08JB (blueprint: lem-weil-pbc-ringed-localization-rhom-calculus). -/
abbrev localizationComplexRestriction (R : Sheaf J CommRingCat.{u}) (U : C) :
    CochainComplex (localizationModules R) ℤ ⥤
      CochainComplex (localizationModules (R.over U)) ℤ :=
  (SheafOfModules.overFunctor.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) U).mapHomologicalComplex (.up ℤ)

/-- The induced exact functor on derived categories, with explicit standard sizes.
Source: Stacks 08JB (blueprint: lem-weil-pbc-ringed-localization-rhom-calculus). -/
abbrev localizationDerivedRestriction (R : Sheaf J CommRingCat.{u}) (U : C) :
    localizationDerived R ⥤ localizationDerived (R.over U) :=
  haveI := ringedSite_overFunctor_additive J R U
  haveI := ringedSite_overFunctor_limits J R U
  haveI := ringedSite_overFunctor_colimits J R U
  @Functor.mapDerivedCategory
    (localizationModules R) _ _ (HasDerivedCategory.standard (localizationModules R))
    (localizationModules (R.over U)) _ _
    (HasDerivedCategory.standard (localizationModules (R.over U)))
    (SheafOfModules.overFunctor.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) U) _ _ _

/-- A bounded complex with finite localization sums in every degree. The empty sum is allowed.
Source: Stacks 0996, localization specialization of 08J9
(blueprint: lem-weil-pbc-ringed-localization-rhom-calculus). -/
def IsBoundedLocalizationComplex (R : Sheaf J CommRingCat.{u})
    (P : CochainComplex (localizationModules R) ℤ) : Prop :=
  (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n)) ∧
    ∀ n : ℤ, ∃ (k : ℕ) (g : Fin k → (R.obj ⋙ forget CommRingCat.{u}).sections),
      Nonempty (P.X n ≅ ∐ (fun i : Fin k ↦ ringedSectionLocalization R (g i)))

/-- Ordinary tensor by a sheaf in degree zero: terms and differentials are tensorized.
Source: Stacks 0996, 08J9
(blueprint: lem-weil-pbc-ringed-localization-rhom-calculus). -/
def localizationTensorComplex (R : Sheaf J CommRingCat.{u}) (S : localizationModules R) :
    CochainComplex (localizationModules R) ℤ ⥤
      CochainComplex (localizationModules R) ℤ :=
  haveI := SheafOfModules.monoidalCategory R
  haveI := Classical.choice (SheafOfModules.tensorClosed R).1
  (@tensorLeft (localizationModules R) _
    (SheafOfModules.monoidalCategory R) S).mapHomologicalComplex
    (.up ℤ)

/-- The actual coefficient localization on the slice, using the recorded fraction presheaf.
Source: Stacks 0996 (blueprint: lem-weil-pbc-ringed-localization-rhom-calculus). -/
abbrev localizationSliceCoefficient (R : Sheaf J CommRingCat.{u}) (U : C)
    (f : R.obj.obj (op U)) : localizationModules (R.over U) :=
  ringedSectionLocalization (R.over U) (ringedSliceSection R U f)

/-- The ordinary localized complex P_f, including its tensor differential.
Source: Stacks 0996, 08J9
(blueprint: lem-weil-pbc-ringed-localization-rhom-calculus). -/
abbrev localizationSliceComplex (R : Sheaf J CommRingCat.{u}) (U : C)
    (f : R.obj.obj (op U)) :
    CochainComplex (localizationModules R) ℤ ⥤
      CochainComplex (localizationModules (R.over U)) ℤ :=
  localizationComplexRestriction R U ⋙
    localizationTensorComplex (R.over U) (localizationSliceCoefficient R U f)

/-- The coefficient localization regarded as an object of the unbounded derived category.
Source: Stacks 08J9 (blueprint: lem-weil-pbc-ringed-localization-rhom-calculus). -/
abbrev localizationSliceDerivedCoefficient (R : Sheaf J CommRingCat.{u}) (U : C)
    (f : R.obj.obj (op U)) : localizationDerived (R.over U) :=
  (localizationQ (R.over U)).obj
    ((HomologicalComplex.single (localizationModules (R.over U)) (.up ℤ) 0).obj
      (localizationSliceCoefficient R U f))

/-- Further slice restriction on the same existing derived categories.
Source: Stacks 08JB (blueprint: lem-weil-pbc-ringed-localization-rhom-calculus). -/
abbrev localizationDerivedOverMap (R : Sheaf J CommRingCat.{u}) {U V : C} (a : V ⟶ U) :
    localizationDerived (R.over U) ⥤ localizationDerived (R.over V) :=
  haveI := ringedSite_overMap_additive J R a
  haveI := ringedSite_overMap_limits J R a
  haveI := ringedSite_overMap_colimits J R a
  @Functor.mapDerivedCategory
    (localizationModules (R.over U)) _ _
    (HasDerivedCategory.standard (localizationModules (R.over U)))
    (localizationModules (R.over V)) _ _
    (HasDerivedCategory.standard (localizationModules (R.over V)))
    (SheafOfModules.overMap.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) a) _ _ _

/-- The canonical relocalization comparison, induced by the sectionwise identity.
Source: Stacks 08JB, Modules on Sites 04IX
(blueprint: lem-weil-pbc-ringed-localization-rhom-calculus). -/
def localizationRestrictionCompIso (R : Sheaf J CommRingCat.{u}) {U V : C} (a : V ⟶ U) :
    localizationDerivedRestriction R U ⋙ localizationDerivedOverMap R a ≅
      localizationDerivedRestriction R V :=
  haveI := HasDerivedCategory.standard (localizationModules R)
  haveI := HasDerivedCategory.standard (localizationModules (R.over U))
  haveI := HasDerivedCategory.standard (SheafOfModules.{u}
    (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).over U))
  haveI := HasDerivedCategory.standard (localizationModules (R.over V))
  haveI := HasDerivedCategory.standard (SheafOfModules.{u}
    (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).over V))
  haveI := ringedSite_overFunctor_additive J R U
  haveI := ringedSite_overFunctor_limits J R U
  haveI := ringedSite_overFunctor_colimits J R U
  haveI := ringedSite_overFunctor_additive J R V
  haveI := ringedSite_overFunctor_limits J R V
  haveI := ringedSite_overFunctor_colimits J R V
  haveI := ringedSite_overMap_additive J R a
  haveI := ringedSite_overMap_limits J R a
  haveI := ringedSite_overMap_colimits J R a
  (@Functor.mapDerivedCategoryCompIso
    (localizationModules R) (localizationModules (R.over U)) (localizationModules (R.over V))
    _ _ _ _ _ _
    (HasDerivedCategory.standard (localizationModules R))
    (HasDerivedCategory.standard (localizationModules (R.over U)))
    (HasDerivedCategory.standard (localizationModules (R.over V)))
    (SheafOfModules.overFunctor.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) U)
    (SheafOfModules.overMap.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) a) _ _ _ _ _ _).symm ≪≫
    @Functor.mapDerivedCategoryNatIso
      (localizationModules R) (localizationModules (R.over V)) _ _ _ _
      (HasDerivedCategory.standard (localizationModules R))
      (HasDerivedCategory.standard (localizationModules (R.over V))) _ _ _ _ _ _ _ _
      (SheafOfModules.overFunctorMap
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) a)

private theorem localization_isFlat (R : Sheaf J CommRingCat.{u})
    (g : (R.obj ⋙ forget CommRingCat.{u}).sections) :
    SheafOfModules.IsFlat (ringedSectionLocalization R g) := by
  let O := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R
  let F := ringedSectionLocalizationPresheaf R g
  have hflat (V : Cᵒᵖ) : Module.Flat (R.obj.obj V) (F.obj V) := by
    dsimp [F, ringedSectionLocalizationPresheaf, ringedSectionLocalizationCarrier]
    infer_instance
  have hF : PreservesFiniteLimits (tensorRight F) := by
    constructor
    intro K _ _
    have (V : Cᵒᵖ) : Module.Flat (R.obj.obj V) (F.obj V) := hflat V
    exact ⟨⟨fun hc ↦ ⟨PresheafOfModules.evaluationJointlyReflectsLimits _ _
      (fun V ↦ isLimitOfPreserves
        (tensorRight (show ModuleCat (R.obj.obj V) from F.obj V))
        (isLimitOfPreserves (PresheafOfModules.evaluation O.obj V) hc))⟩⟩⟩
  have : Presheaf.IsLocallyInjective J (𝟙 O.obj) :=
    Presheaf.isLocallyInjective_of_injective J _ (fun _ ↦ Function.injective_id)
  have : Presheaf.IsLocallySurjective J (𝟙 O.obj) :=
    Presheaf.isLocallySurjective_of_surjective J _ (fun _ ↦ Function.surjective_id)
  exact (PresheafOfModules.isFlat_sheafification_obj (R := R) (𝟙 O.obj) F hF).2

private theorem boundedLocalization_isFlat (R : Sheaf J CommRingCat.{u})
    (P : CochainComplex (localizationModules R) ℤ) (hP : IsBoundedLocalizationComplex R P)
    (n : ℤ) : SheafOfModules.IsFlat (P.X n) := by
  classical
  let := SheafOfModules.monoidalCategory R
  obtain ⟨k, g, ⟨e⟩⟩ := hP.2 n
  let F (i : Fin k) := ringedSectionLocalization R (g i)
  -- The flat-coproduct API uses an index type in the coefficient universe.
  have hf := SheafOfModules.isFlat_coproduct R
    (fun i : ULift.{u} (Fin k) ↦ F i.down)
    (fun i ↦ localization_isFlat R (g i.down))
  let e' : (∐ fun i : ULift.{u} (Fin k) ↦ F i.down) ≅ ∐ F :=
    Sigma.whiskerEquiv Equiv.ulift (fun _ ↦ Iso.refl _)
  exact (exactFunctor _ _).prop_of_iso
    ((curriedTensor _).flip.mapIso (e' ≪≫ e.symm)) hf

/-- The degree-zero coefficient localization is K-flat.
Source: Stacks 00HT and 06YQ
(blueprint: lem-weil-pbc-ringed-localization-complex-models).
Proof: Localization is flat, zero modules are flat, and the degree-zero complex
is bounded above by zero. Apply bounded-above flat K-flatness. -/
theorem localizationSliceCoefficient_kflat (R : Sheaf J CommRingCat.{u}) (U : C)
    (f : R.obj.obj (op U)) :
    CochainComplex.IsAcyclicTensorKFlat
      ((HomologicalComplex.single (localizationModules (R.over U)) (.up ℤ) 0).obj
        (localizationSliceCoefficient R U f)) := by
  let := SheafOfModules.monoidalCategory (R.over U)
  apply CochainComplex.isKFlat_of_boundedAbove_flat
  · exact ⟨0, fun n hn ↦ HomologicalComplex.isZero_single_obj_X _ _ _ _ (ne_of_gt hn)⟩
  · intro n
    by_cases hn : n = 0
    · subst n
      exact (exactFunctor _ _).prop_of_iso
        ((curriedTensor _).flip.mapIso
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0
            (localizationSliceCoefficient R U f)).symm)
        (localization_isFlat (R.over U) (ringedSliceSection R U f))
    · have hz := HomologicalComplex.isZero_single_obj_X (.up ℤ) 0
        (localizationSliceCoefficient R U f) n hn
      let := Classical.choice (SheafOfModules.tensorClosed (R.over U)).1
      exact (ObjectProperty.flat_of_isZero hz).tensorRight

/-- Bounded localization complexes and their coefficient localizations admit identity
K-flat replacements. The ordinary tensor complex is the total tensor with the coefficient
in degree zero, so it represents the derived tensor specified in the node.

Source: Stacks 08J9 and 0996
(blueprint: lem-weil-pbc-ringed-localization-rhom-calculus).
Proof:
1. Sectionwise localization is flat (lem-weil-pbc-localization-flat). Evaluation jointly
   reflects limits, so tensor with its presheaf preserves finite limits. Apply
   lem-pc-sites-modules-sheafification-flat to obtain a flat localization sheaf.
2. Apply lem-pc-sites-modules-coproduct-flat, including for the empty sum.
   Slice restriction preserves flatness
   (lem-weil-pbc-slice-restriction-flat). Bounded-above flat complexes are K-flat
   (lem-pc-bounded-above-flat-kflat-site).
3. The degree-zero coefficient complex is K-flat for the same reason. Its total tensor
   with restricted P has only the summand with first degree zero. The summand inclusions
   identify the differential with 1 tensor d_P (def-pc-tensor-complex-sheaves).
4. Consequently the identity K-flat replacement computes the stated derived tensor.
No bound on the target complex occurs. -/
theorem ringedLocalization_kflat_models (R : Sheaf J CommRingCat.{u})
    (P : CochainComplex (localizationModules R) ℤ) (hP : IsBoundedLocalizationComplex R P)
    (U : C) (f : R.obj.obj (op U)) :
    CochainComplex.IsAcyclicTensorKFlat ((localizationComplexRestriction R U).obj P) ∧
    CochainComplex.IsAcyclicTensorKFlat
      ((HomologicalComplex.single (localizationModules (R.over U)) (.up ℤ) 0).obj
        (localizationSliceCoefficient R U f)) ∧
    Nonempty (CochainComplex.mapBifunctor
      ((HomologicalComplex.single (localizationModules (R.over U)) (.up ℤ) 0).obj
        (localizationSliceCoefficient R U f))
      ((localizationComplexRestriction R U).obj P)
      (@curriedTensor (localizationModules (R.over U)) _
        (SheafOfModules.monoidalCategory (R.over U))) ≅
      (localizationSliceComplex R U f).obj P) := by
  let := SheafOfModules.monoidalCategory (R.over U)
  have hflat (n : ℤ) :
      SheafOfModules.IsFlat (((localizationComplexRestriction R U).obj P).X n) :=
    SheafOfModules.isFlat_over (P.X n) U (boundedLocalization_isFlat R P hP n)
  have hb : ∃ b : ℤ, ∀ n : ℤ, b < n →
      IsZero (((localizationComplexRestriction R U).obj P).X n) := by
    obtain ⟨a, b, h⟩ := hP.1
    refine ⟨b, fun n hn ↦ ?_⟩
    exact (SheafOfModules.overFunctor
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) U).map_isZero
        (h n (Or.inr hn))
  refine ⟨CochainComplex.isKFlat_of_boundedAbove_flat _ hb hflat, ?_, ?_⟩
  · exact localizationSliceCoefficient_kflat R U f
  · exact ⟨CochainComplex.mapBifunctorSingle₁Iso
      (curriedTensor (localizationModules (R.over U)))
      (localizationSliceCoefficient R U f) ((localizationComplexRestriction R U).obj P)⟩

private def localizationTensorEquiv {A : Type u} [CommRing A] (f g : A) :
    TensorProduct A (Localization.Away f) (Localization.Away g) ≃ₐ[A]
      Localization.Away (f * g) := by
  letI : IsLocalization.Away (f * g)
      (TensorProduct A (Localization.Away f) (Localization.Away g)) :=
    IsLocalization.Away.mul' (Localization.Away f) _ f g
  exact IsLocalization.algEquiv (Submonoid.powers (f * g)) _ _

private theorem localizationMap_algebraMap (R : Sheaf J CommRingCat.{u})
    (s : (R.obj ⋙ forget CommRingCat.{u}).sections) {X Y : Cᵒᵖ} (a : X ⟶ Y) :
    (ringedSectionLocalizationMap R s a).comp (algebraMap _ _) =
      (algebraMap _ _).comp (R.obj.map a).hom := by
  ext x
  exact IsLocalization.Away.lift_eq (R := R.obj.obj X) (s.val X)
    (ringedSectionLocalization_isUnit R s a) x

private def localizationPresheafTensorIso (R : Sheaf J CommRingCat.{u})
    (g h k : (R.obj ⋙ forget CommRingCat.{u}).sections)
    (hk : ∀ X, (k.val X : R.obj.obj X) = g.val X * h.val X) :
    (ringedSectionLocalizationPresheaf R g) ⊗ (ringedSectionLocalizationPresheaf R h) ≅
      ringedSectionLocalizationPresheaf R k := by
  let F := ringedSectionLocalizationPresheaf R g
  let G := ringedSectionLocalizationPresheaf R h
  let e (X : Cᵒᵖ) :
      TensorProduct (R.obj.obj X) (ringedSectionLocalizationCarrier R g X)
        (ringedSectionLocalizationCarrier R h X) ≃ₐ[R.obj.obj X]
          ringedSectionLocalizationCarrier R k X := by
    change TensorProduct (R.obj.obj X) (Localization.Away (M := R.obj.obj X) (g.val X))
      (Localization.Away (M := R.obj.obj X) (h.val X)) ≃ₐ[R.obj.obj X]
        Localization.Away (M := R.obj.obj X) (k.val X)
    rw [hk X]
    exact localizationTensorEquiv _ _
  refine PresheafOfModules.isoMk (fun X ↦ (e X).toLinearEquiv.toModuleIso) ?_
  intro X Y a
  let m := Algebra.TensorProduct.mapRingHom (R.obj.map a).hom
    (ringedSectionLocalizationMap R g a) (ringedSectionLocalizationMap R h a)
    (localizationMap_algebraMap R g a) (localizationMap_algebraMap R h a)
  have hm : (e Y).toRingHom.comp m =
      (ringedSectionLocalizationMap R k a).comp (e X).toRingHom := by
    let : IsLocalization.Away (R := R.obj.obj X) ((g.val X : R.obj.obj X) * h.val X)
        (TensorProduct (R.obj.obj X) (ringedSectionLocalizationCarrier R g X)
          (ringedSectionLocalizationCarrier R h X)) :=
      IsLocalization.Away.mul' (R := R.obj.obj X)
        (ringedSectionLocalizationCarrier R g X) _ (g.val X) (h.val X)
    apply IsLocalization.ringHom_ext (R := R.obj.obj X)
      (Submonoid.powers ((g.val X : R.obj.obj X) * h.val X))
    ext x
    change e Y (m (algebraMap (R.obj.obj X) _ x)) =
      ringedSectionLocalizationMap R k a (e X (algebraMap (R.obj.obj X) _ x))
    rw [(e X).commutes]
    have hm' : m (algebraMap (R.obj.obj X) _ x) =
        algebraMap (R.obj.obj Y)
          (TensorProduct (R.obj.obj Y) (ringedSectionLocalizationCarrier R g Y)
            (ringedSectionLocalizationCarrier R h Y)) (R.obj.map a x) := by
      change m ((algebraMap _ _ x) ⊗ₜ (1 : ringedSectionLocalizationCarrier R h X)) = _
      simp only [m, Algebra.TensorProduct.mapRingHom_tmul, map_one]
      rw [show ringedSectionLocalizationMap R g a (algebraMap _ _ x) =
        algebraMap _ _ (R.obj.map a x) from
        RingHom.congr_fun (localizationMap_algebraMap R g a) x]
      rfl
    rw [hm', (e Y).commutes]
    exact (RingHom.congr_fun (localizationMap_algebraMap R k a) x).symm
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  change e Y ((F ⊗ G).map a (x ⊗ₜ y)) =
    ringedSectionLocalizationMap R k a (e X (x ⊗ₜ y))
  change e Y (ringedSectionLocalizationMap R g a x ⊗ₜ
      ringedSectionLocalizationMap R h a y) = _
  change ringedSectionLocalizationCarrier R g X at x
  change ringedSectionLocalizationCarrier R h X at y
  have hh := RingHom.congr_fun hm (x ⊗ₜ y)
  change e Y (m (x ⊗ₜ y)) = ringedSectionLocalizationMap R k a (e X (x ⊗ₜ y)) at hh
  rw [show m (x ⊗ₜ y) = ringedSectionLocalizationMap R g a x ⊗ₜ
      ringedSectionLocalizationMap R h a y from
        Algebra.TensorProduct.mapRingHom_tmul _ _ _ _ _ x y] at hh
  exact hh

/-- Tensoring two coefficient localizations multiplies the denominators.
Source: Stacks 0996, proof of (3)
(blueprint: lem-weil-pbc-ringed-localization-rhom-calculus).
Proof: the sectionwise forward map sends (a/f^r) tensor (b/g^s) to
ab f^(k-r) g^(k-s)/(fg)^k for k at least r,s. The inverse sends c/(fg)^n to
(1/f^n) tensor (c/g^n). Moving scalars across the tensor proves the composites are
identities. These fraction formulas commute with all restriction ring maps. Sheafify
and apply lem-pc-sites-module-sheafification-tensor. Tensor distributes over each finite
sum because it is a left adjoint (lem-pc-sheaf-modules-tensor-closed). -/
theorem ringedLocalization_tensor_product (R : Sheaf J CommRingCat.{u}) (U : C)
    (f g : R.obj.obj (op U)) :
    Nonempty ((SheafOfModules.monoidalCategory (R.over U)).tensorObj
      (localizationSliceCoefficient R U f) (localizationSliceCoefficient R U g) ≅
      localizationSliceCoefficient R U (f * g)) := by
  let := SheafOfModules.monoidalCategory (R.over U)
  let O := (sheafCompose (J.over U) (forget₂ CommRingCat.{u} RingCat.{u})).obj (R.over U)
  let α := 𝟙 O.obj
  have : Presheaf.IsLocallyInjective (J.over U) α :=
    Presheaf.isLocallyInjective_of_injective _ _ (fun _ ↦ Function.injective_id)
  have : Presheaf.IsLocallySurjective (J.over U) α :=
    Presheaf.isLocallySurjective_of_surjective _ _ (fun _ ↦ Function.surjective_id)
  obtain ⟨e, _⟩ := PresheafOfModules.exists_sheafificationTensorIso (R := R.over U) α
  let F := ringedSectionLocalizationPresheaf (R.over U) (ringedSliceSection R U f)
  let G := ringedSectionLocalizationPresheaf (R.over U) (ringedSliceSection R U g)
  let p := localizationPresheafTensorIso (R.over U)
    (ringedSliceSection R U f) (ringedSliceSection R U g) (ringedSliceSection R U (f * g))
    (fun X ↦ (R.obj.map X.unop.hom.op).hom.map_mul f g)
  exact ⟨e.app (F, G) ≪≫ (PresheafOfModules.sheafification α).mapIso p⟩

end CategoryTheory
