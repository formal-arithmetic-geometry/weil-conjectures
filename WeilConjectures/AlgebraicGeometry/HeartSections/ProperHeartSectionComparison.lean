/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import WeilConjectures.SmoothPurity.ProEtaleWeaklyEtaleLocalization
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatNat
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationExact
import Mathlib.Algebra.Category.ModuleCat.Colimits
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunction
import WeilConjectures.CategoryTheory.Abelian.RightDerived.Comp
import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteKInjectiveResolutionsMixedUniverses
import all WeilConjectures.Algebra.Homology.Coefficient.CoefficientRestrictionSectionsAcyclic
import WeilConjectures.CategoryTheory.ProperBaseChange.ModuleAbelianEvaluationComparison
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.CategoryTheory.Sites.SheafCohomologyRightDerived
import Mathlib.CategoryTheory.Category.ULift

/-! # Higher direct images on affine weakly contractible sections

Source: blueprint sk-lem-proper-heart-continuity, proof paragraph 3; Stacks Tags
072W, 03FD and 0946 (blueprint: lem-sfb-proper-heart-section-comparison).
The full module direct image is derived before its scalars are forgotten.

## Main statements

* `properHeartSectionComparison`: the canonical natural section formula.
* `localizedSectionComparison`: its interpretation on the localized ringed site.
* `moduleAbelianSectionComparison`: its underlying abelian-sheaf interpretation.
* `condensedProperHeartSectionComparison`: the exact published internal-module functor.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u uC vC uD vD wC wD

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.HeartSections

variable {X Y : Scheme.{u}}

/-- Forget only the commutativity of a ring sheaf.
Source: Stacks 072W (blueprint: lem-sfb-proper-heart-section-comparison). -/
abbrev ringSheaf (A : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :=
  (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A

/-- The existing sectionwise module category, with the size convention of the small site.
Source: Stacks 03FD (blueprint: lem-sfb-proper-heart-section-comparison). -/
abbrev Modules (A : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :=
  ringedSiteModules.{u + 1} (ringSheaf A)

/-- Underlying section presheaf, retaining the original abelian section groups.
Source: Stacks 03FD (blueprint: lem-sfb-proper-heart-section-comparison). -/
abbrev sectionsPresheaf (A : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :=
  SheafOfModules.toSheaf.{u + 1} (ringSheaf A) ⋙
    sheafToPresheaf _ AddCommGrpCat.{u + 1}

/-- Evaluation of module sections at an object, followed by forgetting scalars.
Source: Stacks 072W (blueprint: lem-sfb-proper-heart-section-comparison). -/
abbrev sectionsAt (A : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (V : X.ProEt) :=
  sectionsPresheaf A ⋙ (evaluation X.ProEtᵒᵖ AddCommGrpCat.{u + 1}).obj (op V)

/-- Base change of pro-etale objects along an arbitrary scheme morphism.
Source: Stacks 072W (blueprint: lem-sfb-proper-heart-section-comparison). -/
abbrev baseChange (p : X ⟶ Y) := MorphismProperty.Over.pullback @WeaklyEtale ⊤ p

/-- The standard localization for abelian presheaves; it imposes no size equality on the site.
Source: the project size convention (blueprint: lem-sfb-proper-heart-section-comparison). -/
local instance presheafDerived (X : Scheme.{u}) :
    HasDerivedCategory.{u + 2} (X.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :=
  HasDerivedCategory.standard _

/-- Right-derived module sections, assembled as a presheaf in the section object.
Evaluation of presheaves is exact, so its value is right-derived section evaluation.
The scalar-forgetful functor is inside this definition only after section evaluation.
Source: Stacks 072W and 03FD (blueprint: lem-sfb-proper-heart-section-comparison). -/
def moduleCohomologyPresheaf
    (A : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) (q : ℤ) :
    Modules A ⥤ X.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  DerivedCategory.singleFunctor (Modules A) 0 ⋙
    (sectionsPresheaf A).rightDerivedFunctor ⋙
      DerivedCategory.homologyFunctor (X.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1}) q

/-- The test category includes every affine weakly contractible pro-etale object and
all morphisms between such objects, so a presheaf isomorphism states naturality in V.
Source: Stacks 0946 (blueprint: lem-sfb-proper-heart-section-comparison). -/
abbrev Tests (Y : Scheme.{u}) :=
  ObjectProperty.FullSubcategory (fun V : Y.ProEt ↦ IsAffine V.left ∧
    (Scheme.ProEt.topology Y).IsWeaklyContractible.{u + 1} V)

/-- The inclusion of the test category.
Source: Stacks 0946 (blueprint: lem-sfb-proper-heart-section-comparison). -/
abbrev testInclusion (Y : Scheme.{u}) : Tests Y ⥤ Y.ProEt :=
  ObjectProperty.ι _

/-- Restriction of abelian presheaves along a functor.
Source: Stacks 072W (blueprint: lem-sfb-proper-heart-section-comparison). -/
abbrev precompose {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (F : C ⥤ D) :=
  (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ AddCommGrpCat.{u + 1}).obj F.op

/-- Standard derived category of presheaves on the test category.
Source: the project size convention (blueprint: lem-sfb-proper-heart-section-comparison). -/
local instance testPresheafDerived (Y : Scheme.{u}) :
    HasDerivedCategory.{u + 2} ((Tests Y)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :=
  HasDerivedCategory.standard _

/-- The resolution comparison for right-derived module sections, evaluated at W.
It uses the canonical unbounded/classical comparison and the homology comparison for
exact presheaf evaluation.
Source: Stacks 072W (blueprint: lem-sfb-proper-heart-section-comparison). -/
def sectionResolutionIso
    (A : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (N : Modules A) (I : InjectiveResolution N) (n : ℕ) (W : X.ProEt) :
    ((moduleCohomologyPresheaf A (n : ℤ)).obj N).obj (op W) ≅
      (((sectionsAt A W).mapHomologicalComplex (.up ℕ)).obj I.cocomplex).homology n :=
  ((evaluation X.ProEtᵒᵖ AddCommGrpCat.{u + 1}).obj (op W)).mapIso
    (((sectionsPresheaf A).singleFunctorCompRightDerivedFunctorCompHomologyFunctorIso n).app N
      ≪≫ I.isoRightDerivedObj (sectionsPresheaf A) n) ≪≫
    (((((sectionsPresheaf A).mapHomologicalComplex (.up ℕ)).obj I.cocomplex).sc n).mapHomologyIso
      ((evaluation X.ProEtᵒᵖ AddCommGrpCat.{u + 1}).obj (op W))).symm

/-- Canonical cohomology computation on an injective resolution.
Source: Stacks 072W (blueprint: lem-sfb-proper-heart-section-comparison). -/
def resolutionIso {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [Abelian C] [Abelian D] [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
    [EnoughInjectives C] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] (N : C) (I : InjectiveResolution N) (n : ℕ) :
    (DerivedCategory.singleFunctor C 0 ⋙ F.rightDerivedFunctor ⋙
      DerivedCategory.homologyFunctor D (n : ℤ)).obj N ≅
        ((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).homology n :=
  (F.singleFunctorCompRightDerivedFunctorCompHomologyFunctorIso n).app N ≪≫
    I.isoRightDerivedObj F n

/-- Total-right-derived abelian sections, including all integer degrees.
It is obtained by deriving the abelian section-presheaf functor, and hence evaluates
to the ordinary right-derived section groups. Negative degrees are zero.
Source: Stacks 03FD (blueprint: lem-sfb-proper-heart-section-comparison). -/
def derivedAbelianSectionsPresheaf (X : Scheme.{u}) (q : ℤ) :
    Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} ⥤
      X.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  DerivedCategory.singleFunctor _ 0 ⋙
    (sheafToPresheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).rightDerivedFunctor ⋙
      DerivedCategory.homologyFunctor _ q

set_option linter.style.haveILetI false in
/-- The ordinary abelian-sheaf identification in the section formula is canonical,
natural in both the module and the section object. Its normalization is the map on
cohomology induced by every augmentation-compatible lift to an abelian resolution.

Source: Stacks 03FD (blueprint: lem-sfb-proper-heart-section-comparison).

Proof: The underlying abelian-sheaf functor is exact. An injective module sheaf is
acyclic for abelian section evaluation at every site object (03FD). Thus its
underlying abelian resolution computes ordinary cohomology. Compare with any
abelian injective resolution by an augmentation-compatible chain map. Homotopic
lifts give the same maps on homology, so the displayed formula is independent of
the lift and determines the isomorphism uniquely. Resolution comparison gives
naturality in N, and the same construction commutes with every restriction in W.
The unbounded/classical comparison identifies these computations for n ≥ 0; both
right derivatives of a sheaf in degree zero vanish in negative degrees. -/
theorem moduleAbelianSectionComparison
    (A : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :
    ∃! a : ∀ q : ℤ, moduleCohomologyPresheaf A q ≅
        SheafOfModules.toSheaf (ringSheaf A) ⋙ derivedAbelianSectionsPresheaf X q,
      ∀ (N : Modules A) (I : InjectiveResolution N)
        (K : InjectiveResolution ((SheafOfModules.toSheaf (ringSheaf A)).obj N))
        (φ : ((SheafOfModules.toSheaf (ringSheaf A)).mapHomologicalComplex (.up ℕ)).obj
          I.cocomplex ⟶ K.cocomplex)
        (_hφ : (SheafOfModules.toSheaf (ringSheaf A)).map (I.ι.f 0) ≫ φ.f 0 = K.ι.f 0)
        (n : ℕ),
        (a (n : ℤ)).hom.app N ≫
            (resolutionIso (sheafToPresheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
              _ K n).hom =
          (resolutionIso (sectionsPresheaf A) N I n).hom ≫
            HomologicalComplex.homologyMap
              (((sheafToPresheaf (Scheme.ProEt.topology X)
                AddCommGrpCat.{u + 1}).mapHomologicalComplex (.up ℕ)).map φ) n := by
  classical
  let C := X.ProEt
  let J := Scheme.ProEt.topology X
  let R := ringSheaf A
  let T := SheafOfModules.toSheaf R
  letI : PreservesFiniteColimits T := (CategoryTheory.moduleSheaves_colimits_forgetful R).2.2.1
  let F := sheafToPresheaf J AddCommGrpCat.{u + 1}
  let e : C ≌ ULiftHom.{u + 1} C := ULiftHom.equiv
  let J' := e.inverse.inducedTopology J
  let R' := (e.sheafCongr J J' RingCat.{u + 1}).functor.obj R
  let em := SheafOfModules.smallModulesEquivalence e R
  let ea := e.sheafCongr J J' AddCommGrpCat.{u + 1}
  let : EnoughInjectives (SheafOfModules.{u + 1} R') :=
    EnoughInjectives.of_equivalence em.inverse
  let : IsGrothendieckAbelian.{u + 1} (Sheaf J' AddCommGrpCat.{u + 1}) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u + 1} _ _
  let : ea.functor.Additive := Functor.additive_of_preserves_binary_products _
  have hT (I : Modules A) [Injective I] : F.rightAcyclic (T.obj I) := by
    intro q
    apply Functor.isZero
    intro W
    let U := W.unop
    let E := (evaluation Cᵒᵖ AddCommGrpCat.{u + 1}).obj W
    let S := F ⋙ E
    let S' := Sheaf.sectionsFunctorAt J' (e.functor.obj U)
    have : Injective (em.functor.obj I) := em.functor.injective_obj I
    obtain ⟨d, _⟩ := module_abelian_evaluation_comparison_general
      J' R' (e.functor.obj U)
    have hz := (SheafOfModules.toSheaf R' ⋙ S').isZero_rightDerived_obj_injective_succ
      q (em.functor.obj I)
    have hz' : IsZero ((S'.rightDerived (q + 1)).obj (ea.functor.obj (T.obj I))) :=
      hz.of_iso ((d (q + 1)).app (em.functor.obj I)).symm
    let c := Functor.compRightDerivedObjIso ea.functor S'
      (fun K _ ↦ S'.rightAcyclic_of_injective (ea.functor.obj K)) (q + 1) (T.obj I)
    have hs : IsZero ((S.rightDerived (q + 1)).obj (T.obj I)) := hz'.of_iso c
    exact hs.of_iso (Functor.rightDerivedCompObjIso F E (q + 1) (T.obj I)).symm
  let c₁ (n : ℕ) : moduleCohomologyPresheaf A (n : ℤ) ≅
      (sectionsPresheaf A).rightDerived n := by
    simpa only [moduleCohomologyPresheaf] using
      (sectionsPresheaf A).singleFunctorCompRightDerivedFunctorCompHomologyFunctorIso n
  let c₂raw (n : ℕ) : F.rightDerived n ≅
      derivedAbelianSectionsPresheaf X (n : ℤ) := by
    simpa only [derivedAbelianSectionsPresheaf] using
      (F.singleFunctorCompRightDerivedFunctorCompHomologyFunctorIso n).symm
  let c₂ (n : ℕ) : F.rightDerived n ≅
      derivedAbelianSectionsPresheaf X (n : ℤ) := c₂raw n
  let pos (n : ℕ) : moduleCohomologyPresheaf A (n : ℤ) ≅
      T ⋙ derivedAbelianSectionsPresheaf X (n : ℤ) :=
    c₁ n ≪≫ exact_comp_comparison T F hT n ≪≫
      Functor.isoWhiskerLeft T (c₂ n)
  have hformula (N : Modules A) (I : InjectiveResolution N)
      (K : InjectiveResolution (T.obj N))
      (φ : (T.mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶ K.cocomplex)
      (hφ : T.map (I.ι.f 0) ≫ φ.f 0 = K.ι.f 0) (n : ℕ) :
      (pos n).hom.app N ≫ (resolutionIso F _ K n).hom =
        (resolutionIso (sectionsPresheaf A) N I n).hom ≫
          HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℕ)).map φ) n := by
    dsimp [pos, c₁, c₂, c₂raw]
    change ((c₁ n).hom.app N ≫
      (exact_comp_comparison T F hT n).hom.app N ≫
      ((F.singleFunctorCompRightDerivedFunctorCompHomologyFunctorIso n).app
        (T.obj N)).inv) ≫
      (((F.singleFunctorCompRightDerivedFunctorCompHomologyFunctorIso n).app
        (T.obj N)).hom ≫ (K.isoRightDerivedObj F n).hom) = _
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [exact_comp_comparison_formula T F hT N I K φ hφ n]
    rfl
  have hsrc (N : Modules A) (q : ℤ) (hq : q < 0) :
      IsZero ((moduleCohomologyPresheaf A q).obj N) :=
    (DerivedCategory.isGE_iff _ 0).mp
      ((sectionsPresheaf A).isGE_rightDerivedFunctor_obj_singleFunctor N) q hq
  have htgt (N : Modules A) (q : ℤ) (hq : q < 0) :
      IsZero ((T ⋙ derivedAbelianSectionsPresheaf X q).obj N) :=
    (DerivedCategory.isGE_iff _ 0).mp
      (F.isGE_rightDerivedFunctor_obj_singleFunctor (T.obj N)) q hq
  let a : ∀ q : ℤ, moduleCohomologyPresheaf A q ≅
      T ⋙ derivedAbelianSectionsPresheaf X q := fun q ↦
    match q with
    | .ofNat n => pos n
    | .negSucc n => NatIso.ofComponents
        (fun N ↦ (hsrc N _ (by omega)).iso (htgt N _ (by omega)))
        (fun {N M} f ↦ (hsrc N _ (by omega)).eq_of_src _ _)
  refine ⟨a, ?_, ?_⟩
  · intro N I K φ hφ n
    exact hformula N I K φ hφ n
  · intro a' ha'
    funext q
    apply Iso.ext
    apply NatTrans.ext
    funext N
    cases q with
    | ofNat n =>
      let I := injectiveResolution N
      let K := injectiveResolution (T.obj N)
      let φ := InjectiveResolution.descOfQuasiIso (𝟙 (T.obj N)) K (T.mapResolution I.ι)
      have hφ : T.map (I.ι.f 0) ≫ φ.f 0 = K.ι.f 0 := by
        have h := InjectiveResolution.descOfQuasiIso_commutes
          (𝟙 (T.obj N)) K (T.mapResolution I.ι)
        simpa [φ, Functor.mapResolution] using congrArg (fun f ↦ f.f 0) h
      apply (cancel_mono (resolutionIso F _ K n).hom).1
      exact (ha' N I K φ hφ n).trans (hformula N I K φ hφ n).symm
    | negSucc n => exact (hsrc N (.negSucc n) (by omega)).eq_of_src _ _

/-- The actual module restriction functor to the slice.
Source: Stacks 0D6F (blueprint: lem-sfb-proper-heart-section-comparison). -/
abbrev restriction (A : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (W : X.ProEt) := SheafOfModules.overFunctor.{u + 1} (ringSheaf A) W

private theorem resolutionIso_naturality
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [Abelian C] [Abelian D] [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
    [EnoughInjectives C] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] {N M : C} (f : N ⟶ M)
    (I : InjectiveResolution N) (K : InjectiveResolution M)
    (φ : I.cocomplex ⟶ K.cocomplex)
    (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ K.ι.f 0) (n : ℕ) :
    (DerivedCategory.singleFunctor C 0 ⋙ F.rightDerivedFunctor ⋙
        DerivedCategory.homologyFunctor D (n : ℤ)).map f ≫
        (resolutionIso F M K n).hom =
      (resolutionIso F N I n).hom ≫
        HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℕ)).map φ) n := by
  dsimp only [resolutionIso, Iso.trans_hom]
  rw [← Category.assoc]
  erw [(F.singleFunctorCompRightDerivedFunctorCompHomologyFunctorIso n).hom.naturality f]
  rw [Category.assoc, InjectiveResolution.isoRightDerivedObj_hom_naturality f I K φ hφ F n]
  simp only [Category.assoc, Functor.comp_map, HomologicalComplex.homologyFunctor_map]
  rfl

private theorem sectionResolutionIso_naturality
    (A : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    {N M : Modules A} (f : N ⟶ M)
    (I : InjectiveResolution N) (K : InjectiveResolution M)
    (φ : I.cocomplex ⟶ K.cocomplex)
    (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ K.ι.f 0) (n : ℕ) (W : X.ProEt) :
    ((moduleCohomologyPresheaf A (n : ℤ)).map f).app (op W) ≫
        (sectionResolutionIso A M K n W).hom =
      (sectionResolutionIso A N I n W).hom ≫
        HomologicalComplex.homologyMap ((sectionsAt A W).mapHomologicalComplex
          (.up ℕ) |>.map φ) n := by
  let E := (evaluation X.ProEtᵒᵖ AddCommGrpCat.{u + 1}).obj (op W)
  have h := congrArg (fun t ↦ E.map t)
    (resolutionIso_naturality (sectionsPresheaf A) f I K φ hφ n)
  simp only [Functor.map_comp] at h
  dsimp only [sectionResolutionIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  change E.map ((moduleCohomologyPresheaf A (n : ℤ)).map f) ≫
      E.map (resolutionIso (sectionsPresheaf A) M K n).hom ≫ _ = _
  dsimp only [moduleCohomologyPresheaf] at *
  erw [← Category.assoc, h, Category.assoc]
  have hh := ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ n).map
      (((sectionsPresheaf A).mapHomologicalComplex (.up ℕ)).map φ)) E
  apply congrArg (fun t ↦ E.map (resolutionIso (sectionsPresheaf A) N I n).hom ≫ t)
    at hh
  dsimp only [resolutionIso] at hh ⊢
  simp only [Category.assoc] at hh ⊢
  convert hh using 1 <;> rfl

private def mappedResolution
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [Abelian C] [Abelian D] (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.PreservesInjectiveObjects] {N : C} (I : InjectiveResolution N) :
    InjectiveResolution (F.obj N) where
  cocomplex := (F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  injective n := F.injective_obj (I.cocomplex.X n)
  ι := F.mapResolution I.ι

set_option linter.style.haveILetI false in
/-- Supply small Ext groups directly from enough injectives on the slice site.
This avoids synthesizing small localized Homs through the derived category.
Source: Mathlib `hasExt_of_enoughInjectives` and the project size convention
(blueprint: lem-sfb-proper-heart-section-comparison). -/
local instance localizedAbelianHasExt (X : Scheme.{u}) (W : X.ProEt) :
    HasExt.{u + 1} (Sheaf ((Scheme.ProEt.topology X).over W) AddCommGrpCat.{u + 1}) := by
  letI : IsGrothendieckAbelian.{u + 1}
      (Sheaf ((Scheme.ProEt.topology X).over W) AddCommGrpCat.{u + 1}) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u + 1} _ _
  exact hasExt_of_enoughInjectives _

set_option linter.style.haveILetI false in
private def evaluatedResolutionIso
    {C : Type uC} {D : Type uD} {E : Type*}
    [Category.{vC} C] [Category.{vD} D] [Category* E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
    [EnoughInjectives C] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] (G : D ⥤ E) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (N : C) (I : InjectiveResolution N) (n : ℕ) :
    G.obj ((DerivedCategory.singleFunctor C 0 ⋙ F.rightDerivedFunctor ⋙
      DerivedCategory.homologyFunctor D (n : ℤ)).obj N) ≅
        ((G.mapHomologicalComplex (.up ℕ)).obj
          ((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex)).homology n :=
  G.mapIso (resolutionIso F N I n) ≪≫
    ((((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).sc n).mapHomologyIso G).symm

private theorem evaluatedResolutionIso_naturality
    {C : Type uC} {D : Type uD} {E : Type*}
    [Category.{vC} C] [Category.{vD} D] [Category* E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
    [EnoughInjectives C] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] (G : D ⥤ E) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {N M : C} (f : N ⟶ M) (I : InjectiveResolution N) (K : InjectiveResolution M)
    (φ : I.cocomplex ⟶ K.cocomplex)
    (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ K.ι.f 0) (n : ℕ) :
    G.map ((DerivedCategory.singleFunctor C 0 ⋙ F.rightDerivedFunctor ⋙
      DerivedCategory.homologyFunctor D (n : ℤ)).map f) ≫
        (evaluatedResolutionIso F G M K n).hom =
      (evaluatedResolutionIso F G N I n).hom ≫
        HomologicalComplex.homologyMap ((G.mapHomologicalComplex (.up ℕ)).map
          (((F.mapHomologicalComplex (.up ℕ)).map φ))) n := by
  have h := congrArg (fun t ↦ G.map t) (resolutionIso_naturality F f I K φ hφ n)
  simp only [Functor.map_comp] at h
  dsimp only [evaluatedResolutionIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [← Category.assoc, h, Category.assoc]
  have hh := congrArg (fun t ↦ G.map (resolutionIso F N I n).hom ≫ t)
    (ShortComplex.mapHomologyIso_inv_naturality
      ((HomologicalComplex.shortComplexFunctor _ _ n).map
        (((F.mapHomologicalComplex (.up ℕ)).map φ))) G)
  simp only [Category.assoc] at hh ⊢
  convert hh using 1 <;> rfl

private theorem evaluatedResolutionIso_evaluation
    {C : Type uC} {D : Type uD} {E : Type*}
    [Category.{vC} C] [Category.{vD} D] [Category* E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
    [EnoughInjectives C] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] {G G' : D ⥤ E} [G.Additive] [G'.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
    (τ : G ⟶ G') (N : C) (I : InjectiveResolution N) (n : ℕ) :
    τ.app ((DerivedCategory.singleFunctor C 0 ⋙ F.rightDerivedFunctor ⋙
      DerivedCategory.homologyFunctor D (n : ℤ)).obj N) ≫
        (evaluatedResolutionIso F G' N I n).hom =
      (evaluatedResolutionIso F G N I n).hom ≫
        ShortComplex.homologyMap
          ((((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).sc n).mapNatTrans τ) := by
  dsimp only [evaluatedResolutionIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [← Category.assoc, ← τ.naturality, Category.assoc]
  rw [ShortComplex.homologyMap_mapNatTrans]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rfl

private theorem testSectionsExact
    (B : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1}) (V : Tests Y) :
    PreservesFiniteLimits (sectionsAt B V.obj) ∧
      PreservesFiniteColimits (sectionsAt B V.obj) := by
  let E := SheafOfModules.evaluation.{u + 1} (ringSheaf B) (op V.obj)
  let U := forget₂ (ModuleCat.{u + 1} ((ringSheaf B).obj.obj (op V.obj)))
    AddCommGrpCat.{u + 1}
  let : E.Additive := { map_add := by intros; rfl }
  have hw : ∀ (P Q : Sheaf (Scheme.ProEt.topology Y) (Type (u + 1)))
      (f : P ⟶ Q), Epi f → Function.Surjective (f.hom.app (op V.obj)) := by
    intro P Q f hf
    exact V.property.2 f ((Sheaf.isLocallySurjective_iff_epi' (φ := f)).mpr hf)
  let : E.PreservesHomology :=
    AlgebraicGeometry.Scheme.ProEt.weaklyContractible_evaluation_preservesHomology
      Y B V.obj hw
  let : PreservesFiniteLimits E := Functor.preservesFiniteLimits_of_preservesHomology E
  let : PreservesFiniteColimits E := Functor.preservesFiniteColimits_of_preservesHomology E
  let : PreservesColimitsOfSize.{0, 0} U :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u + 1, 0, 0}
      ((ringSheaf B).obj.obj (op V.obj))
  let : PreservesFiniteColimits U := PreservesColimitsOfSize0.preservesFiniteColimits U
  change PreservesFiniteLimits (E ⋙ U) ∧ PreservesFiniteColimits (E ⋙ U)
  exact ⟨inferInstance, inferInstance⟩

/-- The section ring sheaf of the pulled-back condensed coefficient object.
Source: blueprint sk-def-sfb-pulled-back-coefficients and 03FD
(blueprint: lem-sfb-proper-heart-section-comparison). -/
abbrev condensedCoefficients
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) :=
  InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X) (condensedRingObj Λ X)

/-- Use the recorded equivalence, preserving underlying sections and restriction maps.
Source: Stacks 00YV (blueprint: lem-sfb-proper-heart-section-comparison). -/
abbrev realization
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) :=
  InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X)
    (condensedRingObj Λ X)

/-- Sections of exactly the published module-object derived pushforward.
Source: blueprint sk-def-sfb-module-derived-pushpull
(blueprint: lem-sfb-proper-heart-section-comparison). -/
abbrev condensedHigherSections
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (p : X ⟶ Y) (q : ℤ) :=
  DerivedCategory.singleFunctor _ 0 ⋙ CondensedRing.moduleObjectDerivedPushforward Λ p ⋙
    DerivedCategory.homologyFunctor _ q ⋙
      (realization Λ Y).functor ⋙ sectionsPresheaf (condensedCoefficients Λ Y)

/-- Resolution normalization for the actual internal-module direct image. The underlying
complex is I(X ×_Y V), using the action defined through the canonical eta_p.
Source: blueprint sk-def-sfb-module-derived-pushpull and 072W
(blueprint: lem-sfb-proper-heart-section-comparison). -/
def condensedImageResolutionIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (p : X ⟶ Y)
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (I : InjectiveResolution N) (n : ℕ) (V : Y.ProEt)
    [PreservesFiniteLimits
      ((realization Λ Y).functor ⋙ sectionsAt (condensedCoefficients Λ Y) V)]
    [PreservesFiniteColimits
      ((realization Λ Y).functor ⋙ sectionsAt (condensedCoefficients Λ Y) V)] :
    ((condensedHigherSections Λ p (n : ℤ)).obj N).obj (op V) ≅
      (((((realization Λ X).functor ⋙
        sectionsAt (condensedCoefficients Λ X) ((baseChange p).obj V)).mapHomologicalComplex
          (.up ℕ)).obj I.cocomplex).homology n) :=
  ((realization Λ Y).functor ⋙ sectionsAt (condensedCoefficients Λ Y) V).mapIso
    (resolutionIso (CondensedRing.lowerStar Λ p) N I n) ≪≫
    (((((CondensedRing.lowerStar Λ p).mapHomologicalComplex (.up ℕ)).obj
      I.cocomplex).sc n).mapHomologyIso
        ((realization Λ Y).functor ⋙ sectionsAt (condensedCoefficients Λ Y) V)).symm

private def realizedResolution
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (I : InjectiveResolution N) :
    InjectiveResolution ((realization Λ X).functor.obj N) :=
  mappedResolution (realization Λ X).functor I

private def condensedPositiveComponent
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (p : X ⟶ Y)
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (I : InjectiveResolution N) (n : ℕ) (V : Tests Y) :
    ((condensedHigherSections Λ p (n : ℤ)).obj N).obj (op V.obj) ≅
      ((moduleCohomologyPresheaf (condensedCoefficients Λ X) (n : ℤ)).obj
        ((realization Λ X).functor.obj N)).obj (op ((baseChange p).obj V.obj)) := by
  let := (testSectionsExact (condensedCoefficients Λ Y) V).1
  let := (testSectionsExact (condensedCoefficients Λ Y) V).2
  exact condensedImageResolutionIso Λ p N I n V.obj ≪≫
    (sectionResolutionIso (condensedCoefficients Λ X) _ (realizedResolution Λ N I)
      n ((baseChange p).obj V.obj)).symm

private theorem condensedPositiveComponent_naturality
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (p : X ⟶ Y)
    {N M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (f : N ⟶ M) (I : InjectiveResolution N) (K : InjectiveResolution M)
    (φ : I.cocomplex ⟶ K.cocomplex)
    (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ K.ι.f 0) (n : ℕ) (V : Tests Y) :
    ((condensedHigherSections Λ p (n : ℤ)).map f).app (op V.obj) ≫
        (condensedPositiveComponent Λ p M K n V).hom =
      (condensedPositiveComponent Λ p N I n V).hom ≫
        ((moduleCohomologyPresheaf (condensedCoefficients Λ X) (n : ℤ)).map
          ((realization Λ X).functor.map f)).app (op ((baseChange p).obj V.obj)) := by
  let := (testSectionsExact (condensedCoefficients Λ Y) V).1
  let := (testSectionsExact (condensedCoefficients Λ Y) V).2
  let E := (realization Λ X).functor
  have hφ' : (realizedResolution Λ N I).ι.f 0 ≫
      ((E.mapHomologicalComplex (.up ℕ)).map φ).f 0 =
        E.map f ≫ (realizedResolution Λ M K).ι.f 0 := by
    change E.map (I.ι.f 0) ≫ E.map (φ.f 0) = E.map f ≫ E.map (K.ι.f 0)
    rw [← Functor.map_comp, hφ, Functor.map_comp]
  have hi := evaluatedResolutionIso_naturality (CondensedRing.lowerStar Λ p)
    ((realization Λ Y).functor ⋙ sectionsAt (condensedCoefficients Λ Y) V.obj)
    f I K φ hφ n
  have hs := sectionResolutionIso_naturality (condensedCoefficients Λ X) (E.map f)
    (realizedResolution Λ N I) (realizedResolution Λ M K)
    ((E.mapHomologicalComplex (.up ℕ)).map φ) hφ' n ((baseChange p).obj V.obj)
  apply (cancel_mono (sectionResolutionIso (condensedCoefficients Λ X) _
    (realizedResolution Λ M K) n ((baseChange p).obj V.obj)).hom).1
  dsimp only [condensedPositiveComponent, Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  erw [hs, Iso.inv_hom_id_assoc]
  exact hi

private theorem condensedPositiveComponent_restriction
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (p : X ⟶ Y)
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (I : InjectiveResolution N) (n : ℕ) {V V' : (Tests Y)ᵒᵖ} (f : V ⟶ V') :
    ((condensedHigherSections Λ p (n : ℤ)).obj N).map
        ((testInclusion Y).op.map f) ≫
        (condensedPositiveComponent Λ p N I n V'.unop).hom =
      (condensedPositiveComponent Λ p N I n V.unop).hom ≫
        ((moduleCohomologyPresheaf (condensedCoefficients Λ X) (n : ℤ)).obj
          ((realization Λ X).functor.obj N)).map
          ((testInclusion Y ⋙ baseChange p).op.map f) := by
  let := (testSectionsExact (condensedCoefficients Λ Y) V.unop).1
  let := (testSectionsExact (condensedCoefficients Λ Y) V.unop).2
  let := (testSectionsExact (condensedCoefficients Λ Y) V'.unop).1
  let := (testSectionsExact (condensedCoefficients Λ Y) V'.unop).2
  let τ : (realization Λ Y).functor ⋙
      sectionsAt (condensedCoefficients Λ Y) V.unop.obj ⟶
        (realization Λ Y).functor ⋙ sectionsAt (condensedCoefficients Λ Y) V'.unop.obj :=
    Functor.whiskerLeft
    ((realization Λ Y).functor ⋙ sectionsPresheaf (condensedCoefficients Λ Y))
    ((evaluation Y.ProEtᵒᵖ AddCommGrpCat.{u + 1}).map ((testInclusion Y).op.map f))
  let σ := (evaluation X.ProEtᵒᵖ AddCommGrpCat.{u + 1}).map
    ((testInclusion Y ⋙ baseChange p).op.map f)
  have hi := evaluatedResolutionIso_evaluation (CondensedRing.lowerStar Λ p) τ N I n
  have hs := evaluatedResolutionIso_evaluation (sectionsPresheaf (condensedCoefficients Λ X))
    σ _ (realizedResolution Λ N I) n
  apply (cancel_mono (sectionResolutionIso (condensedCoefficients Λ X) _
    (realizedResolution Λ N I) n ((baseChange p).obj V'.unop.obj)).hom).1
  dsimp only [condensedPositiveComponent, Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  erw [hs, Iso.inv_hom_id_assoc]
  exact hi

private def condensedPositiveComparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (p : X ⟶ Y) (n : ℕ) :
    condensedHigherSections Λ p (n : ℤ) ⋙ precompose (testInclusion Y) ≅
      (realization Λ X).functor ⋙ moduleCohomologyPresheaf (condensedCoefficients Λ X) (n : ℤ) ⋙
        precompose (testInclusion Y ⋙ baseChange p) :=
  NatIso.ofComponents (fun N ↦ NatIso.ofComponents
    (fun V ↦ condensedPositiveComponent Λ p N (injectiveResolution N) n V.unop)
    (fun f ↦ condensedPositiveComponent_restriction Λ p N (injectiveResolution N) n f))
    (by
      intro N M f
      apply NatTrans.ext
      funext V
      exact condensedPositiveComponent_naturality Λ p f
        (injectiveResolution N) (injectiveResolution M)
        (InjectiveResolution.desc f (injectiveResolution M) (injectiveResolution N))
        (InjectiveResolution.desc_commutes_zero f _ _) n V.unop)

set_option maxHeartbeats 1000000 in
-- The resolution normalization unfolds the realization equivalence and its coherence maps.
/-- The same section formula for arbitrary commutative condensed coefficients, with
exactly moduleObjectDerivedPushforward (the total derivative of mapMod followed by
restriction along eta_p). The right side is transported through the existing internal/
sectionwise equivalence. Naturality includes all maps between the test objects, and
the resolution equation fixes the canonical comparison.

Source: blueprint sk-lem-proper-heart-continuity, paragraph 3; Stacks 072W and 03FD
(blueprint: lem-sfb-proper-heart-section-comparison).

Proof: The sectionwise realization equivalence preserves the underlying sheaves,
section groups and restriction maps. The underived internal pushforward has these
same sections, and its scalar action is the original action composed with eta_p.
Consequently its realization is exactly the continuous module direct image with
rho = eta_p. An equivalence preserves injectives. Apply the general comparison to
realized resolutions, or directly evaluate the internal pushforward of an injective
resolution. The two computations give the displayed normalization, which determines
the comparison uniquely and supplies naturality in both variables. Slice localization
and module/abelian comparison give the remaining interpretations of the right side.
The argument uses neither properness of p nor boundedness of a complex or a scheme. -/
theorem condensedProperHeartSectionComparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (p : X ⟶ Y) :
    ∃! e : ∀ q : ℤ,
      condensedHigherSections Λ p q ⋙ precompose (testInclusion Y) ≅
        (realization Λ X).functor ⋙ moduleCohomologyPresheaf (condensedCoefficients Λ X) q ⋙
          precompose (testInclusion Y ⋙ baseChange p),
      ∀ (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
        (I : InjectiveResolution N)
        (K : InjectiveResolution ((realization Λ X).functor.obj N))
        (φ : ((realization Λ X).functor.mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶
          K.cocomplex)
        (_hφ : (realization Λ X).functor.map (I.ι.f 0) ≫ φ.f 0 = K.ι.f 0)
        (n : ℕ) (V : Tests Y)
        (hlim : PreservesFiniteLimits
          ((realization Λ Y).functor ⋙ sectionsAt (condensedCoefficients Λ Y) V.obj))
        (hcolim : PreservesFiniteColimits
          ((realization Λ Y).functor ⋙ sectionsAt (condensedCoefficients Λ Y) V.obj)),
        letI := hlim
        letI := hcolim
        ((e (n : ℤ)).hom.app N).app (op V) ≫
            (sectionResolutionIso (condensedCoefficients Λ X) _ K n
              ((baseChange p).obj V.obj)).hom =
          (condensedImageResolutionIso Λ p N I n V.obj).hom ≫
            HomologicalComplex.homologyMap
              (((sectionsAt (condensedCoefficients Λ X)
                ((baseChange p).obj V.obj)).mapHomologicalComplex (.up ℕ)).map φ) n := by
  let E := (realization Λ X).functor
  let A := condensedCoefficients Λ X
  let B := condensedCoefficients Λ Y
  have hsrc (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) (q : ℤ) (hq : q < 0) :
      IsZero (((condensedHigherSections Λ p q ⋙ precompose (testInclusion Y)).obj N)) := by
    exact ((realization Λ Y).functor ⋙ sectionsPresheaf B ⋙
      precompose (testInclusion Y)).map_isZero
      ((DerivedCategory.isGE_iff _ 0).mp
        ((CondensedRing.lowerStar Λ p).isGE_rightDerivedFunctor_obj_singleFunctor N) q hq)
  have htgt (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) (q : ℤ) (hq : q < 0) :
      IsZero (((E ⋙ moduleCohomologyPresheaf A q ⋙
        precompose (testInclusion Y ⋙ baseChange p)).obj N)) := by
    exact (precompose (testInclusion Y ⋙ baseChange p)).map_isZero
      ((DerivedCategory.isGE_iff _ 0).mp
        ((sectionsPresheaf A).isGE_rightDerivedFunctor_obj_singleFunctor (E.obj N)) q hq)
  let e : ∀ q : ℤ,
      condensedHigherSections Λ p q ⋙ precompose (testInclusion Y) ≅
        E ⋙ moduleCohomologyPresheaf A q ⋙
          precompose (testInclusion Y ⋙ baseChange p) := fun q ↦ match q with
    | .ofNat n => condensedPositiveComparison Λ p n
    | .negSucc n => NatIso.ofComponents
        (fun N ↦ (hsrc N _ (by omega)).iso (htgt N _ (by omega)))
        (fun {N M} f ↦ (hsrc N _ (by omega)).eq_of_src _ _)
  have hformula (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) (I : InjectiveResolution N)
      (K : InjectiveResolution (E.obj N))
      (φ : (E.mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶ K.cocomplex)
      (hφ : E.map (I.ι.f 0) ≫ φ.f 0 = K.ι.f 0) (n : ℕ) (V : Tests Y)
      (hlim : PreservesFiniteLimits ((realization Λ Y).functor ⋙ sectionsAt B V.obj))
      (hcolim : PreservesFiniteColimits ((realization Λ Y).functor ⋙ sectionsAt B V.obj)) :
      letI := hlim
      letI := hcolim
      ((e (n : ℤ)).hom.app N).app (op V) ≫
          (sectionResolutionIso A _ K n ((baseChange p).obj V.obj)).hom =
        (condensedImageResolutionIso Λ p N I n V.obj).hom ≫
          HomologicalComplex.homologyMap
            (((sectionsAt A ((baseChange p).obj V.obj)).mapHomologicalComplex (.up ℕ)).map
              φ) n := by
    let := hlim
    let := hcolim
    have h := condensedPositiveComponent_naturality Λ p (𝟙 N)
      (injectiveResolution N) I
      (InjectiveResolution.desc (𝟙 N) I (injectiveResolution N))
      (InjectiveResolution.desc_commutes_zero (𝟙 N) I (injectiveResolution N)) n V
    erw [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp,
      CategoryTheory.Functor.map_id, NatTrans.id_app, Category.comp_id] at h
    have hs := sectionResolutionIso_naturality A (𝟙 (E.obj N))
      (realizedResolution Λ N I) K φ
      (by
        dsimp only [realizedResolution, mappedResolution, CategoryTheory.Functor.mapResolution,
          HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
        simp only [HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
          CochainComplex.single₀ObjXSelf, Iso.refl_hom, Iso.refl_inv, Category.id_comp]
        exact hφ)
      n ((baseChange p).obj V.obj)
    erw [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp] at hs
    change (condensedPositiveComponent Λ p N (injectiveResolution N) n V).hom ≫ _ = _
    rw [← h]
    dsimp only [condensedPositiveComponent, Iso.trans_hom, Iso.symm_hom]
    erw [Category.assoc, hs, Iso.inv_hom_id_assoc]
  refine ⟨e, hformula, ?_⟩
  intro e' he'
  funext q
  apply Iso.ext
  apply NatTrans.ext
  funext N
  cases q with
  | ofNat n =>
    apply NatTrans.ext
    funext V
    let := (testSectionsExact B V.unop).1
    let := (testSectionsExact B V.unop).2
    let I := injectiveResolution N
    let K := realizedResolution Λ N I
    have hi : E.map (I.ι.f 0) ≫ (HomologicalComplex.Hom.f (𝟙 K.cocomplex) 0) =
        K.ι.f 0 := by
      change E.map (I.ι.f 0) ≫ 𝟙 _ = E.map (I.ι.f 0)
      exact Category.comp_id _
    apply (cancel_mono (sectionResolutionIso A _ K n
      ((baseChange p).obj V.unop.obj)).hom).1
    exact (he' N I K (𝟙 _) hi n V.unop inferInstance inferInstance).trans
      (hformula N I K (𝟙 _) hi n V.unop inferInstance inferInstance).symm
  | negSucc n => exact (hsrc N (.negSucc n) (by omega)).eq_of_src _ _


end AlgebraicGeometry.ProEtale.HeartSections
