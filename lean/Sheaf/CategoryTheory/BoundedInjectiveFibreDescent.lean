/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q125
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Descent of bounded injective fibre comparisons

Source: Stacks Project, Derived Categories, Tag 05TK,
`lemma-resolution-functor-quasi-inverse`, and the adjacent resolution-functor discussion.
The comparison, shift and pasting calculations are the eight steps of
(blueprint: lem-amb-bounded-injective-fibre-descent).

`boundedInjectiveDerived` uses the existing exact equivalence `K⁺(Inj A) ≌ D⁺(A)`.
`BoundedInjectiveComparison` specifies the component using every pair of resolutions.
Equality in `HomotopyCategory.Plus` means equality of homotopy classes of chain maps.
In particular its comparison arrow can be represented by a chain map, and its augmentation
square says precisely that the two chain maps are homotopic.

## Main definitions

- `CategoryTheory.boundedInjectiveDerived`: the concrete functor computed on injectives.
- `CategoryTheory.boundedInjectiveResolutionIso`: its canonical resolution computation.
- `CategoryTheory.BoundedInjectiveComparison`: the formula for every pair of resolutions.

## Main statements

- `CategoryTheory.boundedInjectiveFibreDescent`: existence and uniqueness of the comparison.
- `CategoryTheory.boundedInjectiveComparison_id`: compatibility with identity data.
- `CategoryTheory.boundedInjectiveComparison_comp`: compatibility with composition data.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe uA vA wA uA' vA' wA' uA'' vA'' wA'' uB vB wB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {A : Type uA} [Category.{vA} A] [Abelian A] [EnoughInjectives A]
  [HasDerivedCategory.{wA} A]
  {A' : Type uA'} [Category.{vA'} A'] [Abelian A'] [EnoughInjectives A']
  [HasDerivedCategory.{wA'} A']
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]

/-- Apply a homotopy functor after the existing injective replacement equivalence and then
localize its output. This is the concrete functor `RF` in Stacks, Tag 05TK and Step 2 of
(blueprint: lem-amb-bounded-injective-fibre-descent). No representative is chosen from a
mere existence assertion: the quasi-inverse belongs to an equivalence. -/
def boundedInjectiveDerived (F : HomotopyCategory.Plus A ⥤ HomotopyCategory.Plus B) :
    DerivedCategory.Plus A ⥤ DerivedCategory.Plus B :=
  (DerivedCategory.Plus.injectiveObjectEquivalence A).inverse ⋙
    (InjectiveObject.ι A).mapHomotopyCategoryPlus ⋙ F ⋙ DerivedCategory.Plus.Qh

/-- The shift comparisons on `RF` are those of the exact injective equivalence and `F`.
Source: Stacks, `lemma-j-is-exact`, Step 2 of
(blueprint: lem-amb-bounded-injective-fibre-descent). -/
instance boundedInjectiveDerived_commShift
    (F : HomotopyCategory.Plus A ⥤ HomotopyCategory.Plus B) [F.CommShift ℤ] :
    (boundedInjectiveDerived F).CommShift ℤ :=
  inferInstanceAs (((DerivedCategory.Plus.injectiveObjectEquivalence A).inverse ⋙
    (InjectiveObject.ι A).mapHomotopyCategoryPlus ⋙ F ⋙ DerivedCategory.Plus.Qh).CommShift ℤ)

/-- The canonical computation on a bounded below injective resolution. The first factor
applies `RF` to the augmentation and the second is the inverse unit of the injective
replacement equivalence, after applying the inclusion, `F` and localization.
Source: Stacks, Tag 05TK and `remark-big-localization`, Steps 2 and 6 of
(blueprint: lem-amb-bounded-injective-fibre-descent). -/
def boundedInjectiveResolutionIso
    (F : HomotopyCategory.Plus A ⥤ HomotopyCategory.Plus B)
    (K : HomotopyCategory.Plus A) (I : HomotopyCategory.Plus (InjectiveObject A))
    (k : K ⟶ (InjectiveObject.ι A).mapHomotopyCategoryPlus.obj I)
    [IsIso (DerivedCategory.Plus.Qh.map k)] :
    (boundedInjectiveDerived F).obj (DerivedCategory.Plus.Qh.obj K) ≅
      DerivedCategory.Plus.Qh.obj
        (F.obj ((InjectiveObject.ι A).mapHomotopyCategoryPlus.obj I)) :=
  (boundedInjectiveDerived F).mapIso (asIso (DerivedCategory.Plus.Qh.map k)) ≪≫
    ((InjectiveObject.ι A).mapHomotopyCategoryPlus ⋙ F ⋙ DerivedCategory.Plus.Qh).mapIso
      ((DerivedCategory.Plus.injectiveObjectEquivalence A).unitIso.app I).symm

/-- The resolution formula for a comparison. Both augmentations are quasi-isomorphisms
(equivalently their localizations are isomorphisms). The universally quantified `u` is a
homotopy class with `E(k) ≫ u = k'`. There is no injectivity condition on `E(I)`.
The equation uses the canonical exact-functor localization comparison to identify
`D⁺E(QK)` with `Q(EK)`.
Source: Stacks, Tag 05TK and `remark-big-localization`, Steps 3--6 of
(blueprint: lem-amb-bounded-injective-fibre-descent). -/
def BoundedInjectiveComparison
    (F : HomotopyCategory.Plus A ⥤ HomotopyCategory.Plus B)
    (F' : HomotopyCategory.Plus A' ⥤ HomotopyCategory.Plus B)
    (E : A ⥤ A') [E.Additive]
    [hElim : PreservesFiniteLimits E] [hEcolim : PreservesFiniteColimits E]
    (τ : F ⟶ E.mapHomotopyCategoryPlus ⋙ F')
    (t : boundedInjectiveDerived F ⟶ E.mapDerivedCategoryPlus ⋙ boundedInjectiveDerived F') :
    Prop :=
  ∀ (K : HomotopyCategory.Plus A)
    (I : HomotopyCategory.Plus (InjectiveObject A))
    (J : HomotopyCategory.Plus (InjectiveObject A'))
    (k : K ⟶ (InjectiveObject.ι A).mapHomotopyCategoryPlus.obj I)
    [IsIso (DerivedCategory.Plus.Qh.map k)]
    (k' : E.mapHomotopyCategoryPlus.obj K ⟶
      (InjectiveObject.ι A').mapHomotopyCategoryPlus.obj J)
    [IsIso (DerivedCategory.Plus.Qh.map k')]
    (u : E.mapHomotopyCategoryPlus.obj
      ((InjectiveObject.ι A).mapHomotopyCategoryPlus.obj I) ⟶
      (InjectiveObject.ι A').mapHomotopyCategoryPlus.obj J),
    E.mapHomotopyCategoryPlus.map k ≫ u = k' →
    (boundedInjectiveResolutionIso F K I k).hom ≫
        DerivedCategory.Plus.Qh.map
          (τ.app ((InjectiveObject.ι A).mapHomotopyCategoryPlus.obj I) ≫ F'.map u) =
      t.app (DerivedCategory.Plus.Qh.obj K) ≫
        (boundedInjectiveDerived F').map (E.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
        (boundedInjectiveResolutionIso F' (E.mapHomotopyCategoryPlus.obj K) J k').hom

/-- Exactness of the functor computed by injective representatives.
Source: Stacks, Tag 05TK and `lemma-j-is-exact`.
Proof: Step 1 uses the interval `[0,0]` of
`lem-trf-filtered-localization-injective-model` to obtain the injective equivalence.
In Step 2 its quasi-inverse has the conjugate shift comparisons and is exact by
`lem-sf-triangulated-right-adjoint`. The injective inclusion is exact because shifts and
finite cone sums retain injectives. Compose this with exact `F` and exact localization,
using `def-weil-abstract-derived-category` and `def-weil-triangulated-category`.
(blueprint: lem-amb-bounded-injective-fibre-descent) -/
theorem boundedInjectiveDerived_isTriangulated
    (F : HomotopyCategory.Plus A ⥤ HomotopyCategory.Plus B)
    [F.CommShift ℤ] [F.IsTriangulated] :
    (boundedInjectiveDerived F).IsTriangulated := by
  unfold boundedInjectiveDerived
  infer_instance

set_option linter.unusedSectionVars false in
/-- The comparison homotopy class exists uniquely, even when `E(I)` is not injective.
Source: Stacks, Tags 05TG and 05TK, and the K-injective Hom comparison.
Proof: Step 3 uses `lem-sc-bounded-below-injective-resolution-existence` and
`lem-weil-pbc-bounded-below-injectives-kinjective`. Exact `E` preserves quasi-isomorphisms
by `lem-sf-exact-functor-derived-triangulated`. In Step 4 lift
`Q(k') Q(E(k))⁻¹` uniquely using `lem-weil-pbc-kinjective-hom-derived`, or the `[0,0]`
Hom clause of `lem-trf-filtered-localization-injective-model`. Injectivity of the same
Hom map with source `EK` proves the augmentation equation in the homotopy category.
Only the target `J` needs to be K-injective.
(blueprint: lem-amb-bounded-injective-fibre-descent) -/
theorem boundedInjectiveComparison_exists_unique_lift
    (E : A ⥤ A') [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (K : HomotopyCategory.Plus A) (I : HomotopyCategory.Plus (InjectiveObject A))
    (J : HomotopyCategory.Plus (InjectiveObject A'))
    (k : K ⟶ (InjectiveObject.ι A).mapHomotopyCategoryPlus.obj I)
    [IsIso (DerivedCategory.Plus.Qh.map k)]
    (k' : E.mapHomotopyCategoryPlus.obj K ⟶
      (InjectiveObject.ι A').mapHomotopyCategoryPlus.obj J)
    [IsIso (DerivedCategory.Plus.Qh.map k')] :
    ∃! u : E.mapHomotopyCategoryPlus.obj
        ((InjectiveObject.ι A).mapHomotopyCategoryPlus.obj I) ⟶
        (InjectiveObject.ι A').mapHomotopyCategoryPlus.obj J,
      E.mapHomotopyCategoryPlus.map k ≫ u = k' := by
  let L := E.mapHomotopyCategoryPlus
  let Q := DerivedCategory.Plus.Qh (C := A')
  have hk : IsIso (Q.map (L.map k)) := by
    have h := E.mapDerivedCategoryPlusFactorsh.inv.naturality k
    dsimp only [Functor.comp_map] at h
    have hc : IsIso (Q.map (L.map k) ≫
        E.mapDerivedCategoryPlusFactorsh.inv.app
          ((InjectiveObject.ι A).mapHomotopyCategoryPlus.obj I)) := by
      rw [h]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      (E.mapDerivedCategoryPlusFactorsh.inv.app
        ((InjectiveObject.ι A).mapHomotopyCategoryPlus.obj I))
  let bij (X : HomotopyCategory.Plus A') :=
    DerivedCategory.Plus.Qh_map_bijective_of_isKInjective X
      ((InjectiveObject.ι A').mapHomotopyCategoryPlus.obj J) inferInstance
  have : IsIso (Q.map (L.map k)) := hk
  obtain ⟨u, hu⟩ := (bij (L.obj
    ((InjectiveObject.ι A).mapHomotopyCategoryPlus.obj I))).surjective
      (inv (Q.map (L.map k)) ≫ Q.map k')
  refine ⟨u, ?_, ?_⟩
  · apply (bij (L.obj K)).injective
    change Q.map _ = Q.map _
    rw [Q.map_comp, hu, IsIso.hom_inv_id_assoc]
  · intro v hv
    apply (bij (L.obj ((InjectiveObject.ι A).mapHomotopyCategoryPlus.obj I))).injective
    change Q.map v = Q.map u
    rw [hu, ← cancel_epi (Q.map (L.map k)), ← Q.map_comp, hv]
    simp


private abbrev biInj : HomotopyCategory.Plus (InjectiveObject A) ⥤
    HomotopyCategory.Plus A := (InjectiveObject.ι A).mapHomotopyCategoryPlus

private abbrev biEquiv : HomotopyCategory.Plus (InjectiveObject A) ≌
    DerivedCategory.Plus.{wA} A := DerivedCategory.Plus.injectiveObjectEquivalence A

private def biAug (K : HomotopyCategory.Plus A) :
    K ⟶ biInj.obj (biEquiv.inverse.obj (DerivedCategory.Plus.Qh.obj K)) :=
  (Equiv.ofBijective _ (DerivedCategory.Plus.Qh_map_bijective_of_isKInjective K
    (biInj.obj (biEquiv.inverse.obj (DerivedCategory.Plus.Qh.obj K)))
      inferInstance)).symm (biEquiv.counitIso.inv.app (DerivedCategory.Plus.Qh.obj K))

private lemma biAug_map (K : HomotopyCategory.Plus A) :
    DerivedCategory.Plus.Qh.map (biAug K) =
      biEquiv.counitIso.inv.app (DerivedCategory.Plus.Qh.obj K) :=
  (Equiv.ofBijective _ (DerivedCategory.Plus.Qh_map_bijective_of_isKInjective K
    (biInj.obj (biEquiv.inverse.obj (DerivedCategory.Plus.Qh.obj K)))
      inferInstance)).apply_symm_apply _

private instance biAug_map_isIso (K : HomotopyCategory.Plus A) :
    IsIso (DerivedCategory.Plus.Qh.map (biAug K)) := by
  rw [biAug_map]
  infer_instance

private lemma biAug_naturality {K L : HomotopyCategory.Plus A} (f : K ⟶ L) :
    f ≫ biAug L = biAug K ≫ biInj.map (biEquiv.inverse.map
      (DerivedCategory.Plus.Qh.map f)) := by
  apply (DerivedCategory.Plus.Qh_map_bijective_of_isKInjective _ _ inferInstance).injective
  simp only [Functor.map_comp, biAug_map]
  exact biEquiv.counitIso.inv.naturality (DerivedCategory.Plus.Qh.map f)

private lemma biAug_inj (I : HomotopyCategory.Plus (InjectiveObject A)) :
    biAug (biInj.obj I) = biInj.map (biEquiv.unitIso.hom.app I) := by
  apply (DerivedCategory.Plus.Qh_map_bijective_of_isKInjective _ _ inferInstance).injective
  rw [biAug_map]
  exact biEquiv.counitInv_app_functor I

private def biUnit (F : HomotopyCategory.Plus A ⥤ HomotopyCategory.Plus B) :
    F ⋙ DerivedCategory.Plus.Qh ⟶ DerivedCategory.Plus.Qh ⋙ boundedInjectiveDerived F where
  app K := DerivedCategory.Plus.Qh.map (F.map (biAug K))
  naturality _ _ f := by
    simp only [Functor.comp_map, ← Functor.map_comp, ← F.map_comp]
    change _ = DerivedCategory.Plus.Qh.map (F.map (biAug _)) ≫
      DerivedCategory.Plus.Qh.map (F.map (biInj.map (biEquiv.inverse.map _)))
    rw [← Functor.map_comp, ← F.map_comp, biAug_naturality]

private lemma biUnit_inj (F : HomotopyCategory.Plus A ⥤ HomotopyCategory.Plus B)
    (I : HomotopyCategory.Plus (InjectiveObject A)) :
    (biUnit F).app (biInj.obj I) =
      (biInj ⋙ F ⋙ DerivedCategory.Plus.Qh).map (biEquiv.unitIso.hom.app I) := by
  simp only [biUnit, biAug_inj, Functor.comp_map]

private instance biUnit_inj_isIso
    (F : HomotopyCategory.Plus A ⥤ HomotopyCategory.Plus B)
    (I : HomotopyCategory.Plus (InjectiveObject A)) :
    IsIso ((biUnit F).app (biInj.obj I)) := by
  rw [biUnit_inj]
  infer_instance

private instance biUnit_isRightDerived
    (F : HomotopyCategory.Plus A ⥤ HomotopyCategory.Plus B) :
    (boundedInjectiveDerived F).IsRightDerivedFunctor (biUnit F)
      (HomotopyCategory.Plus.quasiIso A) :=
  (HomotopyCategory.Plus.localizerMorphism_derives
    (F ⋙ DerivedCategory.Plus.Qh)).isRightDerivedFunctor_of_isIso (biUnit F)
      (fun _ ↦ inferInstance)

private lemma biUnit_resolution
    (F : HomotopyCategory.Plus A ⥤ HomotopyCategory.Plus B)
    (K : HomotopyCategory.Plus A) (I : HomotopyCategory.Plus (InjectiveObject A))
    (k : K ⟶ biInj.obj I) [IsIso (DerivedCategory.Plus.Qh.map k)] :
    (biUnit F).app K ≫ (boundedInjectiveResolutionIso F K I k).hom =
      DerivedCategory.Plus.Qh.map (F.map k) := by
  have h := (biUnit F).naturality k
  dsimp only [Functor.comp_map] at h
  dsimp only [boundedInjectiveResolutionIso, Iso.trans_hom, Functor.mapIso_hom, asIso_hom,
    Iso.symm_hom]
  rw [← Category.assoc, ← h, biUnit_inj]
  change (DerivedCategory.Plus.Qh.map (F.map k) ≫
    (biInj ⋙ F ⋙ DerivedCategory.Plus.Qh).map (biEquiv.unitIso.app I).hom) ≫
    (biInj ⋙ F ⋙ DerivedCategory.Plus.Qh).map (biEquiv.unitIso.app I).inv = _
  rw [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id, Functor.map_id]
  exact Category.comp_id _

private instance biUnit_commShift
    (F : HomotopyCategory.Plus A ⥤ HomotopyCategory.Plus B) [F.CommShift ℤ] :
    NatTrans.CommShift (biUnit F) ℤ := by
  let G := biInj ⋙ F ⋙ DerivedCategory.Plus.Qh
  let e : HomotopyCategory.Plus (InjectiveObject A) ≌ DerivedCategory.Plus.{wA} A :=
    DerivedCategory.Plus.injectiveObjectEquivalence A
  have : e.CommShift ℤ := inferInstance
  have heq : Functor.whiskerLeft biInj (biUnit F) =
      (Functor.leftUnitor G).inv ≫ Functor.whiskerRight e.unitIso.hom G ≫
        (Functor.associator e.functor e.inverse G).hom ≫
        (Functor.associator biInj DerivedCategory.Plus.Qh (boundedInjectiveDerived F)).hom := by
    apply NatTrans.ext
    funext I
    dsimp only [Functor.comp_obj, Functor.whiskerLeft_app, NatTrans.comp_app,
      Functor.leftUnitor_inv_app, Functor.associator_hom_app, Functor.whiskerRight_app]
    erw [Category.id_comp, Category.comp_id, Category.comp_id]
    exact biUnit_inj F I
  have : NatTrans.CommShift (Functor.whiskerLeft biInj (biUnit F)) ℤ := by
    rw [heq]
    infer_instance
  refine NatTrans.CommShift.of_whiskerLeft _ biInj (fun K ↦ ?_)
  exact ⟨_, biAug K, by dsimp; infer_instance⟩

private def biBeta
    (F : HomotopyCategory.Plus A ⥤ HomotopyCategory.Plus B)
    (F' : HomotopyCategory.Plus A' ⥤ HomotopyCategory.Plus B)
    (E : A ⥤ A') [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (τ : F ⟶ E.mapHomotopyCategoryPlus ⋙ F') :
    F ⋙ DerivedCategory.Plus.Qh ⟶
      DerivedCategory.Plus.Qh ⋙ E.mapDerivedCategoryPlus ⋙ boundedInjectiveDerived F' :=
  Functor.whiskerRight τ DerivedCategory.Plus.Qh ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft E.mapHomotopyCategoryPlus (biUnit F') ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight E.mapDerivedCategoryPlusFactorsh.inv (boundedInjectiveDerived F') ≫
    (Functor.associator _ _ _).hom

private lemma biResolution_hom
    (F : HomotopyCategory.Plus A ⥤ HomotopyCategory.Plus B)
    (K : HomotopyCategory.Plus A) (I : HomotopyCategory.Plus (InjectiveObject A))
    (k : K ⟶ biInj.obj I) [IsIso (DerivedCategory.Plus.Qh.map k)] :
    (boundedInjectiveResolutionIso F K I k).hom =
      (boundedInjectiveDerived F).map (DerivedCategory.Plus.Qh.map k) ≫
        inv ((biUnit F).app (biInj.obj I)) := by
  simp only [biUnit_inj]
  simp only [boundedInjectiveResolutionIso, Iso.trans_hom, Functor.mapIso_hom,
    asIso_hom, Iso.symm_hom]
  change _ ≫ _ = _ ≫ inv ((biInj ⋙ F ⋙ DerivedCategory.Plus.Qh).map
    (biEquiv.unitIso.app I).hom)
  rw [← Functor.map_inv]
  have hi : inv (biEquiv.unitIso.app I).hom = (biEquiv.unitIso.app I).inv := by
    apply IsIso.inv_eq_of_hom_inv_id
    exact Iso.hom_inv_id _
  rw [hi]

set_option linter.unusedSectionVars false in
private lemma biBeta_app
    (F : HomotopyCategory.Plus A ⥤ HomotopyCategory.Plus B)
    (F' : HomotopyCategory.Plus A' ⥤ HomotopyCategory.Plus B)
    (E : A ⥤ A') [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (τ : F ⟶ E.mapHomotopyCategoryPlus ⋙ F') (K : HomotopyCategory.Plus A) :
    (biBeta F F' E τ).app K = DerivedCategory.Plus.Qh.map (τ.app K) ≫
      (biUnit F').app (E.mapHomotopyCategoryPlus.obj K) ≫
        (boundedInjectiveDerived F').map (E.mapDerivedCategoryPlusFactorsh.inv.app K) := by
  simp only [biBeta, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id]

private lemma biBeta_resolution
    (F : HomotopyCategory.Plus A ⥤ HomotopyCategory.Plus B)
    (F' : HomotopyCategory.Plus A' ⥤ HomotopyCategory.Plus B)
    (E : A ⥤ A') [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (τ : F ⟶ E.mapHomotopyCategoryPlus ⋙ F') (K : HomotopyCategory.Plus A)
    (J : HomotopyCategory.Plus (InjectiveObject A'))
    (k' : E.mapHomotopyCategoryPlus.obj K ⟶ biInj.obj J)
    [IsIso (DerivedCategory.Plus.Qh.map k')] :
    (biBeta F F' E τ).app K ≫
        (boundedInjectiveDerived F').map (E.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
        (boundedInjectiveResolutionIso F' (E.mapHomotopyCategoryPlus.obj K) J k').hom =
      DerivedCategory.Plus.Qh.map (τ.app K ≫ F'.map k') := by
  rw [biBeta_app]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [Functor.map_id, Category.id_comp]
  rw [biUnit_resolution, ← Functor.map_comp]

private lemma biComparison_iff
    (F : HomotopyCategory.Plus A ⥤ HomotopyCategory.Plus B)
    (F' : HomotopyCategory.Plus A' ⥤ HomotopyCategory.Plus B)
    (E : A ⥤ A') [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (τ : F ⟶ E.mapHomotopyCategoryPlus ⋙ F')
    (t : boundedInjectiveDerived F ⟶ E.mapDerivedCategoryPlus ⋙ boundedInjectiveDerived F') :
    BoundedInjectiveComparison F F' E τ t ↔
      biUnit F ≫ Functor.whiskerLeft DerivedCategory.Plus.Qh t = biBeta F F' E τ := by
  constructor
  · intro ht
    apply NatTrans.ext
    funext K
    let I := biEquiv.inverse.obj (DerivedCategory.Plus.Qh.obj K)
    let J := biEquiv.inverse.obj (DerivedCategory.Plus.Qh.obj
      (E.mapHomotopyCategoryPlus.obj K))
    obtain ⟨u, hu, _⟩ := boundedInjectiveComparison_exists_unique_lift E K I J
      (biAug K) (biAug (E.mapHomotopyCategoryPlus.obj K))
    have h := ht K I J (biAug K) (biAug (E.mapHomotopyCategoryPlus.obj K)) u hu
    change (biUnit F).app K ≫ t.app (DerivedCategory.Plus.Qh.obj K) = _
    apply (cancel_mono ((boundedInjectiveDerived F').map
      (E.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
        (boundedInjectiveResolutionIso F' (E.mapHomotopyCategoryPlus.obj K) J
          (biAug (E.mapHomotopyCategoryPlus.obj K))).hom)).mp
    rw [Category.assoc, ← h, ← Category.assoc, biUnit_resolution, ← Functor.map_comp]
    have hc : F.map (biAug K) ≫
        (τ.app (biInj.obj I) ≫ F'.map u) = τ.app K ≫
          F'.map (biAug (E.mapHomotopyCategoryPlus.obj K)) := by
      rw [← Category.assoc, τ.naturality, Category.assoc]
      dsimp only [Functor.comp_map]
      rw [← F'.map_comp, hu]
    rw [hc]
    exact (biBeta_resolution F F' E τ K J
      (biAug (E.mapHomotopyCategoryPlus.obj K))).symm
  · intro ht K I J k _ k' _ u hu
    have h := congr_app ht (biInj.obj I)
    have hn := t.naturality (DerivedCategory.Plus.Qh.map k)
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, biBeta_app] at h
    have hunit : (biUnit F).app (biInj.obj I) ≫ t.app
        (DerivedCategory.Plus.Qh.obj (biInj.obj I)) ≫
        (boundedInjectiveDerived F').map
          (E.mapDerivedCategoryPlusFactorsh.hom.app (biInj.obj I)) =
        DerivedCategory.Plus.Qh.map (τ.app (biInj.obj I)) ≫
          (biUnit F').app (E.mapHomotopyCategoryPlus.obj (biInj.obj I)) := by
      rw [← Category.assoc, h]
      simp only [Category.assoc]
      rw [← Functor.map_comp, Iso.inv_hom_id_app]
      erw [Functor.map_id, Category.comp_id]
    have hn' := (biUnit F').naturality u
    dsimp only [Functor.comp_map] at hn'
    have hcore : inv ((biUnit F).app (biInj.obj I)) ≫
        DerivedCategory.Plus.Qh.map (τ.app (biInj.obj I) ≫ F'.map u) =
        t.app (DerivedCategory.Plus.Qh.obj (biInj.obj I)) ≫
          (boundedInjectiveDerived F').map
            (E.mapDerivedCategoryPlusFactorsh.hom.app (biInj.obj I)) ≫
          (boundedInjectiveDerived F').map (DerivedCategory.Plus.Qh.map u) ≫
          inv ((biUnit F').app (biInj.obj J)) := by
      apply (cancel_epi ((biUnit F).app (biInj.obj I))).mp
      simp only [IsIso.hom_inv_id_assoc, Functor.map_comp]
      rw [reassoc_of% hunit, ← reassoc_of% hn']
      simp only [IsIso.hom_inv_id, Category.comp_id]
    rw [biResolution_hom, biResolution_hom]
    simp only [Category.assoc]
    rw [hcore, ← Category.assoc, ← Category.assoc, ← Category.assoc, hn]
    dsimp only [Functor.comp_map]
    simp only [Category.assoc]
    rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
    have hf := E.mapDerivedCategoryPlusFactorsh.hom.naturality k
    dsimp only [Functor.comp_map] at hf
    rw [hf]
    rw [Category.assoc, ← DerivedCategory.Plus.Qh.map_comp, hu]
    simp only [Functor.map_comp, Category.assoc]

private lemma biComparison_commShift
    (F : HomotopyCategory.Plus A ⥤ HomotopyCategory.Plus B)
    (F' : HomotopyCategory.Plus A' ⥤ HomotopyCategory.Plus B)
    [F.CommShift ℤ] [F'.CommShift ℤ]
    (E : A ⥤ A') [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (τ : F ⟶ E.mapHomotopyCategoryPlus ⋙ F') [NatTrans.CommShift τ ℤ]
    (t : boundedInjectiveDerived F ⟶ E.mapDerivedCategoryPlus ⋙ boundedInjectiveDerived F')
    (ht : BoundedInjectiveComparison F F' E τ t) : NatTrans.CommShift t ℤ := by
  have hfac := (biComparison_iff F F' E τ t).mp ht
  have hβ : NatTrans.CommShift (biBeta F F' E τ) ℤ := by
    dsimp only [biBeta]
    infer_instance
  have : IsIso (Functor.whiskerLeft biInj (biUnit F)) := by
    exact @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _
      (fun I ↦ biUnit_inj_isIso F I)
  have h₁ : NatTrans.CommShift (Functor.whiskerLeft biInj
      (Functor.whiskerLeft DerivedCategory.Plus.Qh t)) ℤ := by
    have heq : Functor.whiskerLeft biInj (Functor.whiskerLeft DerivedCategory.Plus.Qh t) =
        inv (Functor.whiskerLeft biInj (biUnit F)) ≫
          Functor.whiskerLeft biInj (biBeta F F' E τ) := by
      rw [IsIso.eq_inv_comp, ← Functor.whiskerLeft_comp, hfac]
    rw [heq]
    have : NatTrans.CommShift (inv (Functor.whiskerLeft biInj (biUnit F))) ℤ :=
      NatTrans.CommShift.of_isIso _ _
    infer_instance
  have h₂ : NatTrans.CommShift (Functor.whiskerLeft DerivedCategory.Plus.Qh t) ℤ := by
    refine NatTrans.CommShift.of_whiskerLeft _ biInj (fun K ↦ ?_)
    exact ⟨_, biAug K, by dsimp; infer_instance⟩
  refine NatTrans.CommShift.of_whiskerLeft _ DerivedCategory.Plus.Qh (fun X ↦ ?_)
  exact ⟨_, (DerivedCategory.Plus.Qh.objObjPreimageIso X).inv, inferInstance⟩

private lemma biComparison_fac
    (F : HomotopyCategory.Plus A ⥤ HomotopyCategory.Plus B)
    (F' : HomotopyCategory.Plus A' ⥤ HomotopyCategory.Plus B)
    (E : A ⥤ A') [E.Additive]
    [hElim : PreservesFiniteLimits E] [hEcolim : PreservesFiniteColimits E]
    (τ : F ⟶ E.mapHomotopyCategoryPlus ⋙ F')
    (t : boundedInjectiveDerived F ⟶ E.mapDerivedCategoryPlus ⋙ boundedInjectiveDerived F')
    (ht : BoundedInjectiveComparison F F' E τ t) (K : HomotopyCategory.Plus A) :
    (biUnit F).app K ≫ t.app (DerivedCategory.Plus.Qh.obj K) ≫
        (boundedInjectiveDerived F').map (E.mapDerivedCategoryPlusFactorsh.hom.app K) =
      DerivedCategory.Plus.Qh.map (τ.app K) ≫
        (biUnit F').app (E.mapHomotopyCategoryPlus.obj K) := by
  have h := congr_app ((biComparison_iff F F' E τ t).mp ht) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, biBeta_app] at h
  rw [← Category.assoc, h]
  simp only [Category.assoc]
  rw [← Functor.map_comp, Iso.inv_hom_id_app]
  erw [Functor.map_id, Category.comp_id]

/-- Descent of a shift-compatible comparison on bounded below homotopy categories.
Source: Stacks, Tag 05TK, the adjacent resolution discussion, and the comparison calculations
in Steps 1--8 of the DAG node.
Proof: (1) Specialize `lem-trf-filtered-localization-injective-model` to `[0,0]`.
(2) Use the adjoint injective equivalence and its conjugate shifts; its inverse is exact by
`lem-sf-triangulated-right-adjoint`. This gives the displayed concrete `RF,RF'`.
(3) Resolve `K,EK` by `lem-sc-bounded-below-injective-resolution-existence`; exact `E`
preserves quasi-isomorphisms by `lem-sf-exact-functor-derived-triangulated`.
(4) Lift `Q(k') Q(E(k))⁻¹` by `lem-weil-pbc-kinjective-hom-derived`; bounded below injectives
are K-injective by `lem-weil-pbc-bounded-below-injectives-kinjective`. Apply `F'(u) τ_I`.
(5) For any derived arrow `α`, lift it to maps `a:I_K→I_L`, `b:J_K→J_L`. Their localized
square gives `b u_K = u_L E(a)` by the same Hom bijection, and naturality of `τ` gives the
naturality square. This includes every `K→L[1]`.
(6) The unique comparisons between two resolutions are homotopy equivalences. The same
square with `α=1` identifies the formula for all `I,J,k,k',u`, and proves uniqueness.
(7) Compute on shifted resolutions with comparison `u[n]`. Naturality of the shift
isomorphism of `F'` and shift compatibility of `τ` give the induced shift square for every
integer `n`; Step 6 transfers it to arbitrary chosen resolutions.
(8) Identity uses `u=1`. For composable comparisons use `w=E'(u)≫v`; naturality of the second
transformation identifies the two formulas. Associativity gives the triple comparison.
The identity and composition equalities are stated below.
(blueprint: lem-amb-bounded-injective-fibre-descent) -/
theorem boundedInjectiveFibreDescent
    (F : HomotopyCategory.Plus A ⥤ HomotopyCategory.Plus B)
    (F' : HomotopyCategory.Plus A' ⥤ HomotopyCategory.Plus B)
    [F.CommShift ℤ] [F.IsTriangulated] [F'.CommShift ℤ] [F'.IsTriangulated]
    (E : A ⥤ A') [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (τ : F ⟶ E.mapHomotopyCategoryPlus ⋙ F') [NatTrans.CommShift τ ℤ] :
    ∃! t : boundedInjectiveDerived F ⟶ E.mapDerivedCategoryPlus ⋙ boundedInjectiveDerived F',
      BoundedInjectiveComparison F F' E τ t ∧ NatTrans.CommShift t ℤ := by
  let t := (boundedInjectiveDerived F).rightDerivedDesc (biUnit F)
    (HomotopyCategory.Plus.quasiIso A) _ (biBeta F F' E τ)
  have ht : BoundedInjectiveComparison F F' E τ t :=
    (biComparison_iff F F' E τ t).mpr (Functor.rightDerived_fac _ _ _ _ _)
  refine ⟨t, ⟨ht, biComparison_commShift F F' E τ t ht⟩, ?_⟩
  intro s hs
  apply Functor.rightDerived_ext _ (biUnit F) (HomotopyCategory.Plus.quasiIso A)
  rw [(biComparison_iff F F' E τ s).mp hs.1,
    (biComparison_iff F F' E τ t).mp ht]

/-- Identity comparison data, with the canonical termwise identity isomorphism inserted.
Source: Step 8, identity calculation following Stacks, Tag 05TK.
(blueprint: lem-amb-bounded-injective-fibre-descent) -/
def boundedInjectiveIdentityDatum
    (F : HomotopyCategory.Plus A ⥤ HomotopyCategory.Plus B) :
    F ⟶ (𝟭 A).mapHomotopyCategoryPlus ⋙ F :=
  (Functor.leftUnitor F).inv ≫
    Functor.whiskerRight (Functor.mapHomotopyCategoryPlusIdIso A).inv F

/-- Descent respects identity data, after the canonical identification `D⁺(id) ≅ id`.
Source: Step 8, Stacks, Tag 05TK.
Proof: Use identical resolutions and identity comparison `u=1`. The resolution formula is
then the identity, and Step 6 gives the equality for all choices. Every derived object has
an injective representative, so the equality holds at every object.
(blueprint: lem-amb-bounded-injective-fibre-descent) -/
theorem boundedInjectiveComparison_id
    (F : HomotopyCategory.Plus A ⥤ HomotopyCategory.Plus B)
    [F.CommShift ℤ] [F.IsTriangulated]
    (t : boundedInjectiveDerived F ⟶
      (𝟭 A).mapDerivedCategoryPlus ⋙ boundedInjectiveDerived F)
    (ht : BoundedInjectiveComparison F F (𝟭 A) (boundedInjectiveIdentityDatum F) t)
    (X : DerivedCategory.Plus A) :
    t.app X ≫ (boundedInjectiveDerived F).map
        ((Functor.mapDerivedCategoryPlusIdIso A).hom.app X) = 𝟙 _ := by
  let c : boundedInjectiveDerived F ⟶ boundedInjectiveDerived F :=
    t ≫ Functor.whiskerRight (Functor.mapDerivedCategoryPlusIdIso A).hom
      (boundedInjectiveDerived F) ≫ (Functor.leftUnitor _).hom
  have hc : c = 𝟙 _ := by
    apply Functor.rightDerived_ext _ (biUnit F) (HomotopyCategory.Plus.quasiIso A)
    apply NatTrans.ext
    funext K
    change (biUnit F).app K ≫ (t.app _ ≫ _ ≫ 𝟙 _) = (biUnit F).app K ≫ 𝟙 _
    simp only [Category.comp_id, Functor.whiskerRight_app]
    rw [Functor.mapDerivedCategoryPlusIdIso_hom_app_factorsh]
    have h := biComparison_fac F F (𝟭 A) (boundedInjectiveIdentityDatum F) t ht K
    rw [h]
    simp only [boundedInjectiveIdentityDatum, NatTrans.comp_app, Functor.leftUnitor_inv_app,
      Functor.whiskerRight_app, Functor.mapHomotopyCategoryPlusIdIso_inv_app_eq_id,
      Functor.map_id, Category.id_comp]
    erw [DerivedCategory.Plus.Qh.map_id, Category.id_comp]
    rfl
  have h := congr_app hc X
  dsimp only [c, NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    NatTrans.id_app] at h
  erw [Category.comp_id] at h
  exact h

variable {A'' : Type uA''} [Category.{vA''} A''] [Abelian A''] [EnoughInjectives A'']
  [HasDerivedCategory.{wA''} A'']

/-- Composite comparison data, using the canonical termwise composition isomorphism.
Source: Step 8, comparison/pasting calculation extending Stacks, Tag 05TK.
(blueprint: lem-amb-bounded-injective-fibre-descent) -/
def boundedInjectiveCompositeDatum
    (F : HomotopyCategory.Plus A ⥤ HomotopyCategory.Plus B)
    (F' : HomotopyCategory.Plus A' ⥤ HomotopyCategory.Plus B)
    (F'' : HomotopyCategory.Plus A'' ⥤ HomotopyCategory.Plus B)
    (E : A ⥤ A') (E' : A' ⥤ A'') [E.Additive] [E'.Additive]
    (τ : F ⟶ E.mapHomotopyCategoryPlus ⋙ F')
    (σ : F' ⟶ E'.mapHomotopyCategoryPlus ⋙ F'') :
    F ⟶ (E ⋙ E').mapHomotopyCategoryPlus ⋙ F'' :=
  τ ≫ Functor.whiskerLeft E.mapHomotopyCategoryPlus σ ≫
    (Functor.associator E.mapHomotopyCategoryPlus E'.mapHomotopyCategoryPlus F'').inv ≫
    Functor.whiskerRight
      (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (E ⋙ E'))).hom F''

/-- Descent respects composition, with the canonical isomorphism
`D⁺(E⋙E') ≅ D⁺E⋙D⁺E'` inserted. Together with the identity law this includes all iterated
compositions, since natural-transformation composition and the canonical comparison
isomorphisms are associative.
Source: Step 8, comparison/pasting calculation following Stacks, Tag 05TK.
Proof: Resolve `K,EK,E'EK` by `I,J,H` and choose `u:EI→J`, `v:E'J→H`.
Then `w=E'(u)≫v` satisfies the composite augmentation equation. Naturality of `σ` at `u`
identifies `τ_I≫F'(u)≫σ_J≫F''(v)` with
`τ_I≫σ_EI≫F''(E'(u)≫v)`. Apply localization and the resolution formula; Step 6 makes
this independent of all choices. Naturality of the localization comparison inserts
`mapDerivedCategoryPlusCompIso`. No injectivity of `EI` or `E'J` is used.
(blueprint: lem-amb-bounded-injective-fibre-descent) -/
theorem boundedInjectiveComparison_comp
    (F : HomotopyCategory.Plus A ⥤ HomotopyCategory.Plus B)
    (F' : HomotopyCategory.Plus A' ⥤ HomotopyCategory.Plus B)
    (F'' : HomotopyCategory.Plus A'' ⥤ HomotopyCategory.Plus B)
    [F.CommShift ℤ] [F.IsTriangulated] [F'.CommShift ℤ] [F'.IsTriangulated]
    [F''.CommShift ℤ] [F''.IsTriangulated]
    (E : A ⥤ A') (E' : A' ⥤ A'') [E.Additive] [E'.Additive]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    [PreservesFiniteLimits E'] [PreservesFiniteColimits E']
    (τ : F ⟶ E.mapHomotopyCategoryPlus ⋙ F') [NatTrans.CommShift τ ℤ]
    (σ : F' ⟶ E'.mapHomotopyCategoryPlus ⋙ F'') [NatTrans.CommShift σ ℤ]
    (t : boundedInjectiveDerived F ⟶ E.mapDerivedCategoryPlus ⋙ boundedInjectiveDerived F')
    (s : boundedInjectiveDerived F' ⟶ E'.mapDerivedCategoryPlus ⋙ boundedInjectiveDerived F'')
    (r : boundedInjectiveDerived F ⟶
      (@Functor.mapDerivedCategoryPlus A A'' _ _ _ _ _ _ (E ⋙ E') _
        (comp_preservesFiniteLimits E E') (comp_preservesFiniteColimits E E')) ⋙
          boundedInjectiveDerived F'')
    (ht : BoundedInjectiveComparison F F' E τ t)
    (hs : BoundedInjectiveComparison F' F'' E' σ s)
    (hr : BoundedInjectiveComparison F F'' (E ⋙ E')
      (hElim := comp_preservesFiniteLimits E E')
      (hEcolim := comp_preservesFiniteColimits E E')
      (boundedInjectiveCompositeDatum F F' F'' E E' τ σ) r)
    (X : DerivedCategory.Plus A) :
    r.app X ≫ (boundedInjectiveDerived F'').map
        ((Functor.mapDerivedCategoryPlusCompIso E E').hom.app X) =
      t.app X ≫ s.app (E.mapDerivedCategoryPlus.obj X) := by
  let c₁ : boundedInjectiveDerived F ⟶
      E.mapDerivedCategoryPlus ⋙ E'.mapDerivedCategoryPlus ⋙ boundedInjectiveDerived F'' :=
    r ≫ Functor.whiskerRight (Functor.mapDerivedCategoryPlusCompIso E E').hom
      (boundedInjectiveDerived F'') ≫ (Functor.associator _ _ _).hom
  let c₂ : boundedInjectiveDerived F ⟶
      E.mapDerivedCategoryPlus ⋙ E'.mapDerivedCategoryPlus ⋙ boundedInjectiveDerived F'' :=
    t ≫ Functor.whiskerLeft E.mapDerivedCategoryPlus s
  have hc : c₁ = c₂ := by
    apply Functor.rightDerived_ext _ (biUnit F) (HomotopyCategory.Plus.quasiIso A)
    apply NatTrans.ext
    funext K
    change (biUnit F).app K ≫ (r.app _ ≫ _ ≫ 𝟙 _) =
      (biUnit F).app K ≫ (t.app _ ≫ s.app _)
    simp only [Functor.whiskerRight_app, Category.comp_id]
    let q := (boundedInjectiveDerived F'').mapIso
      (E'.mapDerivedCategoryPlus.mapIso (E.mapDerivedCategoryPlusFactorsh.app K) ≪≫
        E'.mapDerivedCategoryPlusFactorsh.app (E.mapHomotopyCategoryPlus.obj K))
    apply (cancel_mono q.hom).mp
    dsimp only [q, Functor.mapIso_hom, Iso.trans_hom]
    rw [Functor.map_comp]
    have hcomp := Functor.mapDerivedCategoryPlusCompIso_hom_app_factorsh E E' K
    have h₁ := biComparison_fac F F'' (E ⋙ E')
      (hElim := comp_preservesFiniteLimits E E')
      (hEcolim := comp_preservesFiniteColimits E E')
      (boundedInjectiveCompositeDatum F F' F'' E E' τ σ) r hr K
    have h₂ := biComparison_fac F F' E τ t ht K
    have h₃ := biComparison_fac F' F'' E' σ s hs (E.mapHomotopyCategoryPlus.obj K)
    have hn := s.naturality (E.mapDerivedCategoryPlusFactorsh.hom.app K)
    dsimp only [Functor.comp_map] at hn
    simp only [Category.assoc]
    rw [← Functor.map_comp_assoc, ← Functor.map_comp]
    simp only [Category.assoc, Iso.app_hom] at ⊢
    rw [hcomp, h₁]
    rw [← reassoc_of% hn, reassoc_of% h₂, h₃]
    rw [← DerivedCategory.Plus.Qh.map_comp_assoc]
    congr 2
    simp only [boundedInjectiveCompositeDatum, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.associator_inv_app, Functor.whiskerRight_app,
      Functor.mapHomotopyCategoryPlusCompIso_refl_hom_app, Functor.map_id]
    erw [Category.id_comp, Category.comp_id]
  have h := congr_app hc X
  dsimp only [c₁, c₂, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app] at h
  erw [Category.comp_id] at h
  exact h

end CategoryTheory
