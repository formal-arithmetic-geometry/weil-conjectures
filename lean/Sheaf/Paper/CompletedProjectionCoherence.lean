/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q92
-/
module

public import Sheaf.Paper.CompletedProjectionData
public import Sheaf.Paper.ProEtaleConstantReductionTower
public import Sheaf.Paper.ProjectionMateExact
public import Sheaf.Paper.RingedExchangeTensorCoherence
public import Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison
public import Sheaf.CategoryTheory.RingedToposMorphism
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.CategoryTheory.DiagramSiteRealization
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.Limits
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import Sheaf.Algebra.Homology.RingedInternalHomDerivedComplete
import Sheaf.Paper.QuotientTowerAugmentationPullback
import Sheaf.Paper.PerfectQuotientProjection
import Sheaf.Paper.FiniteQuotientTensorProjection

/-!
# Completion coherence of the projection mate

Source: Stacks Project, sites-cohomology.tex, Tags 07A6, 0B56, 0941 and 0A07;
proetale.tex, Tags 099M and 099N
(blueprint: lem-pur-compact-support-completed-projection-coherence).

All sites, strict quotient towers, units, adjunctions and coefficient comparisons
are the existing AdicSites constructions. The additional records only present
their canonical tensor comparisons. The ordinary tensor presentation is an input,
as in the landed ringed-topos tensor theorems; the completed and finite comparisons
are conclusions, not extra hypotheses.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open CategoryTheory.ConstantCompletion
namespace CategoryTheory.AdicSites.ProjectionCoherence

variable {Y X : Site.{u}} {f : Morphism Y X} {A : Type u} [CommRing A]
  [IsNoetherianRing A] {I : Ideal A}

section TensorDescent
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w
private theorem flat_localization (A : RingedTensorCorner.{u, w}) :
    let P : ObjectProperty (HomotopyCategory A.mateModules (ComplexShape.up ℤ)) :=
      fun K ↦ A.mateFlat K.as
    (P.ι ⋙ DerivedCategory.Qh).IsLocalization
      ((HomotopyCategory.quasiIso A.mateModules (ComplexShape.up ℤ)).inverseImage P.ι) := by
  obtain ⟨P, hP, ⟨F, hF, ⟨e⟩⟩, _⟩ :=
    site_derived_tensor_descent_independentCoefficients.{u, u, u, w, 0, 0} A.topology A.ring
  have heq : P = (fun K ↦ A.mateFlat K.as) := by
    funext K
    refine propext ((hP K).trans (and_congr
      (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat K.as)
      (forall_congr' fun n ↦ ?_)))
    let := isMonoidal_W_independentCoefficients A.ring
    let := monoidalCategory A.ring
    exact ⟨fun h ↦ (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso A.ring _) h,
      fun h ↦ (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso A.ring _).symm h⟩
  subst P
  let := hF
  exact Functor.IsLocalization.of_equivalence_target _ _ _ F.asEquivalence e

private theorem iso_descent
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) [F.Full] [F.EssSurj] (U V : D ⥤ E) (e : F ⋙ U ≅ F ⋙ V) :
    ∃ e' : U ≅ V, Functor.isoWhiskerLeft F e' = e := by
  let e' : U ≅ V := NatIso.ofComponents (fun X ↦
    U.mapIso (F.objObjPreimageIso X).symm ≪≫ e.app (F.objPreimage X) ≪≫
      V.mapIso (F.objObjPreimageIso X)) (by
    intro X Y f
    apply (cancel_epi (U.map (F.objObjPreimageIso X).hom)).1
    apply (cancel_mono (V.map (F.objObjPreimageIso Y).inv)).1
    have hn := e.hom.naturality (F.preimage
      ((F.objObjPreimageIso X).hom ≫ f ≫ (F.objObjPreimageIso Y).inv))
    dsimp only [Functor.comp_map] at hn
    rw [F.map_preimage] at hn
    simpa [Category.assoc] using hn
  )
  refine ⟨e', ?_⟩
  apply Iso.ext
  ext X
  apply (cancel_epi (U.map (F.objObjPreimageIso (F.obj X)).hom)).1
  have hn := e.hom.naturality
    (F.preimage (F.objObjPreimageIso (F.obj X)).hom)
  dsimp only [Functor.comp_map] at hn
  rw [F.map_preimage] at hn
  simpa [e', Category.assoc] using hn.symm


private def flatQuotient (A : RingedTensorCorner.{u, w}) :
    A.mateFlat.FullSubcategory ⥤
      ObjectProperty.FullSubcategory
        (fun K : HomotopyCategory A.mateModules (ComplexShape.up ℤ) ↦ A.mateFlat K.as) where
  obj K := ⟨(HomotopyCategory.quotient _ _).obj K.obj, K.property⟩
  map f := ObjectProperty.homMk ((HomotopyCategory.quotient _ _).map f.hom)

private instance flatQuotient_full (A : RingedTensorCorner.{u, w}) :
    (flatQuotient A).Full where
  map_surjective f := ⟨ObjectProperty.homMk f.hom.out, by
    apply ObjectProperty.hom_ext
    change (HomotopyCategory.quotient A.mateModules (ComplexShape.up ℤ)).map
      f.hom.out = f.hom
    exact HomotopyCategory.quotient_map_out f.hom⟩

private instance flatQuotient_essSurj (A : RingedTensorCorner.{u, w}) :
    (flatQuotient A).EssSurj where
  mem_essImage X := ⟨⟨X.obj.as, X.property⟩, ⟨Iso.refl _⟩⟩

set_option maxHeartbeats 800000 in
-- Descending through both a quotient and a localization needs extra elaboration fuel.
private theorem localization_iso_descent
    {C H D E : Type*} [Category C] [Category H] [Category D] [Category E]
    (F : C ⥤ H) [F.Full] [F.EssSurj]
    (L : H ⥤ D) (W : MorphismProperty H) [L.IsLocalization W]
    (K : C ⥤ D) (eK : F ⋙ L ≅ K)
    (U V : D ⥤ E) (e : K ⋙ U ≅ K ⋙ V) :
    ∃ t : U ≅ V, Functor.isoWhiskerLeft K t = e := by
  let ecomp : F ⋙ (L ⋙ U) ≅ F ⋙ (L ⋙ V) :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight eK U ≪≫ e ≪≫
      (Functor.isoWhiskerRight eK V).symm ≪≫ Functor.associator _ _ _
  obtain ⟨eh, heh⟩ := iso_descent F _ _ ecomp
  let t := Localization.liftNatIso L W _ _ U V eh
  refine ⟨t, ?_⟩
  apply Iso.ext
  ext X
  have hh := NatTrans.congr_app (congrArg Iso.hom heh) X
  have ht : t.hom.app (L.obj (F.obj X)) = eh.hom.app (F.obj X) := by
    change (Localization.liftNatTrans L W _ _ U V eh.hom).app (L.obj (F.obj X)) = _
    rw [Localization.liftNatTrans_app]
    simp
  have hn := t.hom.naturality (eK.hom.app X)
  dsimp only [Functor.comp_obj] at hn
  rw [ht] at hn
  have hh' : eh.hom.app (F.obj X) =
      U.map (eK.hom.app X) ≫ e.hom.app X ≫ V.map (eK.inv.app X) := by
    simpa [ecomp, Category.assoc] using hh
  rw [hh'] at hn
  simp only [Category.assoc, ← V.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id] at hn
  erw [Category.comp_id] at hn
  apply (cancel_epi (U.map (eK.hom.app X))).1
  simpa only [CategoryTheory.Category.comp_id, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app] using hn

private theorem flat_product_iso_descent (B : RingedTensorCorner.{u, w})
    {E : Type*} [Category E] (U V : B.mateDerived × B.mateDerived ⥤ E)
    (e : ((B.mateFlat.ι ⋙ DerivedCategory.Q).prod
      (B.mateFlat.ι ⋙ DerivedCategory.Q)) ⋙ U ≅
      ((B.mateFlat.ι ⋙ DerivedCategory.Q).prod (B.mateFlat.ι ⋙ DerivedCategory.Q)) ⋙ V) :
    Nonempty (U ≅ V) := by
  let P : ObjectProperty (HomotopyCategory B.mateModules (ComplexShape.up ℤ)) :=
    fun K ↦ B.mateFlat K.as
  let F := flatQuotient B
  let L := P.ι ⋙ DerivedCategory.Qh
  let K := B.mateFlat.ι ⋙ DerivedCategory.Q
  let eK : F ⋙ L ≅ K := NatIso.ofComponents
    (fun X ↦ (DerivedCategory.quotientCompQhIso B.mateModules).app X.obj) (by
      intro X Y f
      exact (DerivedCategory.quotientCompQhIso B.mateModules).hom.naturality f.hom)
  let W := (HomotopyCategory.quasiIso B.mateModules (ComplexShape.up ℤ)).inverseImage P.ι
  let : L.IsLocalization W := flat_localization B
  let : (F.prod F).Full :=
    { map_surjective := fun h ↦ ⟨Prod.mkHom (F.preimage h.1) (F.preimage h.2), by
        apply Prod.hom_ext <;> exact F.map_preimage _⟩ }
  let : (F.prod F).EssSurj :=
    { mem_essImage := fun X ↦ ⟨(F.objPreimage X.1, F.objPreimage X.2),
        ⟨Iso.prod (F.objObjPreimageIso X.1) (F.objObjPreimageIso X.2)⟩⟩ }
  obtain ⟨t, _⟩ := localization_iso_descent (F.prod F) (L.prod L) (W.prod W)
    (K.prod K) (NatIso.prod eK eK) U V e
  exact ⟨t⟩

private theorem tensor_closed_comparison (B : RingedTensorCorner.{u, w})
    (m : RingedTensorModel B) :
    ∃ S : WeilConjectures.CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{u, u, u, w} B.topology B.ring),
      ∃ _β : @SymmetricCategory B.mateDerived _ S.monoidal,
        Nonempty (B.tensor ≅ S.tensor) := by
  obtain ⟨S, T, β, _⟩ :=
    ringedDerived_closed_symmetric_monoidal.{u, u, u, w} B.topology B.ring
  let ic : B.mateFlat.FullSubcategory ⥤ ObjectProperty.FullSubcategory
      (CochainComplex.IsKFlatIndependentCoefficients (J := B.topology) (R := B.ring)) :=
    { obj := fun P ↦ ⟨P.obj,
        (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P.obj).2 P.property.1⟩
      map := fun h ↦ ObjectProperty.homMk h.hom }
  have rep : ((B.mateFlat.ι ⋙ DerivedCategory.Q).prod
      (B.mateFlat.ι ⋙ DerivedCategory.Q)) ⋙ B.tensor ≅
      ((B.mateFlat.ι ⋙ DerivedCategory.Q).prod
        (B.mateFlat.ι ⋙ DerivedCategory.Q)) ⋙ S.tensor :=
    m.representative.symm ≪≫ Functor.isoWhiskerLeft (ic.prod ic) T.comparison
  exact ⟨S, β, flat_product_iso_descent B _ _ rep⟩

end TensorDescent

set_option backward.isDefEq.respectTransparency false in
private theorem completion_map_isIso (T : Site.{u})
    {V W : T.derived A} (q : V ⟶ W)
    (hq : ∀ Z : T.derived A, T.IsComplete A I Z →
      Function.Bijective (fun a : W ⟶ Z ↦ q ≫ a)) :
    IsIso ((T.completion A I).map q) := by
  let C := T.completion A I
  let η := T.unit A I
  have hC := (T.completion_properties A I).1
  have hη := (T.completion_properties A I).2.1
  obtain ⟨p, hp⟩ := (hq (C.obj V) (hC V)).2 (η.app V)
  obtain ⟨r, hr⟩ := (hη W (C.obj V) (hC V)).2 p
  change η.app W ≫ r = p at hr
  change q ≫ p = η.app V at hp
  have hl : C.map q ≫ r = 𝟙 _ := by
    apply (hη V (C.obj V) (hC V)).1
    change η.app V ≫ (C.map q ≫ r) = η.app V ≫ 𝟙 _
    erw [← reassoc_of% η.naturality, hr, hp, Category.comp_id]
  have hr' : r ≫ C.map q = 𝟙 _ := by
    apply (hη W (C.obj W) (hC W)).1
    apply (hq (C.obj W) (hC W)).1
    change q ≫ η.app W ≫ (r ≫ C.map q) = q ≫ η.app W ≫ 𝟙 _
    erw [reassoc_of% η.naturality, reassoc_of% hl]
    simp only [Category.comp_id]
    exact (η.naturality q).symm
  exact ⟨⟨r, hl, hr'⟩⟩

omit [IsNoetherianRing A] in
set_option backward.isDefEq.respectTransparency false in
private theorem complete_rhom (T : Site.{u}) (V Z : T.derived A)
    (hZ : T.IsComplete A I Z) :
    T.IsComplete A I
      ((derivedInternalHomOfUniverses.{u, u, u, u + 1} T.topology (T.ring A)).obj
        (op V, Z)) := by
  let : ∀ U : T.objects, HasDerivedCategory.{u + 1} (ringedSiteModules.{u}
      ((sheafCompose (T.topology.over U) (forget₂ CommRingCat RingCat)).obj
        ((T.ring A).over U))) := fun _ ↦ HasDerivedCategory.standard _
  let J := kernelIdeal (quotient T.topology A I 0)
  have : Mono J.inclusion := by
    constructor
    intro W a b h
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    exact congrArg (fun k ↦ k.val.app U z) h
  exact isLocallyDerivedRingedIdealComplete_derivedInternalHom T.topology (T.ring A)
    J.module J.inclusion V Z hZ

open MonoidalCategory in
set_option backward.isDefEq.respectTransparency false in
private theorem completion_closed_tensor_left (T : Site.{u})
    (S : WeilConjectures.CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{u, u, u, u + 1} T.topology (T.ring A)))
    (V W : T.derived A) :
    IsIso ((T.completion A I).map
      (S.tensor.map (Prod.mkHom ((T.unit A I).app V) (𝟙 W)))) := by
  let : MonoidalCategory (T.derived A) := S.monoidal
  let C : T.derived A ⥤ T.derived A := T.completion A I
  let η : 𝟭 (T.derived A) ⟶ C := T.unit A I
  change IsIso (C.map ((η.app V) ⊗ₘ 𝟙 W))
  simp only [tensorHom_id]
  apply completion_map_isIso T
  intro Z hZ
  have h := (T.completion_properties A I).2.1 V _ (complete_rhom T W Z hZ)
  constructor
  · intro a b hab
    apply ((S.adjunction W).homEquiv _ _).injective
    apply h.1
    dsimp only at hab ⊢
    erw [← (S.adjunction W).homEquiv_naturality_left,
      ← (S.adjunction W).homEquiv_naturality_left, hab]
    rfl
  · intro a
    obtain ⟨b, hb⟩ := h.2 ((S.adjunction W).homEquiv _ _ a)
    refine ⟨((S.adjunction W).homEquiv _ _).symm b, ?_⟩
    apply ((S.adjunction W).homEquiv _ _).injective
    dsimp only
    erw [(S.adjunction W).homEquiv_naturality_left, Equiv.apply_symm_apply]
    exact hb

open MonoidalCategory in
set_option backward.isDefEq.respectTransparency false in
private theorem completion_closed_tensor_right (T : Site.{u})
    (S : WeilConjectures.CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{u, u, u, u + 1} T.topology (T.ring A)))
    (β : @SymmetricCategory (T.derived A) _ S.monoidal)
    (V W : T.derived A) :
    IsIso ((T.completion A I).map
      (S.tensor.map (Prod.mkHom (𝟙 V) ((T.unit A I).app W)))) := by
  let : MonoidalCategory (T.derived A) := S.monoidal
  let := β
  have := completion_closed_tensor_left T S W V (I := I)
  have hn := congrArg ((T.completion A I).map)
    (BraidedCategory.braiding_naturality (𝟙 V) ((T.unit A I).app W))
  simp only [Functor.map_comp] at hn
  change (T.completion A I).map
      (S.tensor.map (Prod.mkHom (𝟙 V) ((T.unit A I).app W))) ≫
      (T.completion A I).map (β_ V ((T.completion A I).obj W)).hom =
    (T.completion A I).map (β_ V W).hom ≫
      (T.completion A I).map
        (S.tensor.map (Prod.mkHom ((T.unit A I).app W) (𝟙 V))) at hn
  exact IsIso.of_isIso_fac_right hn

set_option backward.isDefEq.respectTransparency false in
private theorem completion_tensor_right (T : Site.{u})
    (t : T.derived A × T.derived A ⥤ T.derived A)
    (m : RingedTensorModel (corner T A t)) (V W : T.derived A) :
    IsIso ((T.completion A I).map
      (t.map (Prod.mkHom (𝟙 V) ((T.unit A I).app W)))) := by
  obtain ⟨S, β, ⟨e⟩⟩ := tensor_closed_comparison (corner T A t) m
  have := completion_closed_tensor_right T S β V W (I := I)
  have hn := congrArg ((T.completion A I).map)
    (e.hom.naturality (Prod.mkHom (𝟙 V) ((T.unit A I).app W)))
  simp only [Functor.map_comp] at hn
  exact IsIso.of_isIso_fac_right hn

set_option backward.isDefEq.respectTransparency false in
private theorem completion_tensor_both (T : Site.{u})
    (t : T.derived A × T.derived A ⥤ T.derived A)
    (m : RingedTensorModel (corner T A t)) (V W : T.derived A) :
    IsIso ((T.completion A I).map
      (t.map (Prod.mkHom ((T.unit A I).app V) ((T.unit A I).app W)))) := by
  obtain ⟨S, β, ⟨e⟩⟩ := tensor_closed_comparison (corner T A t) m
  have := completion_closed_tensor_left T S V W (I := I)
  have := completion_closed_tensor_right T S β ((T.completion A I).obj V) W (I := I)
  have hcomp : S.tensor.map (Prod.mkHom ((T.unit A I).app V) ((T.unit A I).app W)) =
      S.tensor.map (Prod.mkHom ((T.unit A I).app V) (𝟙 W)) ≫
        S.tensor.map (Prod.mkHom (𝟙 _) ((T.unit A I).app W)) := by
    rw [← S.tensor.map_comp]
    congr 1
    ext <;> simp
  have : IsIso ((T.completion A I).map
      (S.tensor.map (Prod.mkHom ((T.unit A I).app V) ((T.unit A I).app W)))) := by
    rw [hcomp, Functor.map_comp]
    infer_instance
  have hn := congrArg ((T.completion A I).map)
    (e.hom.naturality (Prod.mkHom ((T.unit A I).app V) ((T.unit A I).app W)))
  simp only [Functor.map_comp] at hn
  exact IsIso.of_isIso_fac_right hn

set_option backward.isDefEq.respectTransparency false in
private theorem completion_pull_unit_isIso (M : Y.derived A) :
    IsIso ((X.completion A I).map ((f.pull A).map ((Y.unit A I).app M))) := by
  apply completion_map_isIso X
  intro Z hZ
  have h := (Y.completion_properties A I).2.1 M ((f.push A).obj Z)
    (f.push_complete A I Z hZ)
  constructor
  · intro a b hab
    apply ((f.adj A).homEquiv _ _).injective
    apply h.1
    dsimp only at hab ⊢
    rw [← (f.adj A).homEquiv_naturality_left,
      ← (f.adj A).homEquiv_naturality_left, hab]
  · intro a
    obtain ⟨b, hb⟩ := h.2 ((f.adj A).homEquiv _ _ a)
    refine ⟨((f.adj A).homEquiv _ _).symm b, ?_⟩
    apply ((f.adj A).homEquiv _ _).injective
    rw [(f.adj A).homEquiv_naturality_left, Equiv.apply_symm_apply]
    exact hb

set_option backward.isDefEq.respectTransparency false in
private theorem completed_tensor_exists (o : TensorData f A) :
    Nonempty (CompletedTensor I o) := by
  let C := X.completion A I
  let η := X.unit A I
  have hi (V W : X.derived A) :
      IsIso (C.map (o.tensorX.map (Prod.mkHom (𝟙 V) (η.app W)))) :=
    completion_tensor_right X o.tensorX o.modelX V W
  have hp (M : Y.derived A) :
      IsIso (C.map ((f.pull A).map ((Y.unit A I).app M))) :=
    completion_pull_unit_isIso M
  have ht (V W : X.derived A) :
      IsIso (C.map (o.tensorX.map (Prod.mkHom (η.app V) (η.app W)))) :=
    completion_tensor_both X o.tensorX o.modelX V W
  refine ⟨{
    insertRight := fun V W ↦ asIso (C.map
      (o.tensorX.map (Prod.mkHom (𝟙 V) (η.app W))))
    insertRight_eq := fun _ _ ↦ rfl
    pullInsert := fun M ↦ asIso (C.map ((f.pull A).map ((Y.unit A I).app M)))
    pullInsert_eq := fun _ ↦ rfl
    comparison := fun M N ↦
      (asIso (C.map ((f.pull A).map ((Y.unit A I).app (o.tensorY.obj (M, N)))))).symm ≪≫
      C.mapIso (o.comparison.app (M, N)) ≪≫
      asIso (C.map (o.tensorX.map (Prod.mkHom (η.app ((f.pull A).obj M))
        (η.app ((f.pull A).obj N)))))
    comparison_eq := ?_ }⟩
  intro M N
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, asIso_hom,
    ← Functor.map_comp]
  simp only [Functor.map_comp, asIso_inv]
  erw [IsIso.hom_inv_id_assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem completed_unique {o : TensorData f A} (b : CompletedTensor I o)
    (hb : b.UnitEquation) : b.Unique := by
  intro H K p hp
  apply ((Y.completion_properties A I).2.1 _ _
    (f.push_complete A I _ ((X.completion_properties A I).1 _))).1
  exact hp.trans (hb H K).symm

omit [IsNoetherianRing A] in
private theorem projection_naturality (o : TensorData f A)
    {H H' : X.derived A} {K K' : Y.derived A} (h : H ⟶ H') (k : K ⟶ K') :
    o.tensorY.map (Prod.mkHom ((f.push A).map h) k) ≫ o.projection H' K' =
      o.projection H K ≫ (f.push A).map
        (o.tensorX.map (Prod.mkHom h ((f.pull A).map k))) := by
  apply (f.adj A).homEquiv_naturality_left_square
  have hn := o.comparison.hom.naturality (Prod.mkHom ((f.push A).map h) k)
  dsimp at hn
  rw [← Category.assoc, hn, Category.assoc]
  simp only [Category.assoc, ← o.tensorX.map_comp]
  congr 2
  ext
  · exact (f.adj A).counit.naturality h
  · simp

set_option backward.isDefEq.respectTransparency false in
private theorem completed_natural {o : TensorData f A} (b : CompletedTensor I o)
    (hb : b.UnitEquation) : b.Natural := by
  intro H H' K K' h k
  apply ((Y.completion_properties A I).2.1 _ _
    (f.push_complete A I _ ((X.completion_properties A I).1 _))).1
  change (Y.unit A I).app _ ≫ ((Y.completion A I).map _ ≫ _) =
    (Y.unit A I).app _ ≫ (b.projection H K ≫ _)
  erw [← reassoc_of% (Y.unit A I).naturality, hb, reassoc_of% hb H K]
  erw [← (f.push A).map_comp,
    ← (X.unit A I).naturality, (f.push A).map_comp, ← Category.assoc,
    projection_naturality]
  simp only [Category.assoc, Functor.id_map]

private theorem conjugate_homEquiv
    {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (e : L₂ ≅ L₁)
    (M : C) (N : D) (q : L₂.obj M ⟶ N) :
    a₁.homEquiv M N (e.inv.app M ≫ q) =
      a₂.homEquiv M N q ≫ (conjugateIsoEquiv a₁ a₂ e).inv.app N := by
  have hu := unit_conjugateEquiv a₂ a₁ e.inv M
  change a₂.unit.app M ≫ (conjugateIsoEquiv a₁ a₂ e).inv.app (L₂.obj M) =
    a₁.unit.app M ≫ R₁.map (e.inv.app M) at hu
  simp only [Adjunction.homEquiv_apply, Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hu]
  exact congrArg (a₂.unit.app M ≫ ·)
    ((conjugateIsoEquiv a₁ a₂ e).inv.naturality q).symm

set_option backward.isDefEq.respectTransparency false in
private theorem completed_counit (H : X.Complete A I) :
    (X.unit A I).app ((f.pull A).obj ((f.push A).obj H.obj)) ≫
      ((f.completeAdjunction A I).counit.app H).hom = (f.adj A).counit.app H.obj := by
  apply ((f.adj A).homEquiv _ _).injective
  have h := (f.completeAdjunction_existsUnique A I).exists.choose_spec
    ((f.completePush A I).obj H) H ((f.completeAdjunction A I).counit.app H)
  change ((f.completeAdjunction A I).homEquiv _ _
    ((f.completeAdjunction A I).counit.app H)).hom = _ at h
  erw [← h, ← (f.completeAdjunction A I).homEquiv_symm_id H,
    Equiv.apply_symm_apply]
  symm
  change (f.adj A).homEquiv _ _ ((f.adj A).counit.app H.obj) = 𝟙 _
  simp only [Adjunction.homEquiv_apply, Adjunction.right_triangle_components]

set_option backward.isDefEq.respectTransparency false in
private theorem completed_unit {o : TensorData f A} (b : CompletedTensor I o) :
    b.UnitEquation := by
  intro H K
  erw [CompletedTensor.projection,
    (f.completeAdjunction_existsUnique A I).exists.choose_spec, TensorData.projection,
    ← (f.adj A).homEquiv_naturality_left,
    ← (f.adj A).homEquiv_naturality_right]
  apply congrArg ((f.adj A).homEquiv _ _)
  erw [reassoc_of% (X.unit A I).naturality]
  erw [← b.pullInsert_eq, reassoc_of% b.comparison_eq]
  simp only [Category.assoc]
  apply (cancel_mono (b.insertRight H.obj ((f.pull A).obj K.obj)).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [b.insertRight_eq]
  erw [← reassoc_of% (X.unit A I).naturality]
  erw [← (X.unit A I).naturality, ← (X.unit A I).naturality]
  simp only [Functor.id_map, Functor.id_obj, Category.assoc]
  simp only [← Category.assoc, ← o.tensorX.map_comp]
  congr 2
  congr 1
  ext
  · simpa using completed_counit (f := f) H
  · simp


omit [IsNoetherianRing A] in
private theorem transpose_compatibility (f : Morphism Y X) :
    TransposeCompatibility f A := by
  intro M Z W b j
  have h := conjugate_homEquiv
    ((f.adj A).comp (X.deltaAdjunction A))
    ((Y.deltaAdjunction A).comp (f.towerAdjunction A))
    (f.constantPullIso A) M W ((f.towerPull A).map j ≫ b)
  simp only [Adjunction.homEquiv_apply, Adjunction.comp_unit_app, Functor.comp_map,
    Functor.map_comp, Category.assoc] at h
  simp only [Adjunction.homEquiv_apply, Functor.map_comp, Category.assoc,
    Morphism.directLimitIso]
  have hn := congrArg ((Y.rlim A).map) ((f.towerAdjunction A).unit.naturality j)
  simp only [Functor.comp_map, Functor.id_map, Functor.map_comp] at hn
  rw [reassoc_of% hn]
  exact h

omit [IsNoetherianRing A] in
set_option backward.isDefEq.respectTransparency false in
private theorem augmentation_unit (T : Site.{u}) (M : T.derived A) :
    (T.deltaAdjunction A).unit.app M ≫
        (T.rlim A).map ((T.quotientAugmentation A I).app M) = (T.unit A I).app M := by
  change (T.deltaAdjunction A).unit.app M ≫ (T.rlim A).map
    (((T.deltaAdjunction A).homEquiv _ _).symm ((T.unit A I).app M)) = _
  erw [← Adjunction.homEquiv_unit, Equiv.apply_symm_apply]

omit [IsNoetherianRing A] in
set_option backward.isDefEq.respectTransparency false in
private theorem quotient_projection_unit (H : X.derived A) :
    (Y.unit A I).app ((f.push A).obj H) ≫
        (Y.rlim A).map (f.towerProjection A I H) ≫
        (f.directLimitIso A).inv.app ((X.reduction A I).obj H) =
      (f.push A).map ((X.unit A I).app H) := by
  let ε := (f.adj A).counit.app H
  let j := (Y.quotientAugmentation A I).app ((f.push A).obj H)
  let q := (f.reductionPullIso A I).hom.app ((f.push A).obj H) ≫
    (X.reduction A I).map ε
  have ht := transpose_compatibility f (A := A)
    ((f.push A).obj H) ((Y.reduction A I).obj ((f.push A).obj H))
    ((X.reduction A I).obj H) q j
  have hq : (f.constantPullIso A).inv.app ((f.push A).obj H) ≫
      (f.towerPull A).map j ≫ q =
      (X.quotientAugmentation A I).app ((f.pull A).obj ((f.push A).obj H)) ≫
        (X.reduction A I).map ε := by
    dsimp only [q, j]
    rw [← Category.assoc ((f.towerPull A).map _),
      quotientAugmentation_pullback, Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [hq] at ht
  have ha : (X.deltaAdjunction A).unit.app ((f.pull A).obj ((f.push A).obj H)) ≫
      (X.rlim A).map
        ((X.quotientAugmentation A I).app ((f.pull A).obj ((f.push A).obj H)) ≫
          (X.reduction A I).map ε) = ε ≫ (X.unit A I).app H := by
    erw [← (X.quotientAugmentation A I).naturality, Functor.map_comp,
      ← reassoc_of% (X.deltaAdjunction A).unit.naturality, augmentation_unit]
    rfl
  rw [ha] at ht
  have hb : (f.adj A).homEquiv _ _ (ε ≫ (X.unit A I).app H) =
      (f.push A).map ((X.unit A I).app H) := by
    rw [(f.adj A).homEquiv_naturality_right]
    change (f.adj A).homEquiv _ _ ((f.adj A).counit.app H) ≫ _ = _
    simp only [Adjunction.homEquiv_apply, Adjunction.right_triangle_components,
      Category.id_comp]
  erw [hb] at ht
  symm
  apply ht.trans
  dsimp only [j]
  rw [Functor.map_comp]
  simp only [Category.assoc]
  erw [reassoc_of% augmentation_unit]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem completed_limit {o : TensorData f A} (b : CompletedTensor I o)
    (hb : b.Unique) : b.LimitEquation := by
  intro H K
  symm
  apply hb H K
  dsimp only [TensorData.towerProjection]
  rw [Functor.map_comp]
  simp only [Category.assoc]
  change (Y.unit A I).app _ ≫ (Y.completion A I).map (o.projection H.obj K.obj) ≫
    (Y.rlim A).map (f.towerProjection A I _) ≫ (f.directLimitIso A).inv.app _ = _
  erw [← reassoc_of% (Y.unit A I).naturality, quotient_projection_unit]

/-- Completion coherence for the integral projection mate, including its finite quotient
and counit normalizations. It holds for every specified ordinary tensor presentation `o`
of the derived tensor on the two sites (the canonical K-flat model convention of the
landed ringed-topos tensor theorems). The completed tensor comparisons, which are unique by
their unit equations, and the finite quotient tensor presentations are constructed
existentially; the only mathematical hypotheses are Noetherianness and perfectness of
the positive quotients.

Source: Stacks Project, `sites-cohomology.tex`, Tags 07A6, 0B56, 0941, 0A07;
`proetale.tex`, Tags 099M and 099N; the eleven-step agent auxiliary in the DAG
(blueprint: lem-pur-compact-support-completed-projection-coherence).

Proof plan:
1. Closed tensor adjunction and completeness of RHom show that completion of a
   tensor-factor unit is invertible (lem-sf-ringed-derived-closed-symmetric-monoidal,
   lem-sf-ringed-rhom-derived-complete). The same Hom calculation using preservation
   of completeness by direct image gives pullInsert. Unit precomposition fixes all
   tensor comparisons and transports ordinary coherence (lem-sp-completed-pullback-adjunction).
2. Transpose the completed mate. Its completed counit followed by the completion unit
   is the ordinary counit. Cancel the factor units to obtain UnitEquation. The target
   is complete, so unit precomposition is injective and gives Unique.
3. On the diagram sites (lem-weil-pbc-diagram-site-realization) use the ring sheaf
   B=(A/I^(n+1)) with actual quotient transitions. A single flat-term K-flat model
   gives the strict scalar-extension tower; exact restriction gives the recorded
   quotientPresentation (lem-pc-kflat-resolution,
   lem-weil-tower-category-levelwise-abelian,
   lem-weil-pbc-ringed-topoi-derived-tensor-pullback).
4. Derive the componentwise adjunctions with their fraction normalizations
   (lem-pc-pre-derived-adjoint-functors-general). Evaluation at the terminal tower
   index is exact and left adjoint to the diagonal, so the diagonal preserves
   K-injectives (lem-weil-pbc-right-adjoint-preserves-kinjective). On diagonal
   K-injectives the pushforward and limit identities hold literally; quotient
   augmentation has limit equal to the specified completion unit
   (prop-pur-kinjective-resolutions-exist, lem-weil-pbc-kinjective-total-derived,
   lem-weil-pbc-ringed-strict-tower-homotopy-limit).
5. Compare the two composite derived adjunctions through the identical ordinary
   composite direct image. Their normalized right-adjoint comparison is f.directLimitIso.
   Transposing an arbitrary whole tower arrow after a constant augmentation gives
   TransposeCompatibility, including the counits
   (lem-weil-ringed-tower-pushforward-limit-comparison,
   lem-weil-pbc-ringed-topoi-derived-pushforward-composition).
6. Coefficient exchange on the B-ringed diagram, after exact restriction, is
   f.towerProjection: both transposes are counit tensor identity. Evaluation is
   the corresponding finite coefficient mate, by the normalized fraction adjunction.
   No assertion that varying-coefficient evaluation preserves K-injectives is needed.
7. Represent each quotient by the assumed bounded finite-projective A-complex.
   Constant sheafification preserves its quasi-isomorphism and finite-free splittings.
   The specified finite-total projection inverse proves each finite coefficient
   exchange invertible; its cone is zero at every index, so the whole strict exchange
   is invertible (def-weil-pbc-projection-formula-arrows,
   lemma-weil-pbc-projection-formula-totalization).
8. Scalar-extension tensor balancing identifies the B-diagram projection after the
   coefficient exchange with FiniteTensor.projection on evaluation, giving FiniteEquation.
9. Apply lem-weil-pbc-ringed-exchange-tensor-coherence on that diagram square.
   It identifies the whole diagram arrow with reduction of the ordinary projection
   followed by coefficient exchange: this is TensorData.towerProjection before any limit.
10. Tensor-unit normalization and naturality for the actual quotient augmentation
    give exchange times augmentation = pushed augmentation. Total limit and the
    normalized direct-image comparison give rho times eta = P(eta).
11. Apply total derived limit to step 9. Step 10 and naturality of eta give precisely
    UnitEquation for the resulting arrow. Unique identifies it with the completed
    mate, proving CompletedTensor.LimitEquation. All constructions and normalized comparisons are
    natural, proving Natural. No faithfulness of reductions is used. -/
theorem completedProjectionCoherence
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (_hperfect : AdicSites.PerfectQuotients A I) (f : Morphism Y X) (o : TensorData f A) :
    ∃ (b : CompletedTensor I o) (s : ∀ n : ℕ, FiniteTensor (I := I) o n),
      (∀ H : X.derived A, IsIso (f.towerProjection A I H)) ∧
      (∀ (n : ℕ) (H : X.derived A), IsIso (f.finiteProjection A I n H)) ∧
      b.UnitEquation ∧ b.Unique ∧ b.LimitEquation ∧ o.FiniteEquation s ∧
      TransposeCompatibility f A ∧ b.Natural := by
  obtain ⟨b⟩ := completed_tensor_exists (I := I) o
  obtain ⟨s, hs⟩ := finiteQuotientTensorProjection (I := I) f o
  obtain ⟨ht, hf⟩ := perfectQuotientProjection f _hperfect
  have hu := completed_unit b
  have huniq := completed_unique b hu
  exact ⟨b, s, ht, hf, hu, huniq, completed_limit b huniq, hs,
    transpose_compatibility f, completed_natural b hu⟩

end CategoryTheory.AdicSites.ProjectionCoherence
