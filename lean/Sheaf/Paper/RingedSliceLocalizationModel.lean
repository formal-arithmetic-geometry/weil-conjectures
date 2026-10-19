/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q7
-/
module

public import Sheaf.Paper.RingedDerivedSliceData
import all Sheaf.CategoryTheory.RingedKoszulFactorColimit

/-!
# Derived slice proof obligations

Source: Stacks Project, algebraization.tex, Tag 099J; Modules on Sites, Tag 04J0;
Cohomology on Sites, Tag 07A6
(blueprint: lem-weil-pbc-ringed-slice-localization-model).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 256

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules

variable {D C : Type u} [SmallCategory D] [SmallCategory C]
  {K : GrothendieckTopology D} {J : GrothendieckTopology C}
  (u : D ⥤ C) [u.IsContinuous K J]
  {R : Sheaf K CommRingCat.{u}} {S : Sheaf J CommRingCat.{u}}
  (a : R ⟶ (u.sheafPushforwardContinuous CommRingCat.{u} K J).obj S)



private theorem slicePost_final (V : D) : (Over.post (X := V) u).Final := by
  have hp : PreservesLimit (Functor.empty.{0} (Over V)) (Over.post (X := V) u) := by
    apply preservesLimit_of_preserves_limit_cone (Over.mkIdTerminal (X := V))
    apply (isLimitMapConeEmptyConeEquiv (Over.post (X := V) u)
      (Over.mk (𝟙 V))).symm.toFun
    exact (Over.mkIdTerminal (X := u.obj V)).ofIso
      (Over.isoMk (Iso.refl _) (by
        change 𝟙 _ ≫ u.map (𝟙 V) = 𝟙 _
        rw [u.map_id, Category.id_comp]))
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pullback_scalar
    (s : (R.obj ⋙ CategoryTheory.forget CommRingCat).sections)
    (t : (S.obj ⋙ CategoryTheory.forget CommRingCat).sections)
    (h : ∀ X : Dᵒᵖ, a.hom.app X (s.val X) = t.val (u.op.obj X)) :
    (ringedSliceModulePullback u a).map (ringedKoszulScalar R s) ≫
        pullbackObjUnitToUnit (ringedSiteModuleMap u a) =
      pullbackObjUnitToUnit (ringedSiteModuleMap u a) ≫ ringedKoszulScalar S t := by
  apply ((ringedSliceModuleAdjunction u a).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  dsimp only [ringedSliceModuleAdjunction, ringedSliceModulePullback,
    ringedSliceModulePushforward]
  rw [pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit]
  change ringedKoszulScalar R s ≫ unitToPushforwardObjUnit (ringedSiteModuleMap u a) =
    unitToPushforwardObjUnit (ringedSiteModuleMap u a) ≫
      (ringedSliceModulePushforward u a).map (ringedKoszulScalar S t)
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change a.hom.app X ((show R.obj.obj X from x) * (show R.obj.obj X from s.val X)) =
    (show S.obj.obj (u.op.obj X) from a.hom.app X x) *
      (show S.obj.obj (u.op.obj X) from t.val (u.op.obj X))
  rw [map_mul, h]



set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
-- Elaborate the dependent colimit cocone comparisons without unfolding their constructions.
set_option backward.isDefEq.respectTransparency.types false in
private theorem pullback_localization [u.Final]
    (s : (R.obj ⋙ CategoryTheory.forget CommRingCat).sections)
    (t : (S.obj ⋙ CategoryTheory.forget CommRingCat).sections)
    (h : ∀ X : Dᵒᵖ, a.hom.app X (s.val X) = t.val (u.op.obj X)) :
    ∃ loc : (ringedSliceModulePullback u a).obj (ringedSectionLocalization R s) ≅
        ringedSectionLocalization S t,
      (ringedSliceModulePullback u a).map (ringedSectionLocalizationUnit R s) ≫ loc.hom =
        pullbackObjUnitToUnit (ringedSiteModuleMap u a) ≫ ringedSectionLocalizationUnit S t := by
  let L := ringedSliceModulePullback u a
  have : L.IsLeftAdjoint := (ringedSliceModuleAdjunction u a).isLeftAdjoint
  let c := CategoryTheory.localizationSheafCocone R s
  let d := CategoryTheory.localizationSheafCocone S t
  let eunit := asIso (pullbackObjUnitToUnit (ringedSiteModuleMap u a))
  let F := Functor.ofSequence (X := fun _ : ℕ ↦
    unit ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R))
      (fun _ ↦ ringedKoszulScalar R s)
  let G := Functor.ofSequence (X := fun _ : ℕ ↦
    unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
      (fun _ ↦ ringedKoszulScalar S t)
  let τ : F ⋙ L ⟶ G := NatTrans.ofSequence (fun _ ↦ eunit.hom) (by
    intro n
    simp only [F, G, Functor.comp_map, Functor.ofSequence_map_homOfLE_succ]
    change (ringedSliceModulePullback u a).map (ringedKoszulScalar R s) ≫
      pullbackObjUnitToUnit (ringedSiteModuleMap u a) =
      pullbackObjUnitToUnit (ringedSiteModuleMap u a) ≫ ringedKoszulScalar S t
    exact pullback_scalar u a s t h)
  let e : F ⋙ L ≅ G :=
    NatIso.ofComponents (fun _ ↦ eunit) (fun f ↦ τ.naturality f)
  let hc := isColimitOfPreserves L (CategoryTheory.localizationSheafCoconeIsColimit R s)
  let hd := (IsColimit.precomposeHomEquiv e d).symm
    (CategoryTheory.localizationSheafCoconeIsColimit S t)
  let loc := hc.coconePointUniqueUpToIso hd
  refine ⟨loc, ?_⟩
  have hleg : L.map (CategoryTheory.localizationSheafMap R s 1) ≫ loc.hom =
      eunit.hom ≫ CategoryTheory.localizationSheafMap S t 1 :=
    hc.comp_coconePointUniqueUpToIso_hom hd 0
  have hsrc : ringedKoszulScalar R s ≫ CategoryTheory.localizationSheafMap R s 1 =
      ringedSectionLocalizationUnit R s := by
    rw [CategoryTheory.localizationSheafMap_step, CategoryTheory.localizationSheafMap_zero]
  have htgt : ringedKoszulScalar S t ≫ CategoryTheory.localizationSheafMap S t 1 =
      ringedSectionLocalizationUnit S t := by
    rw [CategoryTheory.localizationSheafMap_step, CategoryTheory.localizationSheafMap_zero]
  rw [← hsrc, L.map_comp, Category.assoc, hleg, ← Category.assoc]
  rw [show L.map (ringedKoszulScalar R s) ≫ eunit.hom =
    eunit.hom ≫ ringedKoszulScalar S t from pullback_scalar u a s t h]
  rw [Category.assoc, htgt]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
-- Elaborate the single-complex comparison with the explicit scalar-image casts.
set_option backward.isDefEq.respectTransparency.types false in
/-- A flat single-complex model for pullback of a section localization, normalized
on the localization unit.
Source: Stacks Tag 099J, proof of lemma-pushforward-derived-complete;
Tags 04J0 and 0G7E
(blueprint: lem-weil-pbc-ringed-slice-localization-model).
Proof:
1. Work on the two slice sites, where t and its structural image t' are global
sections. For a ring A and an element z, the colimit of A --z--> A --z--> ... is
A[1/z]: send the n-th copy by x to x/z^n. Surjectivity follows from the fraction
presentation. If two fractions are equal, multiplication by a further power of z
makes their numerators equal, so they agree at a later stage. This works with zero
divisors, z = 0, nilpotents and the zero ring. The maps commute with restriction.
2. Sheafifying this sectionwise colimit gives the actual ringedSectionLocalization.
The module-sheaf colimit theorem identifies it with the colimit of copies of the
unit module and multiplication by the section. The map from stage zero is exactly
ringedSectionLocalizationUnit, since both send 1 to the fraction 1.
3. Module pullback preserves this colimit as a left adjoint. Its canonical unit
isomorphism sends the unit module to the target unit and intertwines multiplication
by t with multiplication by t'. The colimit universal property therefore gives an
ordinary module isomorphism from the pullback localization to the target
localization. It sends the stage-zero map to pullbackObjUnitToUnit followed by the
target localization unit. Applying the degree-zero single-complex comparison gives
loc and precisely the final generator equation in the statement.
The assertion here is the ordinary complex calculation only; the derived counit
is handled separately by the parent theorem using the flat K-flat model. -/
theorem ringedSliceLocalizationModel (V : D)
    [(Over.post (X := V) u).IsContinuous (K.over V) (J.over (u.obj V))]
    (t : R.obj.obj (op V)) :
    ∃ loc :
        ((ringedSliceModulePullback (Over.post (X := V) u)
          (localizedRingedSiteMap u a V)).mapHomologicalComplex (.up ℤ)).obj
          ((CochainComplex.singleFunctor _ 0).obj
            (ringedSectionLocalization (R.over V) (ringedSliceSection R V t))) ≅
        (CochainComplex.singleFunctor _ 0).obj
          (ringedSectionLocalization (S.over (u.obj V))
            (ringedSliceSection S (u.obj V) (a.hom.app (op V) t))),
      ((ringedSliceModulePullback (Over.post (X := V) u)
          (localizedRingedSiteMap u a V)).mapHomologicalComplex (.up ℤ)).map
        ((CochainComplex.singleFunctor _ 0).map
          (ringedSectionLocalizationUnit (R.over V) (ringedSliceSection R V t))) ≫
        loc.hom = ringedSliceLocalizationGenerator (Over.post (X := V) u)
          (localizedRingedSiteMap u a V)
          (ringedSliceSection S (u.obj V) (a.hom.app (op V) t)) := by
  have : (Over.post (X := V) u).Final := slicePost_final u V
  obtain ⟨e, he⟩ := pullback_localization (Over.post (X := V) u)
    (localizedRingedSiteMap u a V) (ringedSliceSection R V t)
      (ringedSliceSection S (u.obj V) (a.hom.app (op V) t)) (by
        intro W
        exact ConcreteCategory.congr_hom (a.hom.naturality W.unop.hom.op) t)
  let F := ringedSliceModulePullback (Over.post (X := V) u) (localizedRingedSiteMap u a V)
  let c := HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0
  refine ⟨c.app _ ≪≫ (CochainComplex.singleFunctor _ 0).mapIso e, ?_⟩
  change (F.mapHomologicalComplex (.up ℤ)).map _ ≫
    (c.hom.app _ ≫ (CochainComplex.singleFunctor _ 0).map e.hom) = _
  have hn := c.hom.naturality
    (ringedSectionLocalizationUnit (R.over V) (ringedSliceSection R V t))
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc]
  calc
    _ = (c.hom.app _ ≫ (CochainComplex.singleFunctor _ 0).map
        (F.map (ringedSectionLocalizationUnit (R.over V) (ringedSliceSection R V t)))) ≫
        (CochainComplex.singleFunctor _ 0).map e.hom :=
      congrArg (fun z ↦ z ≫ (CochainComplex.singleFunctor _ 0).map e.hom) hn
    _ = _ := by
      rw [Category.assoc, ← Functor.map_comp, he]
      rfl

end SheafOfModules
