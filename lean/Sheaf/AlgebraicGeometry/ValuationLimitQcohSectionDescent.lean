/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
public import Sheaf.AlgebraicGeometry.AffinePushforwardColimit
import WeilConjectures.CategoryTheory.SheafAlgebrasDirectedColimit
import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionRestrictionTensor
import WeilConjectures.Topology.AbelianSectionsFilteredColimit
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Limits.ConcreteCategory.WithAlgebraicStructures

/-! # Quasi-coherent sections descend along affine inverse limits

Source: Stacks Project, Limits, Lemma 01Z0 (lemma-descend-section)
(blueprint: lem-sc-valuation-limit-qcoh-section-descent).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
open MonoidalCategory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry

private noncomputable def sections (S : Scheme.{u}) : S.Modules ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf S.ringCatSheaf ⋙
    sheafToPresheaf (Opens.grothendieckTopology S) AddCommGrpCat.{u} ⋙
      (evaluation S.Opensᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)

private noncomputable def structureAlgebra (S : Scheme.{u}) :
    (Over S)ᵒᵖ ⥤ S.CommAlgebraSheaf := by
  refine {
    obj := fun Y ↦ Under.mk (⟨Y.unop.hom.c⟩ : S.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} Y.unop.hom.base).obj Y.unop.left.sheaf)
    map := fun {Y Y'} h ↦ Under.homMk ⟨{
      app := fun V ↦ h.unop.left.appLE (Y.unop.hom ⁻¹ᵁ V.unop)
        (Y'.unop.hom ⁻¹ᵁ V.unop)
        (by rw [← Over.w h.unop, Scheme.Hom.comp_preimage])
      naturality := ?_ }⟩ ?_
    map_id := ?_
    map_comp := ?_ }
  · intro U V i
    change Y.unop.left.presheaf.map
        ((TopologicalSpace.Opens.map Y.unop.hom.base).map i.unop).op ≫ _ = _ ≫
      Y'.unop.left.presheaf.map ((TopologicalSpace.Opens.map Y'.unop.hom.base).map i.unop).op
    simp only [Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]
  · apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    change Y.unop.hom.app V.unop ≫ h.unop.left.appLE _ _ _ =
      Y'.unop.hom.app V.unop
    rw [← Scheme.Hom.comp_appLE]
    exact (Scheme.Hom.congr_app (Over.w h.unop).symm V.unop).symm
  · intro Y
    apply StructuredArrow.hom_ext
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    change Scheme.Hom.appLE (𝟙 Y.unop.left) _ _ _ = 𝟙 _
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_base, Scheme.Hom.id_app,
      homOfLE_refl, op_id, Category.id_comp]
    exact CategoryTheory.Functor.map_id _ _
  · intro Y Y' Y'' h k
    apply StructuredArrow.hom_ext
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    change (k.unop.left ≫ h.unop.left).appLE _ _ _ =
      h.unop.left.appLE _ _ _ ≫ k.unop.left.appLE _ _ _
    rw [Scheme.Hom.appLE_comp_appLE]

private theorem structureAlgebra_obj (S : Scheme.{u}) (Y : (Over S)ᵒᵖ) :
    (structureAlgebra S).obj Y = Under.mk (⟨Y.unop.hom.c⟩ : S.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} Y.unop.hom.base).obj
        Y.unop.left.sheaf) := rfl

private theorem structureAlgebra_map (S : Scheme.{u}) {Y Y' : (Over S)ᵒᵖ}
    (h : Y ⟶ Y') (U : S.Opens) :
    ((structureAlgebra S).map h).right.hom.app (op U) =
      h.unop.left.appLE (Y.unop.hom ⁻¹ᵁ U) (Y'.unop.hom ⁻¹ᵁ U)
        (by rw [← Over.w h.unop, Scheme.Hom.comp_preimage]) := rfl

private noncomputable def pushforwardTopIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (G : X.Modules) :
    (sections Y).obj ((pushforward f).obj G) ≅
      AddCommGrpCat.of (Γ(G, ⊤)) :=
  G.presheaf.mapIso (eqToIso f.preimage_top.symm).op

private theorem pushforwardTopIso_transition
    {X Y S : Scheme.{u}} (f : X ⟶ S) (h : Y ⟶ X) (k : Y ⟶ S)
    (w : h ≫ f = k) (G : X.Modules) (H : Y.Modules)
    (r : G ⟶ (pushforward h).obj H) :
    (pushforwardTopIso f G).inv ≫
      (sections S).map
        ((pushforward f).map r ≫ (pushforwardComp h f).hom.app H ≫
          (pushforwardCongr w).hom.app H) ≫ (pushforwardTopIso k H).hom =
      r.app ⊤ ≫ H.presheaf.map (eqToHom (by simp)).op := by
  subst k
  change G.presheaf.map (eqToHom f.preimage_top).op ≫
    ((pushforward f).map r ≫ (pushforwardComp h f).hom.app H ≫
      (pushforwardCongr rfl).hom.app H).app ⊤ ≫
    H.presheaf.map (eqToHom (h ≫ f).preimage_top.symm).op = _
  simp only [Hom.comp_app, pushforward_map_app, pushforwardComp_hom_app_app,
    pushforwardCongr_hom_app_app, eqToHom_refl, op_id]
  erw [H.presheaf.map_id, Category.comp_id]
  erw [G.presheaf.map_id, Category.id_comp]

private theorem pushforward_transition_smul
    {X Y S : Scheme.{u}} (f : X ⟶ S) (h : Y ⟶ X) (k : Y ⟶ S)
    (w : h ≫ f = k) (F : S.Modules) (G : X.Modules) (H : Y.Modules)
    (η : F ⟶ (pushforward f).obj G) (η' : F ⟶ (pushforward k).obj H)
    (r : G ⟶ (pushforward h).obj H)
    (hr : η ≫ (pushforward f).map r ≫ (pushforwardComp h f).hom.app H ≫
      (pushforwardCongr w).hom.app H = η')
    (U : S.Opens) (x : Γ(F, U)) (a : Γ(X, f ⁻¹ᵁ U)) :
    ((pushforward f).map r ≫ (pushforwardComp h f).hom.app H ≫
      (pushforwardCongr w).hom.app H).app U (a • (@id Γ(G, f ⁻¹ᵁ U) (η.app U x))) =
      h.appLE (f ⁻¹ᵁ U) (k ⁻¹ᵁ U)
        (by rw [← w, Scheme.Hom.comp_preimage]) a • (@id Γ(H, k ⁻¹ᵁ U) (η'.app U x)) := by
  subst k
  have he := congrArg (fun z ↦ z.app U) hr
  simp only [Hom.comp_app, pushforward_map_app, pushforwardComp_hom_app_app,
    pushforwardCongr_hom_app_app, eqToHom_refl, op_id] at he ⊢
  erw [H.presheaf.map_id] at he ⊢
  erw [Category.comp_id] at he ⊢
  have he := ConcreteCategory.congr_hom he x
  change r.app (f ⁻¹ᵁ U) (η.app U x) = η'.app U x at he
  change r.app (f ⁻¹ᵁ U) (a • (@id Γ(G, f ⁻¹ᵁ U) (η.app U x))) =
    h.appLE (f ⁻¹ᵁ U) ((h ≫ f) ⁻¹ᵁ U) _ a •
      (@id Γ(H, (h ≫ f) ⁻¹ᵁ U) (η'.app U x))
  have ht := (r.val.app (op (f ⁻¹ᵁ U))).hom.map_smul a (η.app U x)
  change r.app (f ⁻¹ᵁ U) (a • (@id Γ(G, f ⁻¹ᵁ U) (η.app U x))) =
    h.app (f ⁻¹ᵁ U) a • (@id Γ(H, h ⁻¹ᵁ (f ⁻¹ᵁ U))
      (r.app (f ⁻¹ᵁ U) (η.app U x))) at ht
  dsimp only [Scheme.Hom.appLE]
  erw [Y.presheaf.map_id, Category.comp_id]
  rw [← he]
  exact ht

private theorem isIso_of_colimit_comparison
    {J : Type u} [Category J] (M K : J ⥤ AddCommGrpCat.{u})
    (c : Cocone K) (hc : IsColimit c) (d : M ≅ K)
    {Z : AddCommGrpCat.{u}} (b : c.pt ≅ Z) (q : colimit M ⟶ Z)
    (h : ∀ j, d.hom.app j ≫ c.ι.app j ≫ b.hom = colimit.ι M j ≫ q) : IsIso q := by
  let c' := (Cocone.precompose d.hom).obj c
  have hc' : IsColimit c' := (IsColimit.precomposeHomEquiv d c).symm hc
  let z : Cocone M :=
    { pt := Z
      ι := { app := fun j ↦ colimit.ι M j ≫ q
             naturality := by intro j k f; simp } }
  have hz : IsColimit z := hc'.ofIsoColimit (Cocone.ext b (by intro j; exact h j))
  have he : q = ((colimit.isColimit M).coconePointUniqueUpToIso hz).hom := by
    apply colimit.hom_ext
    intro j
    exact ((colimit.isColimit M).comp_coconePointUniqueUpToIso_hom hz j).symm
  rw [he]
  infer_instance


set_option maxHeartbeats 800000 in
-- Dependent section-map conversions in hR and hL exceed the default heartbeat budget.
/-- For a qcqs inverse system of schemes with affine transitions, global sections of a
quasi-coherent module on a fixed stage are recovered from the directed system of sections
on the later pullbacks.  The diagram `M` records these section groups (the displayed
equivalences and `hM` specify its objects and maps), and `hq` pins `q` to the canonical
map from their colimit to the sections on the limit. The sheaf morphisms `r` and `t`
are uniquely pinned to pullback by their adjunction-unit equations `hr` and `ht`.

Source: Stacks Project, Limits, Lemma 01Z0.
(blueprint: lem-sc-valuation-limit-qcoh-section-descent).

Proof:
1. Restrict to the nonempty directed tail above `i₀` and construct the diagram of
   pushforward structure algebras. Obtain its algebra and underlying module colimit
   from lem-weil-pbc-sheaf-algebras-directed-colimit.
2. Apply affine_pushforward_colimit (lem-sc-valuation-limit-affine-pushforward-colimit):
   pushforwards of the pullbacks identify with `F` tensored with the pushforward algebras;
   the limit algebra and its tensor module are the directed colimits of these diagrams.
3. On the qcqs base, global sections commute with this directed module colimit, by
   lem-sc-topological-abelian-sections-filtered-colimit at the whole open, since
   forgetting module sheaves to abelian sheaves preserves colimits.
4. Sections of each pushforward are sections on its source. Substitute these identifications
   into step 3 to obtain the canonical bijection. The zero criterion for a directed colimit
   (lem-weil-pbc-filtered-colimit-modules-elementwise) gives eventual vanishing.
-/
theorem valuation_limit_qcoh_section_descent
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    (s : Cone D) (hs : IsLimit s)
    [∀ i : I, CompactSpace (D.obj (op i))]
    [∀ i : I, QuasiSeparatedSpace (D.obj (op i))]
    (haff : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f.op))
    (i₀ : I) (F : (D.obj (op i₀)).Modules) [F.IsQuasicoherent]
    (g : ∀ j : {j : I // i₀ ≤ j}, D.obj (op j.val) ⟶ D.obj (op i₀))
    (hg : ∀ j, g j = D.map (homOfLE j.property).op)
    (r : ∀ {j k : {j : I // i₀ ≤ j}} (f : j ⟶ k),
      (tensorPullback (g j)).obj F ⟶
        (pushforward (D.map (homOfLE (x := j.val) (y := k.val) (leOfHom f)).op)).obj
          ((tensorPullback (g k)).obj F))
    (hr : ∀ {j k : {j : I // i₀ ≤ j}} (f : j ⟶ k),
      (Classical.choose (exists_tensorPullbackAdjunction (g j))).unit.app F ≫
        (pushforward (g j)).map (r f) ≫
        (pushforwardComp
          (D.map (homOfLE (x := j.val) (y := k.val) (leOfHom f)).op) (g j)).hom.app
          ((tensorPullback (g k)).obj F) ≫
        (pushforwardCongr (f := D.map (homOfLE (x := j.val) (y := k.val)
          (leOfHom f)).op ≫ g j) (g := g k)
          (by rw [hg j, hg k, ← D.map_comp]; rfl)).hom.app
          ((tensorPullback (g k)).obj F) =
      (Classical.choose (exists_tensorPullbackAdjunction (g k))).unit.app F)
    (t : ∀ j : {j : I // i₀ ≤ j}, (tensorPullback (g j)).obj F ⟶
      (pushforward (s.π.app (op j.val))).obj
        ((tensorPullback (s.π.app (op i₀))).obj F))
    (ht : ∀ j,
      (Classical.choose (exists_tensorPullbackAdjunction (g j))).unit.app F ≫
        (pushforward (g j)).map (t j) ≫
        (pushforwardComp (s.π.app (op j.val)) (g j)).hom.app
          ((tensorPullback (s.π.app (op i₀))).obj F) ≫
        (pushforwardCongr (f := s.π.app (op j.val) ≫ g j)
          (g := s.π.app (op i₀))
          (by rw [hg j]; exact s.w (homOfLE j.property).op)).hom.app
          ((tensorPullback (s.π.app (op i₀))).obj F) =
      (Classical.choose (exists_tensorPullbackAdjunction (s.π.app (op i₀)))).unit.app F)
    (M : {j : I // i₀ ≤ j} ⥤ AddCommGrpCat.{u})
    (e : ∀ j : {j : I // i₀ ≤ j}, M.obj j ≅
      AddCommGrpCat.of (Γ((tensorPullback (g j)).obj F, ⊤)))
    (hM : ∀ {j k : {j : I // i₀ ≤ j}} (f : j ⟶ k) (x : M.obj j),
      (e k).hom (M.map f x) =
        ((tensorPullback (g k)).obj F).presheaf.map (eqToHom (by simp)).op
          ((r f).app ⊤ ((e j).hom x)))
    (q : colimit M ⟶ AddCommGrpCat.of
      (Γ((tensorPullback (s.π.app (op i₀))).obj F, ⊤)))
    (hq : ∀ (j : {j : I // i₀ ≤ j}) (x : M.obj j), q (colimit.ι M j x) =
      ((tensorPullback (s.π.app (op i₀))).obj F).presheaf.map (eqToHom (by simp)).op
        ((t j).app ⊤ ((e j).hom x))) :
    IsIso q ∧
      ∀ (j : {j : I // i₀ ≤ j}) (x : M.obj j), q (colimit.ι M j x) = 0 →
        ∃ k : {j : I // i₀ ≤ j}, ∃ (f : j ⟶ k), M.map f x = 0 := by
  classical
  let J := {j : I // i₀ ≤ j}
  let : Nonempty J := ⟨⟨i₀, le_rfl⟩⟩
  let : IsDirected J (· ≤ ·) := ⟨fun j k ↦ by
    obtain ⟨l, hjl, hkl⟩ := exists_ge_ge j.val k.val
    exact ⟨⟨l, j.property.trans hjl⟩, hjl, hkl⟩⟩
  let S := D.obj (op i₀)
  let T : Jᵒᵖ ⥤ Over S :=
    { obj := fun j ↦ Over.mk (g j.unop)
      map := fun {j k} f ↦ Over.homMk
        (D.map (homOfLE (x := k.unop.val) (y := j.unop.val) (leOfHom f.unop)).op)
        (by change _ ≫ g k.unop = g j.unop
            rw [hg j.unop, hg k.unop, ← D.map_comp]; rfl)
      map_id := by intro j; ext; exact D.map_id _
      map_comp := by intro j k l f h; ext; exact D.map_comp _ _ }
  let A := T.rightOp ⋙ structureAlgebra S
  have hA (j : J) : A.obj j = Under.mk (⟨(g j).c⟩ : S.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} (g j).base).obj
        (D.obj (op j.val)).sheaf) := structureAlgebra_obj S _
  have hAm {j k : J} (f : j ⟶ k) (U : S.Opens) :
      (A.map f).right.hom.app (op U) =
        (D.map (homOfLE (x := j.val) (y := k.val) (leOfHom f)).op).appLE
          ((g j) ⁻¹ᵁ U) ((g k) ⁻¹ᵁ U)
          (by rw [hg j, hg k, ← Scheme.Hom.comp_preimage, ← D.map_comp]; rfl) :=
    structureAlgebra_map S _ U
  let P := A ⋙ Under.forget S.sheaf ⋙
    sheafToPresheaf (Opens.grothendieckTopology S) CommRingCat
  let p := colimit.cocone P
  have hp (U : S.Opens) : Nonempty (IsColimit
      (((evaluation S.Opensᵒᵖ CommRingCat).obj (op U)).mapCocone p)) :=
    ⟨isColimitOfPreserves _ (colimit.isColimit P)⟩
  obtain ⟨σP, σ, ι, _, _, _, hc, hb⟩ :=
    sheafAlgebras_directed_colimit S S.sheaf J A p hp
  let c : Cocone A := Cocone.mk (Under.mk σ) ι
  let V := commAlgebraSheafModuleFunctor S.sheaf
  let B : J ⥤ S.Modules := A ⋙ V
  let b : Cocone B := V.mapCocone c
  obtain ⟨hqc, hqci, hπ, α, hα, _, E, Elim, hE, hElim, hEm, hEι, _, hcol⟩ :=
    affine_pushforward_colimit I i₀ D s hs haff g hg F A hA
      (by intro j k f U; simpa only [eqToHom_refl, Category.id_comp,
        Category.comp_id] using hAm f U)
      c hc.some B (fun _ ↦ rfl) (by intros; rfl) b rfl (by intros; rfl)
  let R {j k : J} (f : j ⟶ k) :
      (pushforward (g j)).obj ((tensorPullback (g j)).obj F) ⟶
        (pushforward (g k)).obj ((tensorPullback (g k)).obj F) :=
    (pushforward (g j)).map (r f) ≫
      (pushforwardComp (D.map (homOfLE (x := j.val) (y := k.val) (leOfHom f)).op)
        (g j)).hom.app _ ≫
      (pushforwardCongr (by rw [hg j, hg k, ← D.map_comp]; rfl)).hom.app _
  let L (j : J) : (pushforward (g j)).obj ((tensorPullback (g j)).obj F) ⟶
      (pushforward (s.π.app (op i₀))).obj
        ((tensorPullback (s.π.app (op i₀))).obj F) :=
    (pushforward (g j)).map (t j) ≫
      (pushforwardComp (s.π.app (op j.val)) (g j)).hom.app _ ≫
      (pushforwardCongr (by rw [hg j]; exact s.w (homOfLE j.property).op)).hom.app _
  have hR {j k : J} (f : j ⟶ k) :
      F ◁ B.map f ≫ (E k).hom = (E j).hom ≫ R f := by
    apply tensorResolution_tensor_hom_ext
    intro U x a
    have hb := pushforward_transition_smul (g j)
      (D.map (homOfLE (x := j.val) (y := k.val) (leOfHom f)).op) (g k)
      (by rw [hg j, hg k, ← D.map_comp]; rfl) F _ _
      _ _ (r f) (hr f) U x a
    simp only [Hom.comp_app, AddCommGrpCat.comp_apply, whiskerLeft_app_tmulSection]
    erw [hE j U x a, hE k U x ((A.map f).right.hom.app (op U) a)]
    simp only [eqToHom_refl, id_eq]
    erw [CommRingCat.id_apply, CommRingCat.id_apply]
    rw [hAm f U]
    exact hb.symm
  have hL (j : J) : F ◁ b.ι.app j ≫ Elim.hom = (E j).hom ≫ L j := by
    apply tensorResolution_tensor_hom_ext
    intro U x a
    have hb := pushforward_transition_smul (g j) (s.π.app (op j.val))
      (s.π.app (op i₀)) (by rw [hg j]; exact s.w (homOfLE j.property).op)
      F _ _ _ _ (t j) (ht j) U x a
    simp only [Hom.comp_app, AddCommGrpCat.comp_apply, whiskerLeft_app_tmulSection]
    erw [hElim U x ((c.ι.app j).right.hom.app (op U) a), hE j U x a]
    change (@id Γ(s.pt, (s.π.app (op i₀)) ⁻¹ᵁ U)
      ((c.ι.app j ≫ α.hom).right.hom.app (op U) a)) •
      (@id Γ((tensorPullback (s.π.app (op i₀))).obj F, (s.π.app (op i₀)) ⁻¹ᵁ U)
        (((Classical.choose (exists_tensorPullbackAdjunction
          (s.π.app (op i₀)))).unit.app F).app U x)) = _
    rw [hα j U]
    simp only [eqToHom_refl, Category.id_comp, id_eq]
    erw [CommRingCat.id_apply]
    exact hb.symm
  let C := (tensorLeft F).mapCocone b
  let K := B ⋙ tensorLeft F
  let H := sections S
  have : PreservesColimitsOfShape J H := by
    let W := SheafOfModules.toSheaf S.ringCatSheaf
    let L := sheafToPresheaf (Opens.grothendieckTopology S) AddCommGrpCat.{u} ⋙
      (evaluation S.Opensᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)
    have : PreservesColimitsOfShape J L :=
      TopCat.abelianSections_preservesDirectedColimits S
        (by
          intro V hV x hx
          obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
            S.isBasis_affineOpens.exists_subset_of_mem_open hx hV
          exact ⟨U, U.isOpen, hU.isCompact, hxU, hUV⟩)
        (fun V W hV hW hcV hcW ↦ hcV.inter_of_isOpen hcW hV hW) J ⊤
        isCompact_univ
    exact inferInstanceAs (PreservesColimitsOfShape J (W ⋙ L))
  have hHC := isColimitOfPreserves H hcol.some
  let a (j : J) := H.mapIso (E j) ≪≫
    pushforwardTopIso (g j) ((tensorPullback (g j)).obj F)
  let alim := H.mapIso Elim ≪≫
    pushforwardTopIso (s.π.app (op i₀)) ((tensorPullback (s.π.app (op i₀))).obj F)
  have hm {j k : J} (f : j ⟶ k) :
      M.map f ≫ (e k).hom ≫ (a k).inv = (e j).hom ≫ (a j).inv ≫ H.map (K.map f) := by
    have htop := pushforwardTopIso_transition (g j)
      (D.map (homOfLE (x := j.val) (y := k.val) (leOfHom f)).op) (g k)
      (by rw [hg j, hg k, ← D.map_comp]; rfl) _ _ (r f)
    have hh : H.map (K.map f) ≫ (a k).hom = (a j).hom ≫
        ((r f).app ⊤ ≫ ((tensorPullback (g k)).obj F).presheaf.map
          (eqToHom (by simp)).op) := by
      dsimp only [a, Iso.trans_hom, Functor.mapIso_hom]
      have hr' := congrArg (fun z ↦ H.map z) (hR f)
      simp only [Functor.map_comp] at hr'
      change H.map (F ◁ B.map f) ≫
        (H.map (E k).hom ≫ (pushforwardTopIso (g k) _).hom) = _
      rw [← Category.assoc, hr', Category.assoc]
      rw [← htop]
      simp only [R, Category.assoc, Iso.hom_inv_id_assoc]
      rfl
    apply (cancel_mono (a k).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← Category.assoc, hh]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    ext x
    exact hM f x
  let d : M ≅ K ⋙ H := NatIso.ofComponents (fun j ↦ e j ≪≫ (a j).symm)
    (by intro j k f; exact hm f)
  have hqiso : IsIso q := by
    apply isIso_of_colimit_comparison M (K ⋙ H) (H.mapCocone C) hHC d alim q
    intro j
    have htop := pushforwardTopIso_transition (g j) (s.π.app (op j.val))
      (s.π.app (op i₀)) (by rw [hg j]; exact s.w (homOfLE j.property).op)
      _ _ (t j)
    have hh : H.map (C.ι.app j) ≫ alim.hom = (a j).hom ≫
        ((t j).app ⊤ ≫ ((tensorPullback (s.π.app (op i₀))).obj F).presheaf.map
          (eqToHom (by simp)).op) := by
      dsimp only [alim, a, Iso.trans_hom, Functor.mapIso_hom]
      have hl' := congrArg (fun z ↦ H.map z) (hL j)
      simp only [Functor.map_comp] at hl'
      change H.map (F ◁ b.ι.app j) ≫
        (H.map Elim.hom ≫ (pushforwardTopIso (s.π.app (op i₀)) _).hom) = _
      rw [← Category.assoc, hl', Category.assoc]
      rw [← htop]
      simp only [L, Category.assoc, Iso.hom_inv_id_assoc]
      rfl
    change (e j).hom ≫ (a j).inv ≫ H.map (C.ι.app j) ≫ alim.hom = _
    rw [hh]
    simp only [Iso.inv_hom_id_assoc]
    ext x
    exact (hq j x).symm
  refine ⟨hqiso, ?_⟩
  intro j x hx
  have he : colimit.ι M j x = colimit.ι M j 0 := by
    apply (ConcreteCategory.bijective_of_isIso q).1
    simpa only [map_zero] using hx
  obtain ⟨k, f, f', hk⟩ := (Concrete.colimit_rep_eq_iff_exists M x 0).mp he
  exact ⟨k, f, by simpa only [map_zero] using hk⟩

end AlgebraicGeometry
