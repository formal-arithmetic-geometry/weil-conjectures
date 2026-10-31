/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Topology.Spectral.Basic
public import Mathlib.Topology.Spectral.Hom
public import WeilConjectures.Topology.SetsInverseImageComposition
import WeilConjectures.Topology.SpectralDirectedLimit
import WeilConjectures.Topology.SpectralLimitDescendOpens
import Mathlib.Topology.Sheaves.Sheafify

/-!
# Sections of inverse images on spectral limits

Source: Stacks Project, Sheaves on Spaces, Tag 0A32, with the composition maps of Tag 008I
(blueprint: lem-weil-pbc-spectral-limit-pullback-sections).
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace

namespace TopCat.Sheaf

open TopCat.Presheaf

@[irreducible] noncomputable def compUnit {A B C : TopCat.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (G : C.Sheaf (Type u)) :
    (pullback (Type u) g).obj G ⟶
      (pushforward (Type u) f).obj ((pullback (Type u) (f ≫ g)).obj G) :=
  (pullbackPushforwardAdjunction (Type u) f).unit.app _ ≫
    (pushforward (Type u) f).map
      ((Classical.choose (exists_sets_inverseImage_comp f g)).hom.app G)

theorem compUnit_unit {A B C : TopCat.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (G : C.Sheaf (Type u)) :
    (pullbackPushforwardAdjunction (Type u) g).unit.app G ≫
      (pushforward (Type u) g).map (compUnit f g G) =
    (pullbackPushforwardAdjunction (Type u) (f ≫ g)).unit.app G := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext W
  apply ConcreteCategory.hom_ext
  intro s
  unfold compUnit
  exact (Classical.choose_spec (exists_sets_inverseImage_comp f g) G).1 W.unop s

private theorem compUnit_unique {A B C : TopCat.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (G : C.Sheaf (Type u))
    (m : (pullback (Type u) g).obj G ⟶
      (pushforward (Type u) f).obj ((pullback (Type u) (f ≫ g)).obj G))
    (hm : (pullbackPushforwardAdjunction (Type u) g).unit.app G ≫
      (pushforward (Type u) g).map m =
        (pullbackPushforwardAdjunction (Type u) (f ≫ g)).unit.app G) :
    m = compUnit f g G := by
  apply ((pullbackPushforwardAdjunction (Type u) g).homEquiv _ _).injective
  simpa only [Adjunction.homEquiv_unit] using hm.trans (compUnit_unit f g G).symm

theorem compUnit_comp {A B C D : TopCat.{u}}
    (h : A ⟶ B) (f : B ⟶ C) (g : C ⟶ D) (G : D.Sheaf (Type u)) :
    compUnit f g G ≫ (pushforward (Type u) f).map (compUnit h (f ≫ g) G) =
      compUnit (h ≫ f) g G := by
  apply compUnit_unique (h ≫ f) g G
  rw [Functor.map_comp, ← Category.assoc, compUnit_unit]
  exact compUnit_unit h (f ≫ g) G

private theorem compUnit_id {B C : TopCat.{u}} (g : B ⟶ C)
    (G : C.Sheaf (Type u)) : compUnit (𝟙 B) g G = 𝟙 _ := by
  symm
  apply compUnit_unique (𝟙 B) g G
  change (pullbackPushforwardAdjunction (Type u) g).unit.app G ≫
    (pushforward (Type u) g).map (𝟙 _) =
      (pullbackPushforwardAdjunction (Type u) g).unit.app G
  rw [CategoryTheory.Functor.map_id]
  exact Category.comp_id _

private theorem compUnit_comp_heq {A B C D : TopCat.{u}}
    (h : A ⟶ B) (f : B ⟶ C) (g : C ⟶ D) (G : D.Sheaf (Type u))
    (fg : B ⟶ D) (hfg : f ≫ g = fg)
    (hf : A ⟶ C) (hhf : h ≫ f = hf)
    (W : Opens C) (V : Opens B) (hV : V = (Opens.map f).obj W)
    (t : ((pullback (Type u) g).obj G).obj.obj (op W))
    (t' : ((pullback (Type u) fg).obj G).obj.obj (op V))
    (ht : HEq t' ((compUnit f g G).hom.app (op W) t)) :
    HEq ((compUnit h fg G).hom.app (op V) t')
      ((compUnit hf g G).hom.app (op W) t) := by
  subst fg
  subst hf
  subst V
  cases ht
  exact heq_of_eq (congrArg (fun m ↦ m.hom.app (op W) t) (compUnit_comp h f g G))

@[irreducible] private noncomputable def unitStalk {A B : TopCat.{u}}
    (f : A ⟶ B) (G : B.Sheaf (Type u)) (x : A) :
    Presheaf.stalk G.obj (f x) ⟶ Presheaf.stalk ((pullback (Type u) f).obj G).obj x :=
  (Presheaf.stalkFunctor (Type u) (f x)).map
    ((pullbackPushforwardAdjunction (Type u) f).unit.app G).hom ≫
      Presheaf.stalkPushforward (Type u) f ((pullback (Type u) f).obj G).obj x

set_option backward.isDefEq.respectTransparency false in
private theorem germ_unitStalk {A B : TopCat.{u}}
    (f : A ⟶ B) (G : B.Sheaf (Type u)) (x : A) (W : Opens B) (hx : f x ∈ W)
    (t : G.obj.obj (op W)) :
    unitStalk f G x (Presheaf.germ G.obj W (f x) hx t) =
      Presheaf.germ ((pullback (Type u) f).obj G).obj ((Opens.map f).obj W) x hx
        (((pullbackPushforwardAdjunction (Type u) f).unit.app G).hom.app (op W) t) := by
  unfold unitStalk
  change Presheaf.stalkPushforward (Type u) f _ x
    ((Presheaf.stalkFunctor (Type u) (f x)).map
      ((pullbackPushforwardAdjunction (Type u) f).unit.app G).hom
        (Presheaf.germ G.obj W (f x) hx t)) = _
  erw [Presheaf.stalkFunctor_map_germ_apply]
  exact Presheaf.stalkPushforward_germ_apply (Type u) f _ W x hx _

set_option backward.isDefEq.respectTransparency false in
private theorem constructed_unit {A B : TopCat.{u}} (f : A ⟶ B)
    (G : B.Sheaf (Type u)) :
    ((pullbackPushforwardAdjunction (Type u) f).unit.app G ≫
      (pushforward (Type u) f).map ((pullbackIso (Type u) f).hom.app G)).hom =
    (Presheaf.pullbackPushforwardAdjunction (Type u) f).unit.app G.obj ≫
      (Presheaf.pushforward (Type u) f).map
        (CategoryTheory.toSheafify (Opens.grothendieckTopology A)
          ((Presheaf.pullback (Type u) f).obj G.obj)) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (pullbackPushforwardAdjunction (Type u) f)
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Opens.map f) (Type u) (Opens.grothendieckTopology B)
        (Opens.grothendieckTopology A)) G
  refine (congrArg (fun m ↦ m.hom) h).trans ?_
  change (sheafToPresheaf (Opens.grothendieckTopology B) (Type u)).map
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Opens.map f) (Type u) (Opens.grothendieckTopology B)
        (Opens.grothendieckTopology A)).unit.app G) = _
  rw [Functor.sheafPullbackConstruction.sheafAdjunctionContinuous,
    Adjunction.map_restrictFullyFaithful_unit_app]
  simp only [Iso.refl_hom]
  rw [Adjunction.comp_unit_app]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem unitStalk_bijective {A B : TopCat.{u}} (f : A ⟶ B)
    (G : B.Sheaf (Type u)) (x : A) : Function.Bijective (unitStalk f G x) := by
  let θ := CategoryTheory.toSheafify (Opens.grothendieckTopology A)
    ((Presheaf.pullback (Type u) f).obj G.obj)
  let e := ((pullbackIso (Type u) f).app G)
  have he : IsIso ((Presheaf.stalkFunctor (Type u) x).map e.hom.hom) := by
    infer_instance
  have hθ : IsIso ((Presheaf.stalkFunctor (Type u) x).map θ) :=
    Presheaf.stalkFunctor_map_unit_toSheafify_isIso x (Type u) _
  have h : unitStalk f G x ≫ (Presheaf.stalkFunctor (Type u) x).map e.hom.hom =
      Presheaf.stalkPullbackHom (Type u) f G.obj x ≫
        (Presheaf.stalkFunctor (Type u) x).map θ := by
    apply Presheaf.stalk_hom_ext
    intro W hx
    apply ConcreteCategory.hom_ext
    intro t
    change (Presheaf.stalkFunctor (Type u) x).map e.hom.hom
      (unitStalk f G x (Presheaf.germ G.obj W (f x) hx t)) =
      (Presheaf.stalkFunctor (Type u) x).map θ
        (Presheaf.stalkPullbackHom (Type u) f G.obj x
          (Presheaf.germ G.obj W (f x) hx t))
    rw [germ_unitStalk, Presheaf.stalkFunctor_map_germ_apply]
    have hc := congrArg (fun m ↦ m.app (op W) t) (constructed_unit f G)
    change e.hom.hom.app (op ((Opens.map f).obj W))
      (((pullbackPushforwardAdjunction (Type u) f).unit.app G).hom.app (op W) t) = _ at hc
    rw [hc]
    rw [← ConcreteCategory.comp_apply, Presheaf.germ_stalkPullbackHom]
    erw [ConcreteCategory.comp_apply, Presheaf.stalkFunctor_map_germ_apply]
    rfl
  have hi : IsIso (Presheaf.stalkPullbackHom (Type u) f G.obj x) :=
    (Presheaf.stalkPullbackIso (Type u) f G.obj x).isIso_hom
  have hu : IsIso (unitStalk f G x ≫ (Presheaf.stalkFunctor (Type u) x).map e.hom.hom) := by
    rw [h]
    infer_instance
  have hu' : IsIso (unitStalk f G x) := IsIso.of_isIso_comp_right
    (unitStalk f G x) ((Presheaf.stalkFunctor (Type u) x).map e.hom.hom)
  exact (CategoryTheory.isIso_iff_bijective (unitStalk f G x)).mp hu'

set_option backward.isDefEq.respectTransparency false in
private theorem unit_equal_on_compact {A B : TopCat.{u}} [PrespectralSpace B]
    (q : A ⟶ B) (hq : IsSpectralMap q) (H : B.Sheaf (Type u))
    (W : Opens B) (hW : IsCompact (W : Set B))
    (t t' : H.obj.obj (op W))
    (he : ((pullbackPushforwardAdjunction (Type u) q).unit.app H).hom.app (op W) t =
      ((pullbackPushforwardAdjunction (Type u) q).unit.app H).hom.app (op W) t') :
    ∃ (V : Opens B) (hVW : V ≤ W), IsCompact (V : Set B) ∧
      q ⁻¹' (W : Set B) ⊆ q ⁻¹' (V : Set B) ∧
      ∀ (y : B) (hy : y ∈ V),
        Presheaf.germ H.obj W y (hVW hy) t = Presheaf.germ H.obj W y (hVW hy) t' := by
  classical
  have hl : ∀ x : (Opens.map q).obj W,
      ∃ (V : Opens B) (hVW : V ≤ W), q x.1 ∈ V ∧ IsCompact (V : Set B) ∧
        ∀ (y : B) (hy : y ∈ V),
          Presheaf.germ H.obj W y (hVW hy) t =
            Presheaf.germ H.obj W y (hVW hy) t' := by
    intro x
    have hg : Presheaf.germ H.obj W (q x.1) x.2 t =
        Presheaf.germ H.obj W (q x.1) x.2 t' := by
      apply (unitStalk_bijective q H x.1).1
      rw [germ_unitStalk, germ_unitStalk, he]
    obtain ⟨O, hxO, iO, iO', hO⟩ := Presheaf.germ_eq H.obj (q x.1) x.2 x.2 t t' hg
    obtain ⟨V, hVc, hVo, hxV, hVO⟩ :=
      PrespectralSpace.exists_isCompact_and_isOpen_between
        (isCompact_singleton (x := q x.1)) O.isOpen (Set.singleton_subset_iff.mpr hxO)
    refine ⟨⟨V, hVo⟩, hVO.trans iO.le, hxV (Set.mem_singleton _), hVc, ?_⟩
    intro y hy
    exact Presheaf.germ_ext H.obj O (hVO hy) iO iO' hO
  choose V hVW hxV hVc hVg using hl
  obtain ⟨b, hb⟩ := (hq.isCompact_preimage_of_isOpen W.isOpen hW).elim_finite_subcover
    (fun x ↦ q ⁻¹' (V x : Set B)) (fun x ↦ (V x).isOpen.preimage hq.continuous)
    (by intro x hx; exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩)
  let E : Opens B := ⨆ x : b, V x.1
  have hEW : E ≤ W := iSup_le fun x ↦ hVW x.1
  refine ⟨E, hEW, ?_, ?_, ?_⟩
  · simpa only [E, Opens.iSup_mk, Opens.carrier_eq_coe, Opens.coe_mk] using
      (isCompact_iUnion (fun x : b ↦ hVc x.1))
  · intro x hx
    obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp (hb hx)
    exact Opens.mem_iSup.mpr ⟨⟨a, ha⟩, hxa⟩
  · intro y hy
    obtain ⟨a, hya⟩ := Opens.mem_iSup.mp hy
    exact hVg a.1 y hya

set_option backward.isDefEq.respectTransparency false in
private theorem eventually_unit_equal
    {I : Type u} [Preorder I] (S : I → TopCat.{u})
    [∀ j : I, SpectralSpace (S j)]
    (f : ∀ (j k : I), j ≤ k → (S k ⟶ S j))
    (X : TopCat.{u}) (p : ∀ j : I, X ⟶ S j)
    (hp : ∀ j, IsSpectralMap (p j))
    (hd : ∀ (j : I) (W V : Opens (S j)),
      IsCompact (W : Set (S j)) → IsCompact (V : Set (S j)) →
      p j ⁻¹' (W : Set (S j)) ⊆ p j ⁻¹' (V : Set (S j)) →
      ∃ (k : I) (hjk : j ≤ k),
        f j k hjk ⁻¹' (W : Set (S j)) ⊆ f j k hjk ⁻¹' (V : Set (S j)))
    (j : I) (H : (S j).Sheaf (Type u)) (W : Opens (S j))
    (hW : IsCompact (W : Set (S j))) (t t' : H.obj.obj (op W))
    (he : ((pullbackPushforwardAdjunction (Type u) (p j)).unit.app H).hom.app (op W) t =
      ((pullbackPushforwardAdjunction (Type u) (p j)).unit.app H).hom.app (op W) t') :
    ∃ (k : I) (hjk : j ≤ k),
      ((pullbackPushforwardAdjunction (Type u) (f j k hjk)).unit.app H).hom.app (op W) t =
        ((pullbackPushforwardAdjunction (Type u) (f j k hjk)).unit.app H).hom.app (op W) t' := by
  obtain ⟨V, hVW, hVc, hcover, hVg⟩ := unit_equal_on_compact (p j) (hp j) H W hW t t' he
  obtain ⟨k, hjk, hsub⟩ := hd j W V hW hVc hcover
  refine ⟨k, hjk, ?_⟩
  apply Presheaf.section_ext ((pullback (Type u) (f j k hjk)).obj H)
    ((Opens.map (f j k hjk)).obj W)
  intro x hx
  rw [← germ_unitStalk, ← germ_unitStalk]
  exact congrArg (unitStalk (f j k hjk) H x) (hVg (f j k hjk x) (hsub hx))

@[irreducible] noncomputable def compMap {A B C : TopCat.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (k : A ⟶ C) (h : f ≫ g = k)
    (G : C.Sheaf (Type u)) :
    (pullback (Type u) g).obj G ⟶
      (pushforward (Type u) f).obj ((pullback (Type u) k).obj G) :=
  compUnit f g G ≫ (pushforward (Type u) f).map
    (eqToHom (congrArg (fun a ↦ (pullback (Type u) a).obj G) h))

theorem compMap_heq {A B C : TopCat.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (k : A ⟶ C) (h : f ≫ g = k)
    (G : C.Sheaf (Type u)) (W : Opens B) (t : ((pullback (Type u) g).obj G).obj.obj (op W)) :
    HEq ((compMap f g k h G).hom.app (op W) t)
      ((compUnit f g G).hom.app (op W) t) := by
  subst k
  unfold compMap
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id]
  rfl

private theorem compMap_unit {A B C : TopCat.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (k : A ⟶ C) (h : f ≫ g = k)
    (G : C.Sheaf (Type u)) (U : Opens C) (t : G.obj.obj (op U)) :
    HEq ((compMap f g k h G).hom.app (op ((Opens.map g).obj U))
      (((pullbackPushforwardAdjunction (Type u) g).unit.app G).hom.app (op U) t))
      (((pullbackPushforwardAdjunction (Type u) k).unit.app G).hom.app (op U) t) := by
  subst k
  refine (compMap_heq f g (f ≫ g) rfl G _ _).trans ?_
  exact heq_of_eq (congrArg (fun m ↦ m.hom.app (op U) t) (compUnit_unit f g G))

private theorem compMap_iso {A B C : TopCat.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (k : A ⟶ C) (h : f ≫ g = k)
    (G : C.Sheaf (Type u)) :
    ∃ e : (pullback (Type u) f).obj ((pullback (Type u) g).obj G) ≅
      (pullback (Type u) k).obj G,
      compMap f g k h G =
        (pullbackPushforwardAdjunction (Type u) f).unit.app _ ≫
          (pushforward (Type u) f).map e.hom := by
  subst k
  refine ⟨(Classical.choose (exists_sets_inverseImage_comp f g)).app G, ?_⟩
  unfold compMap compUnit
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id]
  exact Category.comp_id _

set_option backward.isDefEq.respectTransparency false in
private theorem compMap_equal_iff {A B C : TopCat.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (k : A ⟶ C) (h : f ≫ g = k)
    (G : C.Sheaf (Type u)) (W : Opens B)
    (t t' : ((pullback (Type u) g).obj G).obj.obj (op W)) :
    (compMap f g k h G).hom.app (op W) t = (compMap f g k h G).hom.app (op W) t' ↔
      ((pullbackPushforwardAdjunction (Type u) f).unit.app _).hom.app (op W) t =
        ((pullbackPushforwardAdjunction (Type u) f).unit.app _).hom.app (op W) t' := by
  obtain ⟨e, he⟩ := compMap_iso f g k h G
  rw [he]
  change e.hom.hom.app _
    (((pullbackPushforwardAdjunction (Type u) f).unit.app _).hom.app (op W) t) =
      e.hom.hom.app _
        (((pullbackPushforwardAdjunction (Type u) f).unit.app _).hom.app (op W) t') ↔ _
  exact (CategoryTheory.isIso_iff_bijective (e.hom.hom.app _)).mp inferInstance |>.1.eq_iff

private theorem compMap_comp {A B C D : TopCat.{u}}
    (h : A ⟶ B) (f : B ⟶ C) (g : C ⟶ D)
    (fg : B ⟶ D) (hfg : f ≫ g = fg)
    (hf : A ⟶ C) (hhf : h ≫ f = hf)
    (hfg' : A ⟶ D) (hhfg : h ≫ fg = hfg') (hhfg' : hf ≫ g = hfg')
    (G : D.Sheaf (Type u)) (W : Opens C)
    (t : ((pullback (Type u) g).obj G).obj.obj (op W))
    (V : Opens B) (hV : V = (Opens.map f).obj W)
    (t' : ((pullback (Type u) fg).obj G).obj.obj (op V))
    (ht : HEq t' ((compMap f g fg hfg G).hom.app (op W) t)) :
    HEq ((compMap h fg hfg' hhfg G).hom.app (op V) t')
      ((compMap hf g hfg' hhfg' G).hom.app (op W) t) := by
  refine (compMap_heq h fg hfg' hhfg G V t').trans ?_
  refine (compUnit_comp_heq h f g G fg hfg hf hhf W V hV t t'
    (ht.trans (compMap_heq f g fg hfg G W t))).trans ?_
  exact (compMap_heq hf g hfg' hhfg' G W t).symm

private theorem heq_eq_iff {α β : Type u} {a b : α} {c d : β}
    (hac : HEq a c) (hbd : HEq b d) : a = b ↔ c = d := by
  cases hac
  cases hbd
  rfl

private theorem finite_upper_bound {I : Type u} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] {L : Type u} [Finite L] (a : L → I) (i : I) :
    ∃ k, i ≤ k ∧ ∀ l, a l ≤ k := by
  classical
  have h : ∀ b : Finset I, ∃ k, i ≤ k ∧ ∀ j ∈ b, j ≤ k := by
    intro b
    induction b using Finset.induction_on with
    | empty => exact ⟨i, le_rfl, by simp⟩
    | @insert j b hj ih =>
      obtain ⟨k, hik, hk⟩ := ih
      obtain ⟨k', hkk', hjk'⟩ := exists_ge_ge k j
      refine ⟨k', hik.trans hkk', ?_⟩
      intro l hl
      rcases Finset.mem_insert.mp hl with rfl | hl
      · exact hjk'
      · exact (hk l hl).trans hkk'
  let := Fintype.ofFinite L
  obtain ⟨k, hik, hk⟩ := h (Finset.univ.image a)
  exact ⟨k, hik, fun l ↦ hk (a l) (Finset.mem_image.mpr ⟨l, Finset.mem_univ _, rfl⟩)⟩

set_option backward.isDefEq.respectTransparency false in
private theorem finite_local_unit_sections {A B : TopCat.{u}}
    [PrespectralSpace A] [PrespectralSpace B]
    (q : A ⟶ B) (G : B.Sheaf (Type u)) (U : Opens B)
    (hU : IsCompact (q ⁻¹' (U : Set B)))
    (s : ((pullback (Type u) q).obj G).obj.obj (op ((Opens.map q).obj U))) :
    ∃ (L : Type u) (_ : Finite L) (W : L → Opens A) (V : L → Opens B),
      (∀ l, IsCompact (W l : Set A)) ∧ (∀ l, IsCompact (V l : Set B)) ∧
      ∃ (hVU : ∀ l, V l ≤ U) (hWV : ∀ l, W l ≤ (Opens.map q).obj (V l)),
        (⨆ l, W l) = (Opens.map q).obj U ∧
        ∃ t : ∀ l, G.obj.obj (op (V l)),
          ∀ l, ((pullback (Type u) q).obj G).obj.map
              (homOfLE ((hWV l).trans ((Opens.map q).monotone (hVU l)))).op s =
            ((pullback (Type u) q).obj G).obj.map (homOfLE (hWV l)).op
              (((pullbackPushforwardAdjunction (Type u) q).unit.app G).hom.app
                (op (V l)) (t l)) := by
  classical
  let H := (pullback (Type u) q).obj G
  have hl : ∀ x : (Opens.map q).obj U,
      ∃ (W : Opens A) (V : Opens B) (hVU : V ≤ U) (hWV : W ≤ (Opens.map q).obj V),
        x.1 ∈ W ∧ IsCompact (W : Set A) ∧ IsCompact (V : Set B) ∧
        ∃ t : G.obj.obj (op V),
          H.obj.map (homOfLE (hWV.trans ((Opens.map q).monotone hVU))).op s =
            H.obj.map (homOfLE hWV).op
              (((pullbackPushforwardAdjunction (Type u) q).unit.app G).hom.app (op V) t) := by
    intro x
    obtain ⟨a, ha⟩ := (unitStalk_bijective q G x.1).2 (Presheaf.germ H.obj _ x.1 x.2 s)
    obtain ⟨V₀, hxV₀, t₀, ht₀⟩ := Presheaf.exists_germ_eq G.obj a
    obtain ⟨V, hVc, hVo, hxV, hVV⟩ :=
      PrespectralSpace.exists_isCompact_and_isOpen_between
        (isCompact_singleton (x := q x.1)) (V₀ ⊓ U).isOpen
          (Set.singleton_subset_iff.mpr ⟨hxV₀, x.2⟩)
    let V' : Opens B := ⟨V, hVo⟩
    have hVV₀ : V' ≤ V₀ := fun y hy ↦ (hVV hy).1
    have hVU : V' ≤ U := fun y hy ↦ (hVV hy).2
    let t := G.obj.map (homOfLE hVV₀).op t₀
    have hg : Presheaf.germ H.obj ((Opens.map q).obj V') x.1 (hxV (Set.mem_singleton _))
        (((pullbackPushforwardAdjunction (Type u) q).unit.app G).hom.app (op V') t) =
        Presheaf.germ H.obj _ x.1 x.2 s := by
      rw [← germ_unitStalk]
      have ht : Presheaf.germ G.obj V' (q x.1) (hxV (Set.mem_singleton _)) t = a := by
        exact (Presheaf.germ_res_apply G.obj (homOfLE hVV₀) (q x.1) _ t₀).trans ht₀
      rw [ht]
      exact ha
    obtain ⟨O, hxO, iOV, iOU, hO⟩ := Presheaf.germ_eq H.obj x.1 _ x.2 _ s hg
    obtain ⟨W, hWc, hWo, hxW, hWO⟩ :=
      PrespectralSpace.exists_isCompact_and_isOpen_between
        (isCompact_singleton (x := x.1)) O.isOpen (Set.singleton_subset_iff.mpr hxO)
    refine ⟨⟨W, hWo⟩, V', hVU, hWO.trans iOV.le,
      hxW (Set.mem_singleton _), hWc, hVc, t, ?_⟩
    have hres := congrArg (H.obj.map (homOfLE (show (⟨W, hWo⟩ : Opens A) ≤ O from hWO)).op) hO
    simp only [← ConcreteCategory.comp_apply, ← H.obj.map_comp] at hres
    convert hres.symm using 1 <;> congr 2
  choose W V hVU hWV hxW hWc hVc t ht using hl
  obtain ⟨b, hb⟩ := hU.elim_finite_subcover (fun x ↦ (W x : Set A))
    (fun x ↦ (W x).isOpen) (fun x hx ↦ Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxW ⟨x, hx⟩⟩)
  refine ⟨b, inferInstance, (fun l ↦ W l.1), (fun l ↦ V l.1),
    (fun l ↦ hWc l.1), (fun l ↦ hVc l.1), (fun l ↦ hVU l.1),
    (fun l ↦ hWV l.1), ?_, (fun l ↦ t l.1), (fun l ↦ ht l.1)⟩
  apply le_antisymm
  · exact iSup_le fun l ↦ (hWV l.1).trans ((Opens.map q).monotone (hVU l.1))
  · intro x hx
    obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp (hb hx)
    exact Opens.mem_iSup.mpr ⟨⟨a, ha⟩, hxa⟩

private theorem descend_finite_cover
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (S : I → TopCat.{u}) [∀ j : I, SpectralSpace (S j)]
    (f : ∀ (j k : I), j ≤ k → (S k ⟶ S j))
    (hf : ∀ (j k : I) (h : j ≤ k), IsSpectralMap (f j k h))
    (hc : ∀ (j k l : I) (hjk : j ≤ k) (hkl : k ≤ l) (x : S l),
      f j k hjk (f k l hkl x) = f j l (hjk.trans hkl) x)
    (X : TopCat.{u}) (p : ∀ j : I, X ⟶ S j)
    (hp : ∀ (j k : I) (h : j ≤ k) (x : X), f j k h (p k x) = p j x)
    (hlift : ∀ W : Opens X, IsCompact (W : Set X) →
      ∃ (j : I) (V : Opens (S j)), IsCompact (V : Set (S j)) ∧
        (Opens.map (p j)).obj V = W)
    (hdesc : ∀ (j k : I) (W : Opens (S j)) (V : Opens (S k)),
      IsCompact (W : Set (S j)) → IsCompact (V : Set (S k)) →
      p j ⁻¹' (W : Set (S j)) ⊆ p k ⁻¹' (V : Set (S k)) →
      ∃ (l : I) (hjl : j ≤ l) (hkl : k ≤ l),
        f j l hjl ⁻¹' (W : Set (S j)) ⊆ f k l hkl ⁻¹' (V : Set (S k)))
    (i : I) (U : Opens (S i)) (hU : IsCompact (U : Set (S i)))
    {L : Type u} [Finite L] (W : L → Opens X) (V : L → Opens (S i))
    (hW : ∀ l, IsCompact (W l : Set X)) (hV : ∀ l, IsCompact (V l : Set (S i)))
    (hVU : ∀ l, V l ≤ U) (hWV : ∀ l, W l ≤ (Opens.map (p i)).obj (V l))
    (hcover : (⨆ l, W l) = (Opens.map (p i)).obj U) :
    ∃ (j : I) (hij : i ≤ j) (T : L → Opens (S j)),
      (∀ l, IsCompact (T l : Set (S j))) ∧
      (∀ l, (Opens.map (p j)).obj (T l) = W l) ∧
      (∀ l, T l ≤ (Opens.map (f i j hij)).obj (V l)) ∧
      (⨆ l, T l) = (Opens.map (f i j hij)).obj U := by
  classical
  choose a B hBc hB using fun l ↦ hlift (W l) (hW l)
  obtain ⟨j, hij, haj⟩ := finite_upper_bound a i
  let T₀ (l : L) := (Opens.map (f (a l) j (haj l))).obj (B l)
  have hT₀c (l : L) : IsCompact (T₀ l : Set (S j)) :=
    (hf (a l) j (haj l)).isCompact_preimage_of_isOpen (B l).isOpen (hBc l)
  have hT₀ (l : L) : (Opens.map (p j)).obj (T₀ l) = W l := by
    rw [← hB l]
    apply Opens.ext
    ext x
    change f (a l) j (haj l) (p j x) ∈ B l ↔ p (a l) x ∈ B l
    rw [hp]
  have hsub (l : L) : ∃ (k : I) (hjk : j ≤ k) (hik : i ≤ k),
      f j k hjk ⁻¹' (T₀ l : Set (S j)) ⊆ f i k hik ⁻¹' (V l : Set (S i)) := by
    apply hdesc j i (T₀ l) (V l) (hT₀c l) (hV l)
    intro x hx
    exact hWV l (hT₀ l ▸ hx)
  choose b hjb hib hb using hsub
  obtain ⟨k, hjk, hbk⟩ := finite_upper_bound b j
  let T₁ (l : L) := (Opens.map (f j k hjk)).obj (T₀ l)
  have hT₁c (l : L) : IsCompact (T₁ l : Set (S k)) :=
    (hf j k hjk).isCompact_preimage_of_isOpen (T₀ l).isOpen (hT₀c l)
  have hT₁ (l : L) : (Opens.map (p k)).obj (T₁ l) = W l := by
    rw [← hT₀ l]
    apply Opens.ext
    ext x
    change f j k hjk (p k x) ∈ T₀ l ↔ p j x ∈ T₀ l
    rw [hp]
  have hT₁V (l : L) : T₁ l ≤ (Opens.map (f i k (hij.trans hjk))).obj (V l) := by
    intro x hx
    have hx' : f j (b l) (hjb l) (f (b l) k (hbk l) x) ∈ T₀ l := by
      rw [hc]
      exact hx
    have hv := hb l hx'
    change f i (b l) (hib l) (f (b l) k (hbk l) x) ∈ V l at hv
    rw [hc] at hv
    exact hv
  let C : Opens (S k) := ⨆ l, T₁ l
  have hCc : IsCompact (C : Set (S k)) := by
    simpa only [C, Opens.coe_iSup] using
      (isCompact_iUnion hT₁c)
  let Uk := (Opens.map (f i k (hij.trans hjk))).obj U
  have hUkc : IsCompact (Uk : Set (S k)) :=
    (hf i k _).isCompact_preimage_of_isOpen U.isOpen hU
  have hCU : C ≤ Uk := iSup_le fun l ↦
    (hT₁V l).trans ((Opens.map (f i k _)).monotone (hVU l))
  have hUC : p k ⁻¹' (Uk : Set (S k)) ⊆ p k ⁻¹' (C : Set (S k)) := by
    intro x hx
    have hxU : p i x ∈ U := by
      change f i k (hij.trans hjk) (p k x) ∈ U at hx
      rwa [hp] at hx
    have hxW : x ∈ ⨆ l, W l := hcover.symm ▸ hxU
    obtain ⟨l, hxl⟩ := Opens.mem_iSup.mp hxW
    apply Opens.mem_iSup.mpr
    refine ⟨l, ?_⟩
    change x ∈ (Opens.map (p k)).obj (T₁ l)
    rwa [hT₁]
  obtain ⟨m, hkm, hkm', hm⟩ := hdesc k k Uk C hUkc hCc hUC
  let T (l : L) := (Opens.map (f k m hkm)).obj (T₁ l)
  refine ⟨m, hij.trans (hjk.trans hkm), T, ?_, ?_, ?_, ?_⟩
  · intro l
    exact (hf k m hkm).isCompact_preimage_of_isOpen (T₁ l).isOpen (hT₁c l)
  · intro l
    rw [← hT₁ l]
    apply Opens.ext
    ext x
    change f k m hkm (p m x) ∈ T₁ l ↔ p k x ∈ T₁ l
    rw [hp]
  · intro l x hx
    have hv := hT₁V l hx
    change f i k (hij.trans hjk) (f k m hkm x) ∈ V l at hv
    rwa [hc] at hv
  · apply le_antisymm
    · apply iSup_le
      intro l x hx
      have hx' := hCU (show f k m hkm x ∈ C from Opens.mem_iSup.mpr ⟨l, hx⟩)
      change f i k (hij.trans hjk) (f k m hkm x) ∈ U at hx'
      rwa [hc] at hx'
    · intro x hx
      have hx' : f k m hkm x ∈ Uk := by
        change f i k (hij.trans hjk) (f k m hkm x) ∈ U
        rwa [hc]
      obtain ⟨l, hxl⟩ := Opens.mem_iSup.mp (hm hx')
      exact Opens.mem_iSup.mpr ⟨l, hxl⟩

private theorem map_restrict {A B : TopCat.{u}} (q : A ⟶ B)
    {F : B.Sheaf (Type u)} {H : A.Sheaf (Type u)}
    (r : F ⟶ (pushforward (Type u) q).obj H)
    {W V : Opens B} (h : W ≤ V) (t : F.obj.obj (op V)) :
    r.hom.app (op W) (F.obj.map (homOfLE h).op t) =
      H.obj.map ((Opens.map q).map (homOfLE h)).op (r.hom.app (op V) t) := by
  exact congrArg (fun a ↦ a t) (r.hom.naturality (homOfLE h).op)

private theorem restrict_heq {A : TopCat.{u}} (H : A.Sheaf (Type u))
    {V V' W W' : Opens A} (hV : V = V') (hW : W = W') (hWV : W ≤ V) (hWV' : W' ≤ V')
    (t : H.obj.obj (op V)) (t' : H.obj.obj (op V')) (ht : HEq t t') :
    HEq (H.obj.map (homOfLE hWV).op t) (H.obj.map (homOfLE hWV').op t') := by
  subst V'
  subst W'
  cases ht
  rfl

private theorem restrict_eq_heq {A : TopCat.{u}} (H : A.Sheaf (Type u))
    {V W : Opens A} (h : W = V) (s : H.obj.obj (op V)) :
    HEq (H.obj.map (homOfLE (le_of_eq h)).op s) s := by
  subst W
  simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id]
  rfl

private theorem compMap_restrict_unit {A B C : TopCat.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (k : A ⟶ C) (h : f ≫ g = k)
    (G : C.Sheaf (Type u)) (V : Opens C) (W : Opens B)
    (hWV : W ≤ (Opens.map g).obj V)
    (hWV' : (Opens.map f).obj W ≤ (Opens.map k).obj V)
    (t : G.obj.obj (op V)) :
    (compMap f g k h G).hom.app (op W)
      (((pullback (Type u) g).obj G).obj.map (homOfLE hWV).op
        (((pullbackPushforwardAdjunction (Type u) g).unit.app G).hom.app (op V) t)) =
      ((pullback (Type u) k).obj G).obj.map (homOfLE hWV').op
        (((pullbackPushforwardAdjunction (Type u) k).unit.app G).hom.app (op V) t) := by
  rw [map_restrict]
  apply eq_of_heq
  apply restrict_heq ((pullback (Type u) k).obj G) _ rfl _ hWV' _ _
    (compMap_unit f g k h G V t)
  exact congrArg (fun a : A ⟶ C ↦ (Opens.map a).obj V) h

private theorem compMap_eq_of_later {A B C D : TopCat.{u}}
    (h : A ⟶ B) (f : B ⟶ C) (g : C ⟶ D)
    (fg : B ⟶ D) (hfg : f ≫ g = fg)
    (hf : A ⟶ C) (hhf : h ≫ f = hf)
    (hfg' : A ⟶ D) (hhfg : h ≫ fg = hfg') (hhfg' : hf ≫ g = hfg')
    (G : D.Sheaf (Type u)) (W : Opens C)
    (t t' : ((pullback (Type u) g).obj G).obj.obj (op W))
    (he : (compMap f g fg hfg G).hom.app (op W) t =
      (compMap f g fg hfg G).hom.app (op W) t') :
    (compMap hf g hfg' hhfg' G).hom.app (op W) t =
      (compMap hf g hfg' hhfg' G).hom.app (op W) t' := by
  have ht (a : _) := compMap_comp h f g fg hfg hf hhf hfg' hhfg hhfg' G W a
    ((Opens.map f).obj W) rfl
    ((compMap f g fg hfg G).hom.app (op W) a) (HEq.rfl)
  exact (heq_eq_iff (ht t) (ht t')).mp (congrArg
    ((compMap h fg hfg' hhfg G).hom.app (op ((Opens.map f).obj W))) he)

set_option backward.isDefEq.respectTransparency false in
open Classical in
/-- Sections on a compact open pulled back to a directed spectral limit form the indicated
filtered colimit. The maps `rho` and `transition` are specified by their canonical section
formulas. `HEq` transports those formulas across the equal composite maps and opens; it
introduces no choice of a different comparison map.
Source: Stacks Project, Sheaves on Spaces, Tag 0A32, with Tag 008I
(blueprint: lem-weil-pbc-spectral-limit-pullback-sections).

Proof outline, following the node:
1. The spectral directed-limit theorem makes the limit and its projections spectral;
   compact opens remain compact under every transition and projection. Upper tails are
   cofinal: extend a compatible tail family using common upper bounds.
2. The units and the composition isomorphisms define the displayed section maps and
   commute with restriction (`def-weil-pbc-topological-inverse-image`, Tag 008I).
3. The composition isomorphisms obey triple-composition coherence: use naturality of
   units and the uniqueness characterization in `exists_sets_inverseImage_comp`, testing
   morphisms on successive unit images by the composite adjunction.
4. Coherence gives the cocone and transition identities; uniqueness for the identity
   map gives the diagonal identity.
5. The inverse-image stalk bijection (Tag 008H) identifies equality of the pulled-back
   germs with equality of the original germs; a sheaf isomorphism preserves this test.
6. The unequal-germ locus inside a compact open is constructibly closed: its complement
   there is open and hence a union of compact opens.
7. If two sections never become equal, the constructibly closed nonempty-limit theorem
   gives compatible unequal germs and hence an unequal germ at the limit, a contradiction.
   Equality of all germs determines a section (Tag 0079). This proves the last clause.
8. Locally represent a limit section by unit images using the stalk bijection. Refine by
   compact opens and choose a finite cover by compactness; the empty open is allowed.
9. Descend this finite cover, its inclusions and covering equality to a common stage
   using `lem-weil-pbc-spectral-limit-descend-opens` (Tag 0A30).
10. Pull back and restrict the local sections to this stage. Their images are the given
    limit section, so they agree after pullback on every pairwise intersection.
11. By step 7 and a common upper bound they agree at a later stage. Glue there by the
    sheaf axiom. Compatibility with restriction proves surjectivity, the middle clause.
12. The elementwise description of filtered colimits of sets, together with these
    identities, surjectivity and eventual equality, identifies the target with the colimit
    (`def-weil-pbc-category-colimit`). -/
theorem spectralLimit_pullback_sections
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (S : I → TopCat.{u}) [∀ j : I, SpectralSpace (S j)]
    (f : ∀ (j k : I), j ≤ k → (S k ⟶ S j))
    (hf : ∀ (j k : I) (h : j ≤ k), IsSpectralMap (f j k h))
    (hfid : ∀ j : I, f j j le_rfl = 𝟙 (S j))
    (hfcomp : ∀ (j k l : I) (hjk : j ≤ k) (hkl : k ≤ l),
      f k l hkl ≫ f j k hjk = f j l (hjk.trans hkl))
    (X : TopCat.{u}) (p : ∀ j : I, X ⟶ S j)
    (hpcomp : ∀ (j k : I) (h : j ≤ k), p k ≫ f j k h = p j)
    (hlimit : ∀ a : ∀ j : I, S j,
      (∀ (j k : I) (h : j ≤ k), f j k h (a k) = a j) →
      ∃! x : X, ∀ j : I, p j x = a j)
    (htop : X.str = ⨅ j : I, TopologicalSpace.induced (p j) (S j).str)
    (i : I) (G : (S i).Sheaf (Type u)) (U : Opens (S i)) (hU : IsCompact (U : Set (S i)))
    (rho : ∀ (j : I) (hij : i ≤ j),
      ((pullback (Type u) (f i j hij)).obj G).obj.obj (op ((Opens.map (f i j hij)).obj U)) →
      ((pullback (Type u) (p i)).obj G).obj.obj (op ((Opens.map (p i)).obj U)))
    (transition : ∀ (j k : I) (hij : i ≤ j) (hjk : j ≤ k),
      ((pullback (Type u) (f i j hij)).obj G).obj.obj (op ((Opens.map (f i j hij)).obj U)) →
      ((pullback (Type u) (f i k (hij.trans hjk))).obj G).obj.obj
        (op ((Opens.map (f i k (hij.trans hjk))).obj U)))
    (hrho : ∀ (j : I) (hij : i ≤ j) (t :
        ((pullback (Type u) (f i j hij)).obj G).obj.obj
          (op ((Opens.map (f i j hij)).obj U))),
      HEq (rho j hij t)
        (((Classical.choose
            (exists_sets_inverseImage_comp (p j) (f i j hij))).hom.app G).hom.app
          (op ((Opens.map (p j ≫ f i j hij)).obj U))
            (((pullbackPushforwardAdjunction (Type u) (p j)).unit.app
              ((pullback (Type u) (f i j hij)).obj G)).hom.app
                (op ((Opens.map (f i j hij)).obj U)) t)))
    (htransition : ∀ (j k : I) (hij : i ≤ j) (hjk : j ≤ k) (t :
        ((pullback (Type u) (f i j hij)).obj G).obj.obj
          (op ((Opens.map (f i j hij)).obj U))),
      HEq (transition j k hij hjk t)
        (((Classical.choose
            (exists_sets_inverseImage_comp (f j k hjk) (f i j hij))).hom.app G).hom.app
          (op ((Opens.map (f j k hjk ≫ f i j hij)).obj U))
            (((pullbackPushforwardAdjunction (Type u) (f j k hjk)).unit.app
              ((pullback (Type u) (f i j hij)).obj G)).hom.app
                (op ((Opens.map (f i j hij)).obj U)) t))) :
    ((∀ (j : I) (hij : i ≤ j) (t : _), transition j j hij le_rfl t = t) ∧
      (∀ (j k : I) (hij : i ≤ j) (hjk : j ≤ k) (t : _),
        rho k (hij.trans hjk) (transition j k hij hjk t) = rho j hij t) ∧
      (∀ (j k l : I) (hij : i ≤ j) (hjk : j ≤ k) (hkl : k ≤ l) (t : _),
        transition k l (hij.trans hjk) hkl (transition j k hij hjk t) =
          transition j l hij (hjk.trans hkl) t)) ∧
    (∀ s : ((pullback (Type u) (p i)).obj G).obj.obj (op ((Opens.map (p i)).obj U)),
      ∃ (j : I) (hij : i ≤ j) (t : _), rho j hij t = s) ∧
    (∀ (j : I) (hij : i ≤ j) (t t' : _), rho j hij t = rho j hij t' →
      ∃ (k : I) (hjk : j ≤ k), transition j k hij hjk t = transition j k hij hjk t') := by
  classical
  have hfid' : ∀ j : I, (fun x ↦ f j j le_rfl x) = id := by
    intro j
    funext x
    exact congrArg (fun a : S j ⟶ S j ↦ a x) (hfid j)
  have hfcomp' : ∀ (j k l : I) (hjk : j ≤ k) (hkl : k ≤ l),
      (fun x ↦ f j k hjk (f k l hkl x)) = fun x ↦ f j l (hjk.trans hkl) x := by
    intro j k l hjk hkl
    exact congrArg (fun a : S l ⟶ S j ↦ fun x ↦ a x) (hfcomp j k l hjk hkl)
  have hpcomp' : ∀ (j k : I) (h : j ≤ k),
      (fun x ↦ f j k h (p k x)) = fun x ↦ p j x := by
    intro j k h
    exact congrArg (fun a : X ⟶ S j ↦ fun x ↦ a x) (hpcomp j k h)
  have hpinj : Function.Injective (fun x : X ↦ fun j ↦ p j x) := by
    intro x y hxy
    obtain ⟨z, hz, hu⟩ := hlimit (fun j ↦ p j x) (by
      intro j k h
      exact congrFun (hpcomp' j k h) x)
    exact (hu x (fun j ↦ rfl)).trans (hu y (fun j ↦ (congrFun hxy j).symm)).symm
  have hs := Topology.spectralSpace_directedLimit (fun j ↦ S j)
    (fun j k h ↦ f j k h) hf hfid' hfcomp' X (fun j ↦ p j)
    (fun j ↦ (p j).hom.continuous) hpcomp' hpinj
    (fun a ha ↦ (hlimit a ha).exists) htop
  have hd := (Topology.spectralLimit_descend_opens (fun j ↦ S j)
    (fun j k h ↦ f j k h) hf (fun j x ↦ congrFun (hfid' j) x)
    (fun j k l hjk hkl x ↦ congrFun (hfcomp' j k l hjk hkl) x)
    X (fun j ↦ p j) (fun j ↦ (p j).hom.continuous)
    (fun j k h x ↦ congrFun (hpcomp' j k h) x) hlimit htop).2.1
  have hd' : ∀ (j : I) (W V : Opens (S j)),
      IsCompact (W : Set (S j)) → IsCompact (V : Set (S j)) →
      p j ⁻¹' (W : Set (S j)) ⊆ p j ⁻¹' (V : Set (S j)) →
      ∃ (k : I) (hjk : j ≤ k),
        f j k hjk ⁻¹' (W : Set (S j)) ⊆ f j k hjk ⁻¹' (V : Set (S j)) := by
    intro j W V hW hV hsub
    obtain ⟨k, hjk, hjk', hk⟩ := hd j j W V W.isOpen hW V.isOpen hV hsub
    exact ⟨k, hjk, hk⟩
  have hevent : ∀ (j : I) (hij : i ≤ j) (W : Opens (S j)),
      IsCompact (W : Set (S j)) →
      ∀ t t' : ((pullback (Type u) (f i j hij)).obj G).obj.obj (op W),
      (compMap (p j) (f i j hij) (p i) (hpcomp i j hij) G).hom.app (op W) t =
        (compMap (p j) (f i j hij) (p i) (hpcomp i j hij) G).hom.app (op W) t' →
      ∃ (k : I) (hjk : j ≤ k),
        (compMap (f j k hjk) (f i j hij) (f i k (hij.trans hjk))
          (hfcomp i j k hij hjk) G).hom.app (op W) t =
        (compMap (f j k hjk) (f i j hij) (f i k (hij.trans hjk))
          (hfcomp i j k hij hjk) G).hom.app (op W) t' := by
    intro j hij W hW t t' he
    have he' := (compMap_equal_iff _ _ _ _ _ _ t t').mp he
    obtain ⟨k, hjk, hk⟩ := eventually_unit_equal S f X p hs.2 hd' j
      ((pullback (Type u) (f i j hij)).obj G) W hW t t' he'
    exact ⟨k, hjk, (compMap_equal_iff _ _ _ _ _ _ t t').mpr hk⟩
  have hr : ∀ (j : I) (hij : i ≤ j) (t : _),
      HEq (rho j hij t)
        ((compUnit (p j) (f i j hij) G).hom.app
          (op ((Opens.map (f i j hij)).obj U)) t) := by
    intro j hij t
    unfold compUnit
    exact hrho j hij t
  have ht : ∀ (j k : I) (hij : i ≤ j) (hjk : j ≤ k) (t : _),
      HEq (transition j k hij hjk t)
        ((compUnit (f j k hjk) (f i j hij) G).hom.app
          (op ((Opens.map (f i j hij)).obj U)) t) := by
    intro j k hij hjk t
    unfold compUnit
    exact htransition j k hij hjk t
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · intro j hij t
      have h := ht j j hij le_rfl t
      rw [hfid j, compUnit_id] at h
      exact eq_of_heq h
    · intro j k hij hjk t
      apply eq_of_heq
      refine (hr k (hij.trans hjk) _).trans ((compUnit_comp_heq
        (p k) (f j k hjk) (f i j hij) G
        (f i k (hij.trans hjk)) (hfcomp i j k hij hjk)
        (p j) (hpcomp j k hjk)
        ((Opens.map (f i j hij)).obj U)
        ((Opens.map (f i k (hij.trans hjk))).obj U) ?_
        t _ (ht j k hij hjk t)).trans (hr j hij t).symm)
      exact congrArg (fun a : S k ⟶ S i ↦ (Opens.map a).obj U)
        (hfcomp i j k hij hjk).symm
    · intro j k l hij hjk hkl t
      apply eq_of_heq
      refine (ht k l (hij.trans hjk) hkl _).trans ((compUnit_comp_heq
        (f k l hkl) (f j k hjk) (f i j hij) G
        (f i k (hij.trans hjk)) (hfcomp i j k hij hjk)
        (f j l (hjk.trans hkl)) (hfcomp j k l hjk hkl)
        ((Opens.map (f i j hij)).obj U)
        ((Opens.map (f i k (hij.trans hjk))).obj U) ?_
        t _ (ht j k hij hjk t)).trans (ht j l hij (hjk.trans hkl) t).symm)
      exact congrArg (fun a : S k ⟶ S i ↦ (Opens.map a).obj U)
        (hfcomp i j k hij hjk).symm
  · constructor
    · intro s
      let H := (pullback (Type u) (p i)).obj G
      let : SpectralSpace X := hs.1
      obtain ⟨L, hL, W, V, hWc, hVc, hVU, hWV, hcover, t, htloc⟩ :=
        finite_local_unit_sections (p i) G U
          ((hs.2 i).isCompact_preimage_of_isOpen U.isOpen hU) s
      let : Finite L := hL
      have hdescall := Topology.spectralLimit_descend_opens (fun j ↦ S j)
        (fun j k h ↦ f j k h) hf (fun j x ↦ congrFun (hfid' j) x)
        (fun j k l hjk hkl x ↦ congrFun (hfcomp' j k l hjk hkl) x)
        X (fun j ↦ p j) (fun j ↦ (p j).hom.continuous)
        (fun j k h x ↦ congrFun (hpcomp' j k h) x) hlimit htop
      have hlift : ∀ W : Opens X, IsCompact (W : Set X) →
          ∃ (j : I) (V : Opens (S j)), IsCompact (V : Set (S j)) ∧
            (Opens.map (p j)).obj V = W := by
        intro W hW
        obtain ⟨j, V, hVo, hVc, he⟩ := hdescall.1 W W.isOpen hW
        exact ⟨j, ⟨V, hVo⟩, hVc, Opens.ext he⟩
      obtain ⟨j, hij, T, hTc, hT, hTV, hTcover⟩ := descend_finite_cover S f hf
        (fun j k l hjk hkl x ↦ congrFun (hfcomp' j k l hjk hkl) x)
        X p (fun j k h x ↦ congrFun (hpcomp' j k h) x) hlift
        (fun j k W V hW hV hsub ↦ hd j k W V W.isOpen hW V.isOpen hV hsub)
        i U hU W V hWc hVc hVU hWV hcover
      let F := (pullback (Type u) (f i j hij)).obj G
      let r := compMap (p j) (f i j hij) (p i) (hpcomp i j hij) G
      let v (l : L) : F.obj.obj (op (T l)) :=
        F.obj.map (homOfLE (hTV l)).op
          (((pullbackPushforwardAdjunction (Type u) (f i j hij)).unit.app G).hom.app
            (op (V l)) (t l))
      have hTU' (l : L) : (Opens.map (p j)).obj (T l) ≤ (Opens.map (p i)).obj U := by
        rw [hT l]
        exact (hWV l).trans ((Opens.map (p i)).monotone (hVU l))
      have hTV' (l : L) : (Opens.map (p j)).obj (T l) ≤ (Opens.map (p i)).obj (V l) := by
        rw [hT l]
        exact hWV l
      have hlocal (l : L) : r.hom.app (op (T l)) (v l) =
          H.obj.map (homOfLE (hTU' l)).op s := by
        rw [show r.hom.app (op (T l)) (v l) =
          H.obj.map (homOfLE (hTV' l)).op
            (((pullbackPushforwardAdjunction (Type u) (p i)).unit.app G).hom.app
              (op (V l)) (t l)) from
                compMap_restrict_unit (p j) (f i j hij) (p i) (hpcomp i j hij)
                  G (V l) (T l) (hTV l) (hTV' l) (t l)]
        apply (heq_eq_iff
          (restrict_heq H rfl (hT l) (hTV' l) (hWV l) _ _ HEq.rfl)
          (restrict_heq H rfl (hT l) (hTU' l)
            ((hWV l).trans ((Opens.map (p i)).monotone (hVU l))) _ _ HEq.rfl)).mpr
        exact (htloc l).symm
      have hpair (l m : L) :
          r.hom.app (op (T l ⊓ T m))
              (F.obj.map (Opens.infLELeft (T l) (T m)).op (v l)) =
            r.hom.app (op (T l ⊓ T m))
              (F.obj.map (Opens.infLERight (T l) (T m)).op (v m)) := by
        erw [map_restrict (p j) r (show T l ⊓ T m ≤ T l from inf_le_left) (v l),
          map_restrict (p j) r (show T l ⊓ T m ≤ T m from inf_le_right) (v m)]
        rw [hlocal, hlocal]
        change H.obj.map ((Opens.map (p j)).map (Opens.infLELeft (T l) (T m))).op
            (H.obj.map (homOfLE (hTU' l)).op s) =
          H.obj.map ((Opens.map (p j)).map (Opens.infLERight (T l) (T m))).op
            (H.obj.map (homOfLE (hTU' m)).op s)
        have hmaps : (homOfLE (hTU' l)).op ≫
            ((Opens.map (p j)).map (Opens.infLELeft (T l) (T m))).op =
          (homOfLE (hTU' m)).op ≫
            ((Opens.map (p j)).map (Opens.infLERight (T l) (T m))).op :=
          Subsingleton.elim _ _
        have he := congrArg (fun b ↦ H.obj.map b s) hmaps
        simpa only [H.obj.map_comp, ConcreteCategory.comp_apply] using he
      have hpair' (a : L × L) := hevent j hij (T a.1 ⊓ T a.2)
        ((hTc a.1).inter_of_isOpen (hTc a.2) (T a.1).isOpen (T a.2).isOpen)
        _ _ (hpair a.1 a.2)
      choose k₀ hjk₀ hk₀ using hpair'
      obtain ⟨k, hjk, hkk⟩ := finite_upper_bound k₀ j
      let Fk := (pullback (Type u) (f i k (hij.trans hjk))).obj G
      let a := compMap (f j k hjk) (f i j hij) (f i k (hij.trans hjk))
        (hfcomp i j k hij hjk) G
      let rk := compMap (p k) (f i k (hij.trans hjk)) (p i)
        (hpcomp i k (hij.trans hjk)) G
      let Tk (l : L) := (Opens.map (f j k hjk)).obj (T l)
      let vk (l : L) : Fk.obj.obj (op (Tk l)) := a.hom.app (op (T l)) (v l)
      have hvk : Presheaf.IsCompatible Fk.obj Tk vk := by
        intro l m
        have he := compMap_eq_of_later
          (f (k₀ (l, m)) k (hkk (l, m))) (f j (k₀ (l, m)) (hjk₀ (l, m)))
          (f i j hij) (f i (k₀ (l, m)) (hij.trans (hjk₀ (l, m))))
          (hfcomp i j (k₀ (l, m)) hij (hjk₀ (l, m)))
          (f j k hjk) (hfcomp j (k₀ (l, m)) k (hjk₀ (l, m)) (hkk (l, m)))
          (f i k (hij.trans hjk))
          (hfcomp i (k₀ (l, m)) k _ _) (hfcomp i j k hij hjk) G (T l ⊓ T m)
          _ _ (hk₀ (l, m))
        have hleft := map_restrict (f j k hjk) a
          (show T l ⊓ T m ≤ T l from inf_le_left) (v l)
        have hright := map_restrict (f j k hjk) a
          (show T l ⊓ T m ≤ T m from inf_le_right) (v m)
        change Fk.obj.map (Opens.infLELeft (Tk l) (Tk m)).op
          (a.hom.app (op (T l)) (v l)) =
            Fk.obj.map (Opens.infLERight (Tk l) (Tk m)).op
              (a.hom.app (op (T m)) (v m))
        convert hleft.symm.trans (he.trans hright) using 1 <;> congr 2
      have hTkcover : (⨆ l, Tk l) =
          (Opens.map (f i k (hij.trans hjk))).obj U := by
        apply Opens.ext
        ext x
        rw [Opens.coe_iSup, Set.mem_iUnion]
        change (∃ l, f j k hjk x ∈ T l) ↔ f i k (hij.trans hjk) x ∈ U
        rw [← Opens.mem_iSup, hTcover]
        exact iff_of_eq (congrArg (fun y ↦ y ∈ U) (congrFun (hfcomp' i j k hij hjk) x))
      have hTkU (l : L) : Tk l ≤ (Opens.map (f i k (hij.trans hjk))).obj U :=
        hTkcover ▸ le_iSup Tk l
      obtain ⟨z, hz, _⟩ := Fk.existsUnique_gluing' Tk
        ((Opens.map (f i k (hij.trans hjk))).obj U)
        (fun l ↦ homOfLE (hTkU l)) (le_of_eq hTkcover.symm) vk hvk
      refine ⟨k, hij.trans hjk, z, ?_⟩
      have hrz : HEq (rho k (hij.trans hjk) z)
          (rk.hom.app (op ((Opens.map (f i k (hij.trans hjk))).obj U)) z) :=
        (hr k (hij.trans hjk) z).trans (compMap_heq _ _ _ _ _ _ _).symm
      apply eq_of_heq
      refine hrz.trans ?_
      have hΩ : (Opens.map (p k)).obj
          ((Opens.map (f i k (hij.trans hjk))).obj U) = (Opens.map (p i)).obj U :=
        congrArg (fun b : X ⟶ S i ↦ (Opens.map b).obj U) (hpcomp i k _)
      have himage : rk.hom.app (op ((Opens.map (f i k (hij.trans hjk))).obj U)) z =
          H.obj.map (homOfLE (le_of_eq hΩ)).op s := by
        apply H.eq_of_locally_eq' (fun l ↦ (Opens.map (p k)).obj (Tk l))
          ((Opens.map (p k)).obj ((Opens.map (f i k (hij.trans hjk))).obj U))
          (fun l ↦ homOfLE ((Opens.map (p k)).monotone (hTkU l)))
        · intro x hx
          have hx' : p k x ∈ ⨆ l, Tk l := hTkcover.symm ▸ hx
          obtain ⟨l, hl⟩ := Opens.mem_iSup.mp hx'
          exact Opens.mem_iSup.mpr ⟨l, hl⟩
        · intro l
          erw [← map_restrict (p k) rk (hTkU l) z, hz]
          simp only [← ConcreteCategory.comp_apply, ← H.obj.map_comp]
          have hcomp := compMap_comp (p k) (f j k hjk) (f i j hij)
            (f i k (hij.trans hjk)) (hfcomp i j k hij hjk)
            (p j) (hpcomp j k hjk) (p i) (hpcomp i k (hij.trans hjk))
            (hpcomp i j hij) G (T l) (v l) (Tk l) rfl (vk l) HEq.rfl
          apply (heq_eq_iff hcomp ?_).mpr (hlocal l)
          apply restrict_heq H rfl _ _ (hTU' l) s s HEq.rfl
          exact congrArg (fun b : X ⟶ S j ↦ (Opens.map b).obj (T l)) (hpcomp j k hjk)
      refine (heq_of_eq himage).trans ?_
      exact restrict_eq_heq H hΩ s
    · intro j hij t t' he
      have hr' (a : _) : HEq (rho j hij a)
          ((compMap (p j) (f i j hij) (p i) (hpcomp i j hij) G).hom.app
            (op ((Opens.map (f i j hij)).obj U)) a) :=
        (hr j hij a).trans (compMap_heq _ _ _ _ _ _ _).symm
      have he' := (heq_eq_iff (hr' t) (hr' t')).mp he
      have he'' := (compMap_equal_iff _ _ _ _ _ _ t t').mp he'
      obtain ⟨k, hjk, hk⟩ := eventually_unit_equal S f X p hs.2 hd' j
        ((pullback (Type u) (f i j hij)).obj G)
        ((Opens.map (f i j hij)).obj U)
        ((hf i j hij).isCompact_preimage_of_isOpen U.isOpen hU) t t' he''
      refine ⟨k, hjk, ?_⟩
      have ht' (a : _) : HEq (transition j k hij hjk a)
          ((compMap (f j k hjk) (f i j hij) (f i k (hij.trans hjk))
            (hfcomp i j k hij hjk) G).hom.app
              (op ((Opens.map (f i j hij)).obj U)) a) :=
        (ht j k hij hjk a).trans (compMap_heq _ _ _ _ _ _ _).symm
      exact (heq_eq_iff (ht' t) (ht' t')).mpr
        ((compMap_equal_iff _ _ _ _ _ _ t t').mpr hk)

end TopCat.Sheaf
