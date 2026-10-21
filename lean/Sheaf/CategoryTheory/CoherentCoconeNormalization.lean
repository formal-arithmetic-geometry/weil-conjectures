module

public import Sheaf.CategoryTheory.FilteredTwoColimitModel
public import Mathlib.CategoryTheory.Whiskering

/-! # Normalization of a unital coherent cocone

Source: blueprint main-20261015, filtered 2-colimit model, normalization and compatibility;
auxiliary agent normalization calculation
(blueprint: lem-weil-pbc-coherent-cocone-normalization).
-/

@[expose] public section

universe w u v u' v'

namespace CategoryTheory

/-- A unital coherent cocone can be normalized without changing its finite-stage conditions.
Source: blueprint main-20261015, filtered 2-colimit model, coherence hypotheses; auxiliary
agent normalization lemma (blueprint: lem-weil-pbc-coherent-cocone-normalization).

Proof plan (the node's ten steps):
1. Replace diagonal transitions by identity functors and keep all other transitions and Φ.
   On the diagonal put β = ε⁻¹; off the diagonal put β = id. Transport θ by Φ(β).
2. Put B_ijk = (T_jk β_ij)(β_jk T'_ij), and τ'_ijk = β_ik⁻¹ τ_ijk B_ijk.
   Whiskering, composition and inversion preserve natural isomorphisms.
3. Expand the first pentagon composite. Naturality of β_kl identifies its composite with
   β_il with τ_ikl(T_kl τ_ijk)B_ijkl, where B_ijkl is the threefold β comparison.
4. Expand the other composite. Naturality of τ_jkl identifies its composite with β_il
   with τ_ijl(τ_jkl T_ij)B_ijkl. Apply the given pentagon and cancel β_il.
5. The first unit equation cancels T_ij(ε_i) against T_ij(ε_i⁻¹), giving τ'_iij = id.
6. Naturality of ε_j on β_ij and cancellation give τ'_ijj = id, also on the full diagonal.
7. Naturality of θ_jk on β_ij gives the transported cocone compatibility. The diagonal
   equation θ_ii = Φ_i(ε_i) cancels Φ_i(ε_i⁻¹), giving θ'_ii = id. These are exactly the
   hypotheses of det-def-sfb-filtered-two-colimit-model.
8. Conjugation sends g to β_jk⁻¹ g β_ik, with inverse h ↦ β_jk h β_ik⁻¹. Substitution
   into the comparison-functor formula cancels the β components, leaving its image unchanged.
9. Obj uses the unchanged Φ. The bijection in step 8 transports Hom-surj witnesses both ways.
10. Naturality of β_kl identifies equality of T_kl(g), T_kl(g') with equality of their
    normalized images. The same later indices witness Hom-inj in both directions.
The cocone and three conditions are those of det-def-sfb-filtered-two-colimit-cocone and
 det-def-sfb-filtered-two-colimit-conditions. -/
theorem coherent_cocone_normalization
    {I : Type w} [PartialOrder I] [IsDirected I (· ≤ ·)]
    {C : I → Type u} [∀ i, Category.{v} (C i)] {D : Type u'} [Category.{v'} D]
    (c : CategoryCocone C D)
    (ε : ∀ i : I, c.T (le_refl i) ≅ 𝟭 (C i))
    (τ : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k),
      c.T hij ⋙ c.T hjk ≅ c.T (hij.trans hjk))
    (pentagon : ∀ {i j k l : I} (hij : i ≤ j) (hjk : j ≤ k) (hkl : k ≤ l)
      (x : C i),
      (c.T hkl).map ((τ hij hjk).hom.app x) ≫
          (τ (hij.trans hjk) hkl).hom.app x =
        (τ hjk hkl).hom.app ((c.T hij).obj x) ≫
          (τ hij (hjk.trans hkl)).hom.app x)
    (unit_left : ∀ {i j : I} (h : i ≤ j) (x : C i),
      (τ (le_refl i) h).hom.app x = (c.T h).map ((ε i).hom.app x))
    (unit_right : ∀ {i j : I} (h : i ≤ j) (x : C i),
      (τ h (le_refl j)).hom.app x = (ε j).hom.app ((c.T h).obj x))
    (compatibility : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) (x : C i),
      (c.Φ k).map ((τ hij hjk).hom.app x) ≫
          (c.iso (hij.trans hjk)).hom.app x =
        (c.iso hjk).hom.app ((c.T hij).obj x) ≫ (c.iso hij).hom.app x)
    (cocone_unit : ∀ (i : I) (x : C i),
      (c.iso (le_refl i)).hom.app x = (c.Φ i).map ((ε i).hom.app x)) :
    ∃ (n : CoherentCategoryCocone (C := C) (D := D))
      (β : ∀ {i j : I} (h : i ≤ j), n.T h ≅ c.T h),
      n.Φ = c.Φ ∧
      (∀ i : I, HEq (β (le_refl i)) (ε i).symm) ∧
      (∀ {i j : I} (h : i ≤ j), i ≠ j →
        n.T h = c.T h ∧ HEq (β h) (Iso.refl (c.T h))) ∧
      (∀ {i j : I} (h : i ≤ j),
        HEq (n.iso h) (Functor.isoWhiskerRight (β h) (c.Φ j) ≪≫ c.iso h)) ∧
      (∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k),
        n.tau hij hjk =
          Functor.isoWhiskerLeft (n.T hij) (β hjk) ≪≫
            Functor.isoWhiskerRight (β hij) (c.T hjk) ≪≫ τ hij hjk ≪≫
              (β (hij.trans hjk)).symm) ∧
      (c.EssSurjObj ↔ n.toCategoryCocone.EssSurjObj) ∧
      (c.HomSurj ↔ n.toCategoryCocone.HomSurj) ∧
      (c.HomInj ↔ n.toCategoryCocone.HomInj) ∧
      (∀ {i j k : I} (hik : i ≤ k) (hjk : j ≤ k) (x : C i) (y : C j)
        (g : (c.T hik).obj x ⟶ (c.T hjk).obj y),
        HEq
          ((n.iso hik).inv.app x ≫
            (n.Φ k).map ((β hik).hom.app x ≫ g ≫ (β hjk).inv.app y) ≫
              (n.iso hjk).hom.app y)
          ((c.iso hik).inv.app x ≫ (c.Φ k).map g ≫ (c.iso hjk).hom.app y)) := by
  classical
  -- Replace only diagonal transitions; beta identifies the replacement with the old data.
  let data : ∀ {i j : I} (h : i ≤ j), Σ F : C i ⥤ C j, F ≅ c.T h :=
    fun {i j} h ↦ if e : i = j then by
      subst j
      exact ⟨𝟭 (C i), (ε i).symm⟩
    else ⟨c.T h, Iso.refl _⟩
  let T : ∀ {i j : I}, i ≤ j → C i ⥤ C j := fun h ↦ (data h).1
  let β : ∀ {i j : I} (h : i ≤ j), T h ≅ c.T h := fun h ↦ (data h).2
  let t : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k),
      T hij ⋙ T hjk ≅ T (hij.trans hjk) := fun hij hjk ↦
    Functor.isoWhiskerLeft (T hij) (β hjk) ≪≫
      Functor.isoWhiskerRight (β hij) (c.T hjk) ≪≫ τ hij hjk ≪≫
        (β (hij.trans hjk)).symm
  let θ : ∀ {i j : I} (h : i ≤ j), T h ⋙ c.Φ j ≅ c.Φ i := fun h ↦
    Functor.isoWhiskerRight (β h) (c.Φ _) ≪≫ c.iso h
  -- The transport equation lets us check coherence without expanding inverse components.
  have ht {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) (x : C i) :
      (t hij hjk).hom.app x ≫ (β (hij.trans hjk)).hom.app x =
        (β hjk).hom.app ((T hij).obj x) ≫
          (c.T hjk).map ((β hij).hom.app x) ≫ (τ hij hjk).hom.app x := by
    simp [t, Category.assoc]
  have hp {i j k l : I} (hij : i ≤ j) (hjk : j ≤ k) (hkl : k ≤ l)
      (x : C i) :
      (T hkl).map ((t hij hjk).hom.app x) ≫
          (t (hij.trans hjk) hkl).hom.app x =
        (t hjk hkl).hom.app ((T hij).obj x) ≫
          (t hij (hjk.trans hkl)).hom.app x := by
    apply (cancel_mono ((β ((hij.trans hjk).trans hkl)).hom.app x)).1
    simp only [Category.assoc, ht]
    rw [← Category.assoc, (β hkl).hom.naturality]
    simp only [Category.assoc]
    rw [← Functor.map_comp_assoc, ht]
    simp only [Functor.map_comp, Category.assoc]
    rw [pentagon]
    rw [← Category.assoc ((t hjk hkl).hom.app ((T hij).obj x)), ht]
    simp only [Category.assoc]
    have hn := (τ hjk hkl).hom.naturality_assoc ((β hij).hom.app x)
      ((τ hij (hjk.trans hkl)).hom.app x)
    dsimp only [Functor.comp_map] at hn
    rw [← hn]
    rfl
  -- Unit equations include the fully diagonal case.
  have hTi (i : I) : T (le_refl i) = 𝟭 (C i) := by simp [T, data]
  have hβi (i : I) : HEq (β (le_refl i)) (ε i).symm := by
    have hd : data (le_refl i) = ⟨𝟭 (C i), (ε i).symm⟩ := by simp [data]
    change HEq (data (le_refl i)).2 (ε i).symm
    generalize data (le_refl i) = d at hd ⊢
    cases hd
    rfl
  have hθi (i : I) : HEq (θ (le_refl i)) (Iso.refl (c.Φ i)) := by
    have aux (F : C i ⥤ C i) (b : F ≅ c.T (le_refl i))
        (hF : F = 𝟭 (C i)) (hb : HEq b (ε i).symm) :
        HEq (Functor.isoWhiskerRight b (c.Φ i) ≪≫ c.iso (le_refl i))
          (Iso.refl (c.Φ i)) := by
      subst F
      rw [eq_of_heq hb]
      apply heq_of_eq
      apply Iso.ext
      ext x
      simp [cocone_unit, ← Functor.map_comp]
    exact aux _ _ (hTi i) (hβi i)
  have htl {i j : I} (h : i ≤ j) : HEq (t (le_refl i) h) (Iso.refl (T h)) := by
    have aux (F : C i ⥤ C i) (b : F ≅ c.T (le_refl i))
        (hF : F = 𝟭 (C i)) (hb : HEq b (ε i).symm) :
        HEq (Functor.isoWhiskerLeft F (β h) ≪≫
          Functor.isoWhiskerRight b (c.T h) ≪≫ τ (le_refl i) h ≪≫ (β h).symm)
          (Iso.refl (T h)) := by
      subst F
      rw [eq_of_heq hb]
      apply heq_of_eq
      apply Iso.ext
      ext x
      suffices (T h).map ((ε i).inv.app x) ≫
          (T h).map ((ε i).hom.app x) = 𝟙 _ by
        simpa [unit_left] using this
      rw [← Functor.map_comp]
      simp
    exact aux _ _ (hTi i) (hβi i)
  have htr {i j : I} (h : i ≤ j) : HEq (t h (le_refl j)) (Iso.refl (T h)) := by
    have aux (F : C j ⥤ C j) (b : F ≅ c.T (le_refl j))
        (hF : F = 𝟭 (C j)) (hb : HEq b (ε j).symm) :
        HEq (Functor.isoWhiskerLeft (T h) b ≪≫
          Functor.isoWhiskerRight (β h) (c.T (le_refl j)) ≪≫
            τ h (le_refl j) ≪≫ (β h).symm) (Iso.refl (T h)) := by
      subst F
      rw [eq_of_heq hb]
      apply heq_of_eq
      apply Iso.ext
      ext x
      simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
        Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
        Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, unit_right]
      rw [(ε j).hom.naturality_assoc]
      simp
    exact aux _ _ (hTi j) (hβi j)
  have hc {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) (x : C i) :
      (θ (hij.trans hjk)).hom.app x =
        (c.Φ k).map ((t hij hjk).inv.app x) ≫
          (θ hjk).hom.app ((T hij).obj x) ≫ (θ hij).hom.app x := by
    have h : (c.Φ k).map ((t hij hjk).hom.app x) ≫
        (θ (hij.trans hjk)).hom.app x =
          (θ hjk).hom.app ((T hij).obj x) ≫ (θ hij).hom.app x := by
      dsimp only [θ, Iso.trans_hom, NatTrans.comp_app,
        Functor.isoWhiskerRight_hom, Functor.whiskerRight_app]
      rw [← Functor.map_comp_assoc, ht]
      simp only [Functor.map_comp, Category.assoc]
      rw [compatibility]
      rw [← (c.iso hjk).hom.naturality_assoc]
      rfl
    rw [← h]
    simp [← Functor.map_comp_assoc]
  let n : CoherentCategoryCocone (C := C) (D := D) :=
    { T := T
      Φ := c.Φ
      iso := θ
      tau := t
      transition_identity := hTi
      cocone_identity := hθi
      tau_identity_left := htl
      tau_identity_right := htr
      tau_cocycle := hp
      compatibility := hc }
  -- Conjugation of a finite-stage arrow leaves its comparison image unchanged.
  have image {i j k : I} (hik : i ≤ k) (hjk : j ≤ k) (x : C i) (y : C j)
      (g : (c.T hik).obj x ⟶ (c.T hjk).obj y) :
      (θ hik).inv.app x ≫
          (c.Φ k).map ((β hik).hom.app x ≫ g ≫ (β hjk).inv.app y) ≫
            (θ hjk).hom.app y =
        (c.iso hik).inv.app x ≫ (c.Φ k).map g ≫ (c.iso hjk).hom.app y := by
    dsimp [θ]
    simp only [Functor.map_comp, Category.assoc]
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Iso.inv_hom_id_app_assoc,
      Functor.map_id, Category.id_comp]
  refine ⟨n, β, rfl, hβi, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j h e
    change (data h).1 = c.T h ∧ HEq (data h).2 (Iso.refl (c.T h))
    have hd : data h = ⟨c.T h, Iso.refl (c.T h)⟩ := by simp [data, e]
    generalize data h = d at hd ⊢
    cases hd
    exact ⟨rfl, HEq.rfl⟩
  · intro i j h
    rfl
  · intro i j k hij hjk
    rfl
  · rfl
  · constructor
    · intro h i j x y f
      obtain ⟨k, hi, hj, g, hg⟩ := h i j x y f
      refine ⟨k, hi, hj, (β hi).hom.app x ≫ g ≫ (β hj).inv.app y, ?_⟩
      exact hg.trans (image hi hj x y g).symm
    · intro h i j x y f
      obtain ⟨k, hi, hj, g, hg⟩ := h i j x y f
      refine ⟨k, hi, hj, (β hi).inv.app x ≫ g ≫ (β hj).hom.app y, ?_⟩
      rw [hg, ← image hi hj x y]
      simp [n, Category.assoc]
  · have maps {k l : I} (h : k ≤ l) (x y : C k) (g : x ⟶ y) :
        (T h).map g = (β h).hom.app x ≫ (c.T h).map g ≫ (β h).inv.app y := by
      rw [← (β h).hom.naturality_assoc]
      simp
    constructor
    · intro h k x y g g' hg
      obtain ⟨l, hl, he⟩ := h k x y g g' hg
      exact ⟨l, hl, by change (T hl).map g = (T hl).map g'; rw [maps, maps, he]⟩
    · intro h k x y g g' hg
      obtain ⟨l, hl, he⟩ := h k x y g g' hg
      change (T hl).map g = (T hl).map g' at he
      rw [maps, maps] at he
      exact ⟨l, hl, (cancel_mono _).1 ((cancel_epi _).1 he)⟩
  · intro i j k hik hjk x y g
    exact heq_of_eq (image hik hjk x y g)

end CategoryTheory
