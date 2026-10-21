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
  sorry

end CategoryTheory
