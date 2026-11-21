/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Finite
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Basic.Finite.Sigma

/-!
# Finite initial truncation of the simplicial indexing category

`S.Elements` is the opposite of the category of simplices: a morphism
`(n,s) ⟶ (m,t)` lies over `[m] ⟶ [n]` and satisfies `S(φ)(s) = t`.
The degree predicate selects the full subcategory directly, without a new definition.

## References

* Stacks Project, Tag 017K, proof, and Tag 002R
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace SSet

private lemma simultaneous_repeat {k n n' : ℕ} (m : ℕ)
    (hn : n ≤ m) (hn' : n' ≤ m) (hk : 2 * m < k + 1)
    (f : ⦋k + 1⦌ ⟶ ⦋n⦌) (g : ⦋k + 1⦌ ⟶ ⦋n'⦌) :
    ∃ i : Fin (k + 1),
      f.toOrderHom i.castSucc = f.toOrderHom i.succ ∧
      g.toOrderHom i.castSucc = g.toOrderHom i.succ := by
  by_contra h
  have hstep (i : Fin (k + 1)) :
      (f.toOrderHom i.castSucc).val + (g.toOrderHom i.castSucc).val <
        (f.toOrderHom i.succ).val + (g.toOrderHom i.succ).val := by
    have hf := f.toOrderHom.monotone (Fin.castSucc_le_succ i)
    have hg := g.toOrderHom.monotone (Fin.castSucc_le_succ i)
    have hne : ¬ (f.toOrderHom i.castSucc = f.toOrderHom i.succ ∧
        g.toOrderHom i.castSucc = g.toOrderHom i.succ) := fun hi ↦ h ⟨i, hi⟩
    simp only [Fin.le_iff_val_le_val] at hf hg
    have hne' : ¬ ((f.toOrderHom i.castSucc).val = (f.toOrderHom i.succ).val ∧
        (g.toOrderHom i.castSucc).val = (g.toOrderHom i.succ).val) := by
      simpa only [Fin.ext_iff] using hne
    omega
  have hbound (i : Fin (k + 2)) :
      i.val ≤ (f.toOrderHom i).val + (g.toOrderHom i).val := by
    induction i using Fin.induction with
    | zero => exact Nat.zero_le _
    | succ i hi =>
        have := hstep i
        simp only [Fin.val_succ, Fin.val_castSucc] at *
        omega
  have := hbound (Fin.last (k + 1))
  have hf := (f.toOrderHom (Fin.last (k + 1))).isLt
  have hg := (g.toOrderHom (Fin.last (k + 1))).isLt
  simp only [Fin.val_last] at this
  omega

private lemma common_factor (S : SSet.{u}) (m : ℕ) {k n n' : ℕ}
    (hn : n ≤ m) (hn' : n' ≤ m) (x : S.obj (op ⦋n⦌))
    (x' : S.obj (op ⦋n'⦌)) (f : ⦋k⦌ ⟶ ⦋n⦌) (g : ⦋k⦌ ⟶ ⦋n'⦌)
    (h : S.map f.op x = S.map g.op x') :
    ∃ (l : ℕ) (_ : l ≤ 2 * m) (t : ⦋k⦌ ⟶ ⦋l⦌)
      (p : ⦋l⦌ ⟶ ⦋n⦌) (q : ⦋l⦌ ⟶ ⦋n'⦌),
      f = t ≫ p ∧ g = t ≫ q ∧ S.map p.op x = S.map q.op x' := by
  induction k with
  | zero => exact ⟨0, by omega, 𝟙 _, f, g, by simp, by simp, h⟩
  | succ k ih =>
      by_cases hk : k + 1 ≤ 2 * m
      · exact ⟨k + 1, hk, 𝟙 _, f, g, by simp, by simp, h⟩
      obtain ⟨i, hi, hi'⟩ := simultaneous_repeat m hn hn' (by omega) f g
      obtain ⟨f₁, hf⟩ := SimplexCategory.eq_σ_comp_of_not_injective' f i hi
      obtain ⟨g₁, hg⟩ := SimplexCategory.eq_σ_comp_of_not_injective' g i hi'
      have hinj : Function.Injective (S.map (SimplexCategory.σ i).op) := by
        apply Function.LeftInverse.injective
          (g := S.map (SimplexCategory.δ i.castSucc).op)
        intro a
        simp only [← Functor.map_comp_apply, ← op_comp,
          SimplexCategory.δ_comp_σ_self, op_id, Functor.map_id_apply]
      have h₁ : S.map f₁.op x = S.map g₁.op x' := by
        apply hinj
        simpa only [hf, hg, op_comp, Functor.map_comp_apply] using h
      obtain ⟨l, hl, t, p, q, hp, hq, hpq⟩ := ih f₁ g₁ h₁
      exact ⟨l, hl, SimplexCategory.σ i ≫ t, p, q,
        by rw [hf, hp, Category.assoc], by rw [hg, hq, Category.assoc], hpq⟩

private lemma bounded_ancestor (S : SSet.{u}) (m : ℕ)
    (hdegenerate : ∀ n : ℕ, m < n → ∀ s : S.obj (op ⦋n⦌),
      s ∈ S.degenerate n) (z : S.Elements) :
    ∃ y : S.Elements, y.obj.unop.len ≤ m ∧ Nonempty (y ⟶ z) := by
  rcases z with @⟨⟨⟨k⟩⟩, s⟩
  obtain ⟨n, f, _, x, hx⟩ := S.exists_nonDegenerate s
  have hn : n ≤ m := by
    by_contra h
    exact x.property (hdegenerate n (by omega) x.val)
  exact ⟨S.elementsMk (op ⦋n⦌) x.val, hn, ⟨⟨f.op, hx.symm⟩⟩⟩

private lemma common_ancestor (S : SSet.{u}) (m : ℕ)
    (x x' z : S.Elements) (hx : x.obj.unop.len ≤ m)
    (hx' : x'.obj.unop.len ≤ m) (f : x ⟶ z) (g : x' ⟶ z) :
    ∃ (a : S.Elements) (_ : a.obj.unop.len ≤ 2 * m) (t : a ⟶ z)
      (p : x ⟶ a) (q : x' ⟶ a), p ≫ t = f ∧ q ≫ t = g := by
  rcases x with @⟨⟨⟨n⟩⟩, x⟩
  rcases x' with @⟨⟨⟨n'⟩⟩, x'⟩
  rcases z with @⟨⟨⟨k⟩⟩, z⟩
  obtain ⟨l, hl, t, p, q, hp, hq, hpq⟩ :=
    common_factor S m hx hx' x x' f.hom.unop g.hom.unop
      (f.map_val.trans g.map_val.symm)
  let a : S.Elements := S.elementsMk (op ⦋l⦌) (S.map p.op x)
  have ht : S.map t.op a.val = z := by
    change S.map t.op (S.map p.op x) = z
    rw [← Functor.map_comp_apply, ← op_comp, ← hp]
    exact f.map_val
  refine ⟨a, hl, ⟨t.op, ht⟩, ⟨p.op, rfl⟩, ⟨q.op, hpq.symm⟩, ?_, ?_⟩
  · apply Functor.Elements.hom_ext
    change p.op ≫ t.op = f.hom
    rw [← op_comp, ← hp]
    rfl
  · apply Functor.Elements.hom_ext
    change q.op ≫ t.op = g.hom
    rw [← op_comp, ← hq]
    rfl

private lemma four_step (S : SSet.{u}) (m : ℕ)
    (hdegenerate : ∀ n : ℕ, m < n → ∀ s : S.obj (op ⦋n⦌),
      s ∈ S.degenerate n) (z : S.Elements)
    (y y' : ObjectProperty.FullSubcategory
      (fun x : S.Elements ↦ x.obj.unop.len ≤ 2 * m))
    (α : y.obj ⟶ z) (α' : y'.obj ⟶ z) :
    ∃ (u a u' : ObjectProperty.FullSubcategory
      (fun x : S.Elements ↦ x.obj.unop.len ≤ 2 * m))
      (β : u.obj ⟶ y.obj) (p : u.obj ⟶ a.obj) (q : u'.obj ⟶ a.obj)
      (β' : u'.obj ⟶ y'.obj) (t : a.obj ⟶ z),
      p ≫ t = β ≫ α ∧ q ≫ t = β' ≫ α' := by
  obtain ⟨u, hu, ⟨β⟩⟩ := bounded_ancestor S m hdegenerate y.obj
  obtain ⟨u', hu', ⟨β'⟩⟩ := bounded_ancestor S m hdegenerate y'.obj
  obtain ⟨a, ha, t, p, q, hp, hq⟩ :=
    common_ancestor S m u u' z hu hu' (β ≫ α) (β' ≫ α')
  exact ⟨⟨u, by omega⟩, ⟨a, ha⟩, ⟨u', by omega⟩, β, p, q, β', t, hp, hq⟩

/-- If `S` has finite nonempty levels and all simplices above degree `m₀` are degenerate, then the
full subcategory of `S.Elements` on objects of degree at most `2 * m₀` is finite with finite
hom sets, satisfies the zigzag connectedness conditions below, is initial in `S.Elements`, and
hence restriction along it preserves and detects limits and the comparison map is an
isomorphism. -/
theorem simplicialIndex_finite_initial (S : SSet.{u}) [S.Finite]
    (hfinite : ∀ n : ℕ, Finite (S.obj (op ⦋n⦌)))
    (hnonempty : ∀ n : ℕ, Nonempty (S.obj (op ⦋n⦌)))
    (m₀ : ℕ) (hdegenerate : ∀ n : ℕ, m₀ < n → ∀ s : S.obj (op ⦋n⦌),
      s ∈ S.degenerate n) :
    Finite (ObjectProperty.FullSubcategory
      (fun x : S.Elements => x.obj.unop.len ≤ 2 * m₀)) ∧
    (∀ y y' : (ObjectProperty.FullSubcategory
      (fun x : S.Elements => x.obj.unop.len ≤ 2 * m₀)), Finite (y ⟶ y')) ∧
    (∀ z : S.Elements, ∃ y : (ObjectProperty.FullSubcategory
      (fun x : S.Elements => x.obj.unop.len ≤ 2 * m₀)), Nonempty (y.obj ⟶ z)) ∧
    (∀ (z : S.Elements) (y y' : (ObjectProperty.FullSubcategory
      (fun x : S.Elements => x.obj.unop.len ≤ 2 * m₀)))
      (α : y.obj ⟶ z) (α' : y'.obj ⟶ z),
      ∃ (r : ℕ) (ys : ℕ → (ObjectProperty.FullSubcategory
      (fun x : S.Elements => x.obj.unop.len ≤ 2 * m₀))) (a : ∀ i : ℕ, (ys i).obj ⟶ z),
        ys 0 = y ∧ ys (2 * r) = y' ∧ HEq (a 0) α ∧ HEq (a (2 * r)) α' ∧
        ∀ i : ℕ, i < r →
          ∃ (f : (ys (2 * i + 1)).obj ⟶ (ys (2 * i)).obj)
            (g : (ys (2 * i + 1)).obj ⟶ (ys (2 * i + 2)).obj),
            f ≫ a (2 * i) = a (2 * i + 1) ∧
            g ≫ a (2 * i + 2) = a (2 * i + 1)) ∧
    (ObjectProperty.ι
      (fun x : S.Elements => x.obj.unop.len ≤ 2 * m₀)).Initial ∧
    (∀ (C : Type v) [Category.{w} C] (D : S.Elements ⥤ C),
      HasLimit D ↔ HasLimit ((ObjectProperty.ι
      (fun x : S.Elements => x.obj.unop.len ≤ 2 * m₀)) ⋙ D)) ∧
    (∀ (C : Type v) [Category.{w} C] (D : S.Elements ⥤ C)
      [HasLimit D] [HasLimit ((ObjectProperty.ι
      (fun x : S.Elements => x.obj.unop.len ≤ 2 * m₀)) ⋙ D)],
      IsIso (limit.pre D (ObjectProperty.ι
      (fun x : S.Elements => x.obj.unop.len ≤ 2 * m₀)))) := by
  classical
  obtain ⟨_⟩ := hnonempty 0
  let P : ObjectProperty S.Elements := fun x ↦ x.obj.unop.len ≤ 2 * m₀
  have hobjects : Finite P.FullSubcategory := by
    let F : (Σ n : Fin (2 * m₀ + 1), S.obj (op ⦋n.val⦌)) → P.FullSubcategory :=
      fun ⟨n, s⟩ ↦ ⟨S.elementsMk (op ⦋n.val⦌) s, by change n.val ≤ 2 * m₀; omega⟩
    apply Finite.of_surjective F
    rintro ⟨@⟨⟨⟨n⟩⟩, s⟩, hn⟩
    exact ⟨⟨⟨n, by change n ≤ 2 * m₀ at hn; omega⟩, s⟩, rfl⟩
  have hhoms (y y' : P.FullSubcategory) : Finite (y ⟶ y') := by
    apply Finite.of_injective (fun f : y ⟶ y' ↦ f.hom.hom.unop)
    intro f g h
    apply ObjectProperty.hom_ext
    apply Functor.Elements.hom_ext
    exact Quiver.Hom.unop_inj h
  have hreach (z : S.Elements) : ∃ y : P.FullSubcategory, Nonempty (y.obj ⟶ z) := by
    obtain ⟨y, hy, f⟩ := bounded_ancestor S m₀ hdegenerate z
    exact ⟨⟨y, by change y.obj.unop.len ≤ 2 * m₀; omega⟩, f⟩
  have hzig (z : S.Elements) (y y' : P.FullSubcategory)
      (α : y.obj ⟶ z) (α' : y'.obj ⟶ z) :
      ∃ (r : ℕ) (ys : ℕ → P.FullSubcategory) (a : ∀ i, (ys i).obj ⟶ z),
        ys 0 = y ∧ ys (2 * r) = y' ∧ HEq (a 0) α ∧ HEq (a (2 * r)) α' ∧
        ∀ i : ℕ, i < r →
          ∃ (f : (ys (2 * i + 1)).obj ⟶ (ys (2 * i)).obj)
            (g : (ys (2 * i + 1)).obj ⟶ (ys (2 * i + 2)).obj),
            f ≫ a (2 * i) = a (2 * i + 1) ∧
            g ≫ a (2 * i + 2) = a (2 * i + 1) := by
    obtain ⟨u, b, u', β, p, q, β', t, hp, hq⟩ :=
      four_step S m₀ hdegenerate z y y' α α'
    let ys : ℕ → P.FullSubcategory
      | 0 => y
      | 1 => u
      | 2 => b
      | 3 => u'
      | _ + 4 => y'
    let a : ∀ i, (ys i).obj ⟶ z
      | 0 => α
      | 1 => β ≫ α
      | 2 => t
      | 3 => β' ≫ α'
      | _ + 4 => α'
    refine ⟨2, ys, a, rfl, rfl, HEq.rfl, HEq.rfl, ?_⟩
    intro i hi
    have hi : i = 0 ∨ i = 1 := by omega
    rcases hi with rfl | rfl
    · exact ⟨β, p, rfl, hp⟩
    · exact ⟨q, β', hq, rfl⟩
  have hinitial : P.ι.Initial := by
    constructor
    intro z
    obtain ⟨y, ⟨α⟩⟩ := hreach z
    have : Nonempty (CostructuredArrow P.ι z) := ⟨CostructuredArrow.mk α⟩
    apply zigzag_isConnected
    intro c c'
    obtain ⟨u, b, u', β, p, q, β', t, hp, hq⟩ :=
      four_step S m₀ hdegenerate z c.left c'.left c.hom c'.hom
    let cu : CostructuredArrow P.ι z := CostructuredArrow.mk (β ≫ c.hom)
    let cb : CostructuredArrow P.ι z := CostructuredArrow.mk t
    let cu' : CostructuredArrow P.ι z := CostructuredArrow.mk (β' ≫ c'.hom)
    have f : cu ⟶ c := CostructuredArrow.homMk (ObjectProperty.homMk β) rfl
    have g : cu ⟶ cb := CostructuredArrow.homMk (ObjectProperty.homMk p) hp
    have f' : cu' ⟶ cb := CostructuredArrow.homMk (ObjectProperty.homMk q) hq
    have g' : cu' ⟶ c' := CostructuredArrow.homMk (ObjectProperty.homMk β') rfl
    exact (Zigzag.of_inv_hom f g).trans (Zigzag.of_inv_hom f' g')
  refine ⟨hobjects, hhoms, hreach, hzig, hinitial, ?_, ?_⟩
  · intro C _ D
    exact (Functor.Initial.hasLimit_comp_iff P.ι (G := D)).symm
  · intro C _ D _ _
    exact Functor.Initial.limit_pre_isIso P.ι (G := D)

end SSet
