/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q75
-/
module

public import Sheaf.AlgebraicTopology.AugmentedPosetChains
public import Sheaf.AlgebraicTopology.AugmentedPosetChainPrism
public import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.Abel
import Mathlib.Data.Fintype.Pi

/-! # Explicit contraction of a non-Boolean proper product interval

Source: the agent-written combinatorial extraction below paragraph (3) of
`latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`'s direct-images proof,
steps 1–4 of the node (blueprint: lem-sfb-product-interval-nullhomotopy).
The blueprint paragraph provides context only; this combinatorial assertion is not in it.
The prism input is the augmented strict-poset adaptation of Stacks Tag 019S.

The proper interval is Mathlib's `Set.Ioo 0 m` in the coordinatewise ordered product:
its elements are precisely the vectors bounded by m, other than zero and m.
The chain complex and prism operators are the recorded dependency constructions.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicTopology.AugmentedPosetChains.ProductInterval

/-- The unit vector belongs to the proper interval; coordinatewise maximum stays
in that interval, is monotone, and dominates both the identity and the unit vector.
Source: node proof step 1, agent-written extraction below direct-images paragraph (3)
(blueprint: lem-sfb-product-interval-nullhomotopy).

Proof: the j coordinate of e is 1, with 0 < 1 < m_j, and all others are zero.
For u(x), all coordinates remain bounded, and its j coordinate is positive.
If u(x) = m, then max(x_j,1) = m_j >= 2 forces x_j = m_j; the other
coordinates are unchanged, contradicting x != m. Maximum is monotone in x_j;
in each coordinate x <= u(x) and e <= u(x). -/
theorem coordinate_laws {r : ℕ} (hr : 1 ≤ r) (m : Fin r → ℕ)
    (j : Fin r) (hj : 2 ≤ m j) :
    Function.update (0 : Fin r → ℕ) j 1 ∈ Set.Ioo (0 : Fin r → ℕ) m ∧
      (∀ x : Set.Ioo (0 : Fin r → ℕ) m,
        Function.update x.val j (max (x.val j) 1) ∈ Set.Ioo (0 : Fin r → ℕ) m) ∧
      (∀ x y : Set.Ioo (0 : Fin r → ℕ) m, x ≤ y →
        Function.update x.val j (max (x.val j) 1) ≤
          Function.update y.val j (max (y.val j) 1)) ∧
      (∀ x : Set.Ioo (0 : Fin r → ℕ) m,
        x.val ≤ Function.update x.val j (max (x.val j) 1)) ∧
      (∀ x : Set.Ioo (0 : Fin r → ℕ) m,
        Function.update (0 : Fin r → ℕ) j 1 ≤
          Function.update x.val j (max (x.val j) 1)) := by
  classical
  by_cases hr0 : r = 0
  · subst r
    omega
  have hraise (x : Fin r → ℕ) : x ≤ Function.update x j (max (x j) 1) := by
    intro i
    by_cases hi : i = j
    · subst i
      simp
    · simp [Function.update_of_ne hi]
  have hunit (x : Fin r → ℕ) :
      Function.update (0 : Fin r → ℕ) j 1 ≤ Function.update x j (max (x j) 1) := by
    intro i
    by_cases hi : i = j
    · subst i
      simp
    · simp [Function.update_of_ne hi]
  have he : Function.update (0 : Fin r → ℕ) j 1 ∈ Set.Ioo (0 : Fin r → ℕ) m := by
    constructor
    · apply lt_iff_le_not_ge.mpr
      refine ⟨fun i ↦ Nat.zero_le _, ?_⟩
      intro h
      have := h j
      simp at this
    · apply lt_iff_le_not_ge.mpr
      constructor
      · intro i
        by_cases hi : i = j
        · subst i
          simpa using (show 1 ≤ m j by omega)
        · simp [Function.update_of_ne hi]
      · intro h
        have := h j
        simp only [Function.update_self] at this
        omega
  refine ⟨he, ?_, ?_, ?_, ?_⟩
  · intro x
    constructor
    · exact lt_of_lt_of_le x.property.1 (hraise x.val)
    · apply lt_iff_le_not_ge.mpr
      constructor
      · intro i
        by_cases hi : i = j
        · subst i
          simpa using max_le (x.property.2.le j) (show 1 ≤ m j by omega)
        · simpa [Function.update_of_ne hi] using x.property.2.le i
      · intro h
        apply (not_le_of_gt x.property.2)
        intro i
        by_cases hi : i = j
        · subst i
          have hji := h j
          simp only [Function.update_self] at hji
          have hx := x.property.2.le j
          change m j ≤ x.val j
          omega
        · simpa [Function.update_of_ne hi] using h i
  · intro x y h i
    by_cases hi : i = j
    · subst i
      simpa using max_le_max (h j) (le_refl 1)
    · simpa [Function.update_of_ne hi] using h i
  · exact fun x ↦ hraise x.val
  · exact fun x ↦ hunit x.val

/-- The actual j-th unit vector as a point of the proper interval.
Source: node statement and proof step 1, below direct-images paragraph (3)
(blueprint: lem-sfb-product-interval-nullhomotopy). -/
def vertex {r : ℕ} (hr : 1 ≤ r) (m : Fin r → ℕ) (j : Fin r) (hj : 2 ≤ m j) :
    Set.Ioo (0 : Fin r → ℕ) m :=
  ⟨Function.update (0 : Fin r → ℕ) j 1, (coordinate_laws hr m j hj).1⟩

/-- The specified coordinate-max endomorphism, with its induced order structure.
Source: node statement and proof step 1, below direct-images paragraph (3)
(blueprint: lem-sfb-product-interval-nullhomotopy). -/
def raise {r : ℕ} (hr : 1 ≤ r) (m : Fin r → ℕ) (j : Fin r) (hj : 2 ≤ m j) :
    Set.Ioo (0 : Fin r → ℕ) m →o Set.Ioo (0 : Fin r → ℕ) m where
  toFun x := ⟨Function.update x.val j (max (x.val j) 1),
    (coordinate_laws hr m j hj).2.1 x⟩
  monotone' x y h := (coordinate_laws hr m j hj).2.2.1 x y h

/-- The explicit degree-raising maps. In nonnegative degrees this is h(c_e,u)-h(id,u);
in degree -1 it sends the empty generator to [e], and below -1 it is zero.
Source: node statement and proof steps 2–4, below direct-images paragraph (3),
using the prism of Stacks Tag 019S
(blueprint: lem-sfb-product-interval-nullhomotopy). -/
noncomputable def contractionComponent (R : Type u) [CommRing R]
    {r : ℕ} (hr : 1 ≤ r) (m : Fin r → ℕ) (j : Fin r) (hj : 2 ≤ m j) (n k : ℤ) :
    (complex R (Set.Ioo (0 : Fin r → ℕ) m)).X n ⟶
      (complex R (Set.Ioo (0 : Fin r → ℕ) m)).X k :=
  if 0 ≤ n then
    prismComponent R (OrderHom.const _ (vertex hr m j hj)) (raise hr m j hj) n k -
      prismComponent R OrderHom.id (raise hr m j hj) n k
  else if n = -1 ∧ k = n + 1 then
    ModuleCat.ofHom (Finsupp.linearCombination R
      fun _ : Simplex (Set.Ioo (0 : Fin r → ℕ) m) n ↦
        bracket R k [vertex hr m j hj])
  else 0

private noncomputable def augmentationSection (R : Type u) [CommRing R]
    {P : Type} [PartialOrder P] (e : P) :
    (complex R P).X (-1) ⟶ (complex R P).X 0 :=
  ModuleCat.ofHom (Finsupp.linearCombination R fun _ : Simplex P (-1) ↦ bracket R 0 [e])

private theorem constant_positive (R : Type u) [CommRing R] {P : Type}
    [PartialOrder P] (e : P) (n : ℤ) (hn : 0 < n) :
    mapComponent R (OrderHom.const P e) n = 0 := by
  classical
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro c a
  have hb : bracket R n (c.val.map (OrderHom.const P e)) = 0 := by
    apply dif_neg
    intro h
    have hp := h.1
    change (c.val.map (Function.const P e)).Pairwise (· < ·) at hp
    rw [List.map_const, List.pairwise_replicate] at hp
    rcases hp with hp | hp
    · have := c.property.2
      omega
    · exact lt_irrefl e hp
  change (Finsupp.linearCombination R
    (fun c : Simplex P n ↦ bracket R n (c.val.map (OrderHom.const P e))))
      (Finsupp.single c a) = 0
  rw [Finsupp.linearCombination_single, hb, smul_zero]

private theorem augmentation_right (R : Type u) [CommRing R] {P : Type}
    [PartialOrder P] (e : P) :
    (complex R P).d 0 (-1) ≫ augmentationSection R e =
      mapComponent R (OrderHom.const P e) 0 := by
  classical
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro c a
  rcases c with ⟨l, hp, hl⟩
  have hlen : l.length = 1 := by omega
  obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp hlen
  simp [complex, boundary, augmentationSection, mapComponent, bracket,
    Finsupp.linearCombination_single]

private theorem augmentation_left (R : Type u) [CommRing R] {P : Type}
    [PartialOrder P] (e : P) :
    augmentationSection R e ≫ (complex R P).d 0 (-1) = 𝟙 _ := by
  classical
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro c a
  rcases c with ⟨l, hp, hl⟩
  have hlen : l.length = 0 := by omega
  have heq := List.length_eq_zero_iff.mp hlen
  subst l
  simp [complex, boundary, augmentationSection, bracket, Finsupp.linearCombination_single]

private theorem below_augmentation (R : Type u) [CommRing R] {P : Type}
    [PartialOrder P] (n : ℤ) (hn : n < -1) :
    (0 : (complex R P).X n ⟶ (complex R P).X n) = 𝟙 _ := by
  have : IsEmpty (Simplex P n) := ⟨fun c ↦ by have := c.property.2; omega⟩
  apply ModuleCat.hom_ext
  change (0 : chains R P n →ₗ[R] chains R P n) = LinearMap.id
  apply LinearMap.ext
  intro x
  exact Subsingleton.elim _ _

/-- The coordinate-max maps dominate the identity and the constant map, and the
specified linear maps contract the augmented strict-chain complex in every degree.
Source: node proof steps 1–4, agent-written extraction below the latest blueprint's
direct-images paragraph (3), with the prism input from Stacks Tag 019S
(blueprint: lem-sfb-product-interval-nullhomotopy).

Proof: coordinate_laws proves well-definedness and both comparisons. The interval is
finite, since its coordinates are bounded by m. Apply lem-sfb-poset-augmented-chain-prism
to (c_e,u) and (id,u), and subtract: for s=h(c_e,u)-h(id,u), ds+sd=id-(c_e)_*.
The identity-map clause identifies id_* with id. In positive degrees the constant map
kills strict generators because its image repeats e, so ds+sd=id. In degree zero,
d_0[x]=[empty], hence t_{-1}d_0[x]=[e]=(c_e)_{*,0}[x], supplying the missing term.
In degree -1, d_0t_{-1}[empty]=d_0[e]=[empty], while the other summand is zero.
Below -1 the source is zero. Extend all generator calculations by R-linearity.
These are exactly the four proof steps of the node; no characteristic restriction is used. -/
theorem nullhomotopy (R : Type u) [CommRing R] {r : ℕ} (hr : 1 ≤ r)
    (m : Fin r → ℕ) (j : Fin r) (hj : 2 ≤ m j) :
    (OrderHom.id : Set.Ioo (0 : Fin r → ℕ) m →o Set.Ioo (0 : Fin r → ℕ) m) ≤
        raise hr m j hj ∧
      OrderHom.const (Set.Ioo (0 : Fin r → ℕ) m) (vertex hr m j hj) ≤ raise hr m j hj ∧
      ∀ n : ℤ,
        contractionComponent R hr m j hj n (n + 1) ≫
            (complex R (Set.Ioo (0 : Fin r → ℕ) m)).d (n + 1) n +
          (complex R (Set.Ioo (0 : Fin r → ℕ) m)).d n (n - 1) ≫
            contractionComponent R hr m j hj (n - 1) n =
          𝟙 ((complex R (Set.Ioo (0 : Fin r → ℕ) m)).X n) := by
  classical
  let P := Set.Ioo (0 : Fin r → ℕ) m
  let e : P := vertex hr m j hj
  let u : P →o P := raise hr m j hj
  have hI : (OrderHom.id : P →o P) ≤ u := (coordinate_laws hr m j hj).2.2.2.1
  have hC : OrderHom.const P e ≤ u := (coordinate_laws hr m j hj).2.2.2.2
  refine ⟨hI, hC, ?_⟩
  let code : P → (i : Fin r) → Fin (m i + 1) :=
    fun x i ↦ ⟨x.val i, Nat.lt_succ_of_le (x.property.2.le i)⟩
  have : Finite P := Finite.of_injective code (by
    intro x y h
    apply Subtype.ext
    funext i
    exact congrArg Fin.val (congrFun h i))
  have hid (n : ℤ) : (map R (OrderHom.id : P →o P)).f n = 𝟙 _ :=
    congrArg (fun f : complex R P ⟶ complex R P ↦ f.f n) (map_id R P)
  have hs (n : ℤ) :
      (prismComponent R (OrderHom.const P e) u n (n + 1) -
          prismComponent R OrderHom.id u n (n + 1)) ≫ (complex R P).d (n + 1) n +
        (complex R P).d n (n - 1) ≫
          (prismComponent R (OrderHom.const P e) u (n - 1) n -
            prismComponent R OrderHom.id u (n - 1) n) =
        𝟙 _ - mapComponent R (OrderHom.const P e) n := by
    rw [Preadditive.sub_comp, Preadditive.comp_sub, sub_add_sub_comm,
      prism_identity R (OrderHom.const P e) u hC n,
      prism_identity R OrderHom.id u hI n, hid]
    change (_ - mapComponent R (OrderHom.const P e) n) - (_ - 𝟙 _) = _
    abel
  intro n
  by_cases hn : 0 < n
  · have hn0 : 0 ≤ n := by omega
    have hn1 : 0 ≤ n - 1 := by omega
    simpa only [contractionComponent, if_pos hn0, if_pos hn1,
      constant_positive R e n hn, sub_zero] using hs n
  · by_cases hz : n = 0
    · subst n
      have h : (prismComponent R (OrderHom.const P e) u 0 1 -
          prismComponent R OrderHom.id u 0 1) ≫ (complex R P).d 1 0 =
          𝟙 _ - mapComponent R (OrderHom.const P e) 0 := by
        simpa [prismComponent] using hs 0
      change (prismComponent R (OrderHom.const P e) u 0 1 -
          prismComponent R OrderHom.id u 0 1) ≫ (complex R P).d 1 0 +
        (complex R P).d 0 (-1) ≫ augmentationSection R e = 𝟙 _
      rw [h, augmentation_right]
      exact sub_add_cancel _ _
    · by_cases hm : n = -1
      · subst n
        change augmentationSection R e ≫ (complex R P).d 0 (-1) +
          (complex R P).d (-1) (-2) ≫ 0 = 𝟙 _
        simpa using augmentation_left R e
      · have hn0 : ¬ 0 ≤ n := by omega
        have hn1 : ¬ 0 ≤ n - 1 := by omega
        have hm1 : n - 1 ≠ -1 := by omega
        simp only [contractionComponent, if_neg hn0, if_neg hn1, hm, hm1,
          false_and, if_false, Limits.zero_comp, Limits.comp_zero, add_zero]
        exact below_augmentation R n (by omega)

end AlgebraicTopology.AugmentedPosetChains.ProductInterval
