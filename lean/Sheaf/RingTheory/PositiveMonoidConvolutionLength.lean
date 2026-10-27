/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q49
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Group.Submonoid.Operations
public import Mathlib.Algebra.Ring.Pi

import Mathlib.Data.Set.Finite.List
import Mathlib.Data.Nat.SuccPred
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Order.SuccPred.Archimedean
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith

/-!
# Positive monoid lengths and finite convolution

Source: Illusie–Laszlo–Orgogozo, Travaux de Gabber, Exposé VI, §1.6(i)–(ii),
printed p. 70 (PDF p. 76), formal monoid models. The elementary coefficient
argument is supplied by the DAG, rather than asserted to be a theorem of ILO
(blueprint: lem-trf-positive-monoid-convolution-length).
-/

@[expose] public section

universe u v

namespace AddMonoidAlgebra

private theorem length_weight_bound {P : Type*} [AddCommMonoid P]
    (w : P →+ ℤ) (hw : ∀ p, p ≠ 0 → 0 < w p)
    (l : ℕ) (f : Fin l → P) (hf : ∀ i, f i ≠ 0) : (l : ℤ) ≤ w (∑ i, f i) := by
  calc
    (l : ℤ) = ∑ _i : Fin l, (1 : ℤ) := by simp
    _ ≤ ∑ i, w (f i) := Finset.sum_le_sum fun i _ ↦ by
      have := hw (f i) (hf i)
      omega
    _ = w (∑ i, f i) := (map_sum w f Finset.univ).symm

private theorem exists_max_length {P : Type*} [AddCommMonoid P]
    (w : P →+ ℤ) (hw : ∀ p, p ≠ 0 → 0 < w p) :
    ∃ ν : P → ℕ,
      (∀ p, IsGreatest {l : ℕ | ∃ f : Fin l → P,
        (∀ i, f i ≠ 0) ∧ (∑ i, f i) = p} (ν p)) ∧ ν 0 = 0 := by
  classical
  have hmax (p : P) : ∃ n, IsGreatest {l : ℕ | ∃ f : Fin l → P,
      (∀ i, f i ≠ 0) ∧ (∑ i, f i) = p} n := by
    apply BddAbove.exists_isGreatest_of_nonempty
    · refine ⟨(w p).toNat, ?_⟩
      rintro l ⟨f, hf, rfl⟩
      have := length_weight_bound w hw l f hf
      omega
    · by_cases hp : p = 0
      · subst p
        exact ⟨0, (fun i ↦ Fin.elim0 i), (by simp), (by simp)⟩
      · exact ⟨1, (fun _ ↦ p), (fun _ ↦ hp), (by simp)⟩
  choose ν hν using hmax
  refine ⟨ν, hν, ?_⟩
  obtain ⟨f, hf, he⟩ := (hν 0).1
  have hb := length_weight_bound w hw (ν 0) f hf
  rw [he, map_zero] at hb
  omega

private theorem exists_generator_word {G : Type*} [AddCommGroup G]
    (P : AddSubmonoid G) {s : ℕ} (g : Fin s → G)
    (hgen : AddSubmonoid.closure (Set.range g) = P)
    (gp : Fin s → P) (hgp : ∀ i, (gp i : G) = g i) (p : P) :
    ∃ l : List (Fin s), (l.map gp).sum = p := by
  have hx : (p : G) ∈ AddSubmonoid.closure (Set.range g) := hgen.symm ▸ p.property
  have hall (x : G) (hx : x ∈ AddSubmonoid.closure (Set.range g)) :
      ∃ l : List (Fin s), (l.map g).sum = x := by
    induction hx using AddSubmonoid.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact ⟨[i], by simp⟩
    | zero => exact ⟨[], by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨l, rfl⟩ := hx
      obtain ⟨k, rfl⟩ := hy
      exact ⟨l ++ k, by simp⟩
  obtain ⟨l, hl⟩ := hall p hx
  refine ⟨l, Subtype.ext ?_⟩
  change P.subtype ((l.map gp).sum) = _
  rw [map_list_sum, List.map_map]
  have he : (P.subtype ∘ gp) = g := funext hgp
  rw [he]
  exact hl

private theorem word_length_mem {P : Type*} [AddCommMonoid P]
    {ι : Type*} (gp : ι → P) (hg : ∀ i, gp i ≠ 0) (l : List ι) :
    ∃ f : Fin l.length → P, (∀ i, f i ≠ 0) ∧ ∑ i, f i = (l.map gp).sum := by
  refine ⟨fun i ↦ gp (l.get i), fun i ↦ hg _, ?_⟩
  simpa only [List.ofFn_comp', List.ofFn_get] using
    (Fin.sum_ofFn (fun i ↦ gp (l.get i))).symm

private noncomputable def pmConv {P A : Type*} [AddCommMonoid P] [CommRing A]
    (a b : P → A) (p : P) : A :=
  ∑ᶠ q : {q : P × P // q.1 + q.2 = p}, a q.1.1 * b q.1.2

private theorem pmConv_comm {P A : Type*} [AddCommMonoid P] [CommRing A]
    (a b : P → A) : pmConv a b = pmConv b a := by
  funext p
  let e : {q : P × P // q.1 + q.2 = p} ≃ {q : P × P // q.1 + q.2 = p} :=
    { toFun := fun q ↦ ⟨(q.1.2, q.1.1), (add_comm _ _).trans q.2⟩
      invFun := fun q ↦ ⟨(q.1.2, q.1.1), (add_comm _ _).trans q.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  exact finsum_eq_of_bijective e e.bijective (fun _ ↦ mul_comm _ _)

open Classical in
private theorem pmConv_single {P A : Type*} [AddCommMonoid P] [IsCancelAdd P]
    [CommRing A] [DecidableEq P]
    (s q : P) (a : A) (c : P → A) :
    pmConv (Pi.single s a) c (s + q) = a * c q := by
  classical
  unfold pmConv
  let t : {t : P × P // t.1 + t.2 = s + q} := ⟨(s, q), rfl⟩
  calc
    _ = (Pi.single s a : P → A) t.1.1 * c t.1.2 := by
      apply finsum_eq_single _ t
      intro x hx
      by_cases hs : x.1.1 = s
      · have hq : x.1.2 = q := add_left_cancel (a := s) (by simpa only [hs] using x.2)
        exact (hx (Subtype.ext (Prod.ext hs hq))).elim
      · simp [hs]
    _ = a * c q := by simp [t]

open Classical in
private theorem pmConv_single_zero {P A : Type*} [AddCommMonoid P] [CommRing A]
    [DecidableEq P]
    (s p : P) (a : A) (c : P → A) (hp : ¬ ∃ q, p = s + q) :
    pmConv (Pi.single s a) c p = 0 := by
  classical
  apply finsum_eq_zero_of_forall_eq_zero
  intro x
  have hs : x.1.1 ≠ s := fun hs ↦ hp ⟨x.1.2, by simpa [hs] using x.2.symm⟩
  simp [hs]

open Classical in
private theorem pmConv_single_single {P A : Type*}
    [AddCommMonoid P] [IsCancelAdd P] [CommRing A] [DecidableEq P] (u v : P) (a b : A) :
    pmConv (Pi.single u a) (Pi.single v b) = Pi.single (u + v) (a * b) := by
  classical
  funext p
  by_cases hp : p = u + v
  · subst p
    rw [pmConv_single]
    simp
  · have hs : (Pi.single (u + v) (a * b) : P → A) p = 0 := by simp [hp]
    rw [hs]
    apply finsum_eq_zero_of_forall_eq_zero
    rintro ⟨⟨x, y⟩, hxy⟩
    by_cases hx : x = u
    · have hy : y ≠ v := by
        intro hy
        exact hp (by simpa [hx, hy] using hxy.symm)
      simp [Pi.single_apply, hy]
    · simp [Pi.single_apply, hx]

private theorem pmConv_assoc {P A : Type*} [AddCommMonoid P] [CommRing A]
    (hpairs : ∀ p : P, Set.Finite {q : P × P | q.1 + q.2 = p})
    (a b c : P → A) : pmConv (pmConv a b) c = pmConv a (pmConv b c) := by
  classical
  let D (p : P) := {q : P × P // q.1 + q.2 = p}
  let (p : P) : Fintype (D p) := (hpairs p).fintype
  funext p
  let e : (Σ q : D p, D q.1.1) ≃ (Σ q : D p, D q.1.2) :=
    { toFun := fun x ↦
        ⟨⟨(x.2.1.1, x.2.1.2 + x.1.1.2), by
          rw [← add_assoc, x.2.2, x.1.2]⟩, ⟨(x.2.1.2, x.1.1.2), rfl⟩⟩
      invFun := fun x ↦
        ⟨⟨(x.1.1.1 + x.2.1.1, x.2.1.2), by
          rw [add_assoc, x.2.2, x.1.2]⟩, ⟨(x.1.1.1, x.2.1.1), rfl⟩⟩
      left_inv := by
        rintro ⟨⟨⟨h, t⟩, ht⟩, ⟨⟨u, v⟩, uv⟩⟩
        dsimp at uv
        subst h
        rfl
      right_inv := by
        rintro ⟨⟨⟨u, k⟩, uk⟩, ⟨⟨v, t⟩, vt⟩⟩
        dsimp at vt
        subst k
        rfl }
  change (∑ᶠ q : D p, (∑ᶠ r : D q.1.1, a r.1.1 * b r.1.2) * c q.1.2) =
    ∑ᶠ q : D p, a q.1.1 * ∑ᶠ r : D q.1.2, b r.1.1 * c r.1.2
  simp only [finsum_eq_sum_of_fintype, Finset.sum_mul, Finset.mul_sum]
  rw [← Fintype.sum_sigma', ← Fintype.sum_sigma']
  exact Fintype.sum_equiv e _ _ (fun _ ↦ mul_assoc _ _ _)

@[instance_reducible]
private noncomputable def pmRing {P A : Type*} [AddCommMonoid P] [IsCancelAdd P]
    [CommRing A] [DecidableEq P]
    (hpairs : ∀ p : P, Set.Finite {q : P × P | q.1 + q.2 = p}) : CommRing (P → A) := by
  classical
  let : Mul (P → A) := ⟨pmConv⟩
  let : One (P → A) := ⟨Pi.single 0 1⟩
  let : NatCast (P → A) := ⟨fun n ↦ Pi.single 0 (n : A)⟩
  let : IntCast (P → A) := ⟨fun n ↦ Pi.single 0 (n : A)⟩
  exact
    { Pi.addCommGroup with
      mul := pmConv
      one := Pi.single 0 1
      npow := fun n a ↦ Nat.rec (Pi.single 0 1) (fun _ b ↦ pmConv b a) n
      npow_zero := fun _ ↦ rfl
      npow_succ := fun _ _ ↦ rfl
      mul_assoc := pmConv_assoc hpairs
      mul_comm := pmConv_comm
      one_mul := fun a ↦ funext fun p ↦ by
        change pmConv (Pi.single 0 1) a p = a p
        simpa using pmConv_single 0 p (1 : A) a
      mul_one := fun a ↦ by
        change pmConv a (Pi.single 0 1) = a
        rw [pmConv_comm]
        exact funext fun p ↦ by simpa using pmConv_single 0 p (1 : A) a
      zero_mul := fun a ↦ funext fun p ↦ by
        change pmConv 0 a p = 0
        simp [pmConv]
      mul_zero := fun a ↦ funext fun p ↦ by
        change pmConv a 0 p = 0
        simp [pmConv]
      left_distrib := fun a b c ↦ funext fun p ↦ by
        change pmConv a (b + c) p = pmConv a b p + pmConv a c p
        let : Fintype {q : P × P // q.1 + q.2 = p} := (hpairs p).fintype
        simp [pmConv, mul_add, finsum_eq_sum_of_fintype, Finset.sum_add_distrib]
      right_distrib := fun a b c ↦ funext fun p ↦ by
        change pmConv (a + b) c p = pmConv a c p + pmConv b c p
        let : Fintype {q : P × P // q.1 + q.2 = p} := (hpairs p).fintype
        simp [pmConv, add_mul, finsum_eq_sum_of_fintype, Finset.sum_add_distrib]
      natCast := fun n ↦ Pi.single 0 (n : A)
      natCast_zero := by ext p; simp
      natCast_succ := fun n ↦ by
        change (Pi.single 0 ((n + 1 : ℕ) : A) : P → A) =
          (Pi.single 0 (n : A) : P → A) + (Pi.single 0 (1 : A) : P → A)
        ext p
        by_cases hp : p = 0 <;> simp [hp]
      intCast := fun n ↦ Pi.single 0 (n : A)
      intCast_ofNat := fun n ↦ by
        change (Pi.single 0 ((n : ℤ) : A) : P → A) = Pi.single 0 (n : A)
        simp
      intCast_negSucc := fun n ↦ by
        change (Pi.single 0 ((Int.negSucc n : ℤ) : A) : P → A) =
          -(Pi.single 0 ((n + 1 : ℕ) : A) : P → A)
        ext p
        by_cases hp : p = 0 <;> simp [hp] }

private noncomputable def pmConstant {P A : Type*} [AddCommMonoid P] [IsCancelAdd P]
    [CommRing A] [DecidableEq P]
    (hpairs : ∀ p : P, Set.Finite {q : P × P | q.1 + q.2 = p}) :
    @RingHom A (P → A) _ (pmRing hpairs).toNonAssocSemiring := by
  letI : NonAssocSemiring (P → A) := (pmRing hpairs).toNonAssocSemiring
  exact
    { toFun := fun a ↦ (Pi.single 0 a : P → A)
      map_zero' := by ext p; simp
      map_one' := rfl
      map_add' := fun a b ↦ by
        change (Pi.single 0 (a + b) : P → A) = Pi.single 0 a + Pi.single 0 b
        ext p
        by_cases hp : p = 0 <;> simp [hp]
      map_mul' := fun a b ↦ by
        change (Pi.single 0 (a * b) : P → A) = pmConv (Pi.single 0 a) (Pi.single 0 b)
        simpa using (pmConv_single_single (0 : P) 0 a b).symm }

open Classical in
/-- Positive lattice monoids have attained maximal decomposition lengths, finite
weight and length sublevel sets, and a convolution ring of all coefficient families.

Source: ILO, Exposé VI, §1.6(i)–(ii), printed p. 70 (PDF p. 76), formal monoid
models; agent-supplied elementary coefficient argument
(blueprint: lem-trf-positive-monoid-convolution-length).

The finite list of nonzero generators may be empty. `Module.Free` and
`Module.Finite` say that the ambient group has a finite integral basis.
The explicitly quantified ring on `P → A` has convolution multiplication.
`Pi.single p 1` is the monomial `z^p`; the displayed formula for `C` is `a z^0`.

Proof plan:
1. Each nonzero summand has integral weight at least one. Additivity bounds a
   decomposition length by the weight and makes every nonempty sum positive.
2. Decomposition lengths form a nonempty bounded subset of the naturals: use the
   empty decomposition at zero and the singleton elsewhere. Its largest element
   is attained; at zero only the empty decomposition is possible.
3. Express an exponent as a sum of the generators with natural multiplicities.
   Weight at most `M` bounds every multiplicity by `M`, so a finite box surjects
   onto the weight sublevel set, also for the empty generator list.
4. The sum of these multiplicities is a decomposition length, hence at most `ν p`.
   Thus `ν p < n` bounds each multiplicity by `n - 1`, giving another finite box.
5. In a pair or triple with sum `p`, each weight is at most `wgt p`. The pair and
   triple sets therefore lie in products of the finite weight sublevel set.
6. Define addition, zero and negatives coefficientwise, and multiplication by
   the finite pair sum. The additive laws and distributivity hold coefficientwise
   by the ring laws of `A` and induction on finite sums.
7. Swapping the two indices proves commutativity. In multiplication by `z^0`,
   the only nonzero term has indices `(0,p)`, proving the unit laws.
8. Both bracketings of a triple product reindex to the finite triples with sum
   `p`, by inserting or forgetting the intermediate sum. Associativity in `A`
   then proves associativity, completing the commutative ring structure.
9. Multiplying two monomials leaves only their single pair of indices, proving
   the monomial formula. Constants supported at zero preserve addition, products
   and one, and a constant times a monomial has the stated single coefficient.
10. In `z^s₀ * c`, only the first index `s₀` survives. The second index is unique
    by cancellation in `G`. If it does not exist the sum is zero. All sums are
    finite, so the argument requires neither a topology nor completeness on `A`.
-/
theorem positiveMonoid_convolution_length
    (G : Type u) [AddCommGroup G] [Module.Free ℤ G] [Module.Finite ℤ G]
    (P : AddSubmonoid G) (s : ℕ) (g : Fin s → G)
    (hg : ∀ i : Fin s, g i ≠ 0)
    (hgen : AddSubmonoid.closure (Set.range g) = P)
    (wgt : G →+ ℤ) (hpos : ∀ p : P, p ≠ 0 → 0 < wgt (p : G)) :
    (∀ (l : ℕ) (f : Fin l → P), (∀ i : Fin l, f i ≠ 0) →
      (0 < l → 0 < wgt ((∑ i, f i : P) : G)) ∧
      (l : ℤ) ≤ wgt ((∑ i, f i : P) : G)) ∧
    ∃ ν : P → ℕ,
      (∀ p : P, IsGreatest {l : ℕ | ∃ f : Fin l → P,
        (∀ i : Fin l, f i ≠ 0) ∧ (∑ i, f i) = p} (ν p)) ∧
      ν 0 = 0 ∧
      (∀ M : ℤ, 0 ≤ M → Set.Finite {p : P | wgt (p : G) ≤ M}) ∧
      (∀ n : ℕ, 1 ≤ n → Set.Finite {p : P | ν p < n}) ∧
      (∀ p : P, Set.Finite {q : P × P | q.1 + q.2 = p}) ∧
      (∀ p : P, Set.Finite {q : P × P × P | q.1 + q.2.1 + q.2.2 = p}) ∧
      ∀ (A : Type v) [CommRing A],
        ∃ ring : CommRing (P → A),
          (∀ p : P, (@Zero.zero (P → A) ring.toZero) p = 0) ∧
          (@One.one (P → A) ring.toOne) = Pi.single (0 : P) (1 : A) ∧
          (∀ (a c : P → A) (p : P),
            (@Add.add (P → A) ring.toAdd a c) p = a p + c p) ∧
          (∀ (a c : P → A) (p : P),
            (@Mul.mul (P → A) ring.toMul a c) p =
              ∑ᶠ q : {q : P × P // q.1 + q.2 = p}, a q.1.1 * c q.1.2) ∧
          ∃ C : @RingHom A (P → A) _ ring.toNonAssocSemiring,
            (∀ (a : A) (p : P), C a p = if p = 0 then a else 0) ∧
            (∀ u v : P,
              @Mul.mul (P → A) ring.toMul (Pi.single u (1 : A)) (Pi.single v (1 : A)) =
                Pi.single (u + v) (1 : A)) ∧
            (∀ (a : A) (p q : P),
              (@Mul.mul (P → A) ring.toMul (C a) (Pi.single p (1 : A))) q =
                if q = p then a else 0) ∧
            ∀ (s₀ : P) (c : P → A),
              (∀ p q : P, p = s₀ + q →
                (@Mul.mul (P → A) ring.toMul (Pi.single s₀ (1 : A)) c) p = c q) ∧
              (∀ p : P, (¬ ∃ q : P, p = s₀ + q) →
                (@Mul.mul (P → A) ring.toMul (Pi.single s₀ (1 : A)) c) p = 0) ∧
              (∀ q q' : P, s₀ + q = s₀ + q' → q = q')  := by
  classical
  let w : P →+ ℤ := wgt.comp P.subtype
  have hw : ∀ p : P, p ≠ 0 → 0 < w p := hpos
  have hw0 (p : P) : 0 ≤ w p := by
    by_cases hp : p = 0
    · simp [hp]
    · exact le_of_lt (hw p hp)
  refine ⟨?_, ?_⟩
  · intro l f hf
    have hb := length_weight_bound w hw l f hf
    exact ⟨fun hl ↦ lt_of_lt_of_le (Nat.cast_pos.mpr hl) hb, hb⟩
  obtain ⟨ν, hν, hν0⟩ := exists_max_length w hw
  have hgmem (i : Fin s) : g i ∈ P := by
    rw [← hgen]
    exact AddSubmonoid.subset_closure (Set.mem_range_self i)
  let gp : Fin s → P := fun i ↦ ⟨g i, hgmem i⟩
  have hgp (i : Fin s) : gp i ≠ 0 := fun h ↦ hg i (congrArg Subtype.val h)
  have hword := exists_generator_word P g hgen gp (fun _ ↦ rfl)
  have hfinite (M : ℤ) (_hM : 0 ≤ M) : Set.Finite {p : P | w p ≤ M} := by
    apply ((List.finite_length_le (Fin s) M.toNat).image
      (fun l ↦ (l.map gp).sum)).subset
    intro p hp
    obtain ⟨l, rfl⟩ := hword p
    obtain ⟨f, hf, he⟩ := word_length_mem gp hgp l
    refine ⟨l, ?_, rfl⟩
    change l.length ≤ M.toNat
    have hb := length_weight_bound w hw l.length f hf
    rw [he] at hb
    change w ((l.map gp).sum) ≤ M at hp
    omega
  have hlow (n : ℕ) (_hn : 1 ≤ n) : Set.Finite {p : P | ν p < n} := by
    apply ((List.finite_length_lt (Fin s) n).image
      (fun l ↦ (l.map gp).sum)).subset
    intro p hp
    obtain ⟨l, hl⟩ := hword p
    obtain ⟨f, hf, he⟩ := word_length_mem gp hgp l
    have hb := (hν p).2 (show l.length ∈ {l : ℕ | ∃ f : Fin l → P,
      (∀ i, f i ≠ 0) ∧ (∑ i, f i) = p} from ⟨f, hf, he.trans hl⟩)
    exact ⟨l, lt_of_le_of_lt hb hp, hl⟩
  have hpairs (p : P) : Set.Finite {q : P × P | q.1 + q.2 = p} := by
    apply ((hfinite (w p) (hw0 p)).prod (hfinite (w p) (hw0 p))).subset
    rintro ⟨a, b⟩ hab
    have he : w a + w b = w p := (map_add w a b).symm.trans (congrArg w hab)
    exact ⟨by dsimp; linarith [hw0 b], by dsimp; linarith [hw0 a]⟩
  have htriples (p : P) :
      Set.Finite {q : P × P × P | q.1 + q.2.1 + q.2.2 = p} := by
    apply ((hfinite (w p) (hw0 p)).prod
      ((hfinite (w p) (hw0 p)).prod (hfinite (w p) (hw0 p)))).subset
    rintro ⟨a, b, c⟩ habc
    have he : w a + w b + w c = w p := by
      rw [← map_add, ← map_add, habc]
    exact ⟨by dsimp; linarith [hw0 b, hw0 c],
      by dsimp; linarith [hw0 a, hw0 c], by dsimp; linarith [hw0 a, hw0 b]⟩
  refine ⟨ν, hν, hν0, hfinite, hlow, hpairs, htriples, ?_⟩
  intro A instA
  let ring : CommRing (P → A) := pmRing hpairs
  refine ⟨ring, (fun _ ↦ rfl), rfl, (fun _ _ _ ↦ rfl), (fun _ _ _ ↦ rfl), ?_⟩
  let C := pmConstant (A := A) hpairs
  refine ⟨C, ?_, ?_, ?_, ?_⟩
  · intro a p
    change (Pi.single 0 a : P → A) p = _
    simp [Pi.single_apply]
  · intro u v
    change pmConv (Pi.single u (1 : A)) (Pi.single v (1 : A)) = _
    simpa using pmConv_single_single u v (1 : A) 1
  · intro a p q
    change pmConv (Pi.single 0 a) (Pi.single p (1 : A)) q = _
    rw [pmConv_single_single]
    simp [Pi.single_apply]
  · intro s₀ c
    refine ⟨?_, ?_, ?_⟩
    · intro p q hp
      subst p
      change pmConv (Pi.single s₀ (1 : A)) c (s₀ + q) = _
      simpa using pmConv_single s₀ q (1 : A) c
    · intro p hp
      exact pmConv_single_zero s₀ p (1 : A) c hp
    · intro q q' hq
      exact add_left_cancel hq

end AddMonoidAlgebra
