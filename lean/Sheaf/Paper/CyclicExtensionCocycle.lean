/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.Exact.Basic

/-! # Cyclic extensions and Koszul one-cocycles

Source: Stacks Project, More on Algebra, Tags 05ED and 05EE, and Homology,
Section 010I (blueprint: lem-weil-pbc-cyclic-extension-cocycle).
-/

@[expose] public section

universe u v w z

namespace Paper

/-- Extensions of `A/J` by `P` are represented by admissible Koszul one-cycles.
Source: Stacks Project, More on Algebra, Tags 05ED and 05EE, read on extensions
as in Homology, Section 010I (blueprint: lem-weil-pbc-cyclic-extension-cocycle).

Proof, following the node's five steps:
1. The map from the free module sending `e i` to `f i` kills the relations and
   descends to `μ`, with image `J`. A cycle similarly induces `xhat` on `F/W`.
   Its vanishing on `ker μ` says that every relation `∑ a i * f i = 0` also
   satisfies `∑ a i • x i = 0` (free-module and quotient-module dependency nodes).
2. Projection to `A/J` kills `(x i, -f i)` and descends to the quotient. It is
   surjective. For a representative `(p,a)` in its kernel, write `a = ∑ b i * f i`
   and add the corresponding relations to get `(p + ∑ b i • x i,0)`.
   If `(p,0)` is a relation, admissibility gives `p = 0`. This proves exactness
   (quotient-module, direct-sum-modules and exact-sequence dependency nodes).
3. In any extension, `q (f i • lift) = 0`. Exactness and injectivity of `j` give
   unique `x i` with `j (x i) = f i • lift`. Commutativity gives the cycle
   identities. Applying `j` to any relation proves admissibility (exact-sequence node).
4. The map `(p,a) ↦ j p + a • lift` kills the relations. To lift an element of `E`,
   lift its image in `A/J` to `a` and use exactness on the remainder. For its
   kernel, write `a = ∑ b i * f i`; injectivity of `j` gives
   `p = -∑ b i • x i`, so the pair lies in the relation submodule. The induced
   map is an isomorphism and commutes with the extension maps (quotient-module,
   direct-sum-modules and exact-sequence dependency nodes).
5. Subtracting `f i • m` preserves cycles and the vanishing on relations.
   The map `(p,a) ↦ (p + a • m,a)` sends each relation for `x` to the relation
   for `x'`; its inverse uses `-m`. The first inclusion and the second-coordinate
   projection commute with it (quotient-module and direct-sum-modules nodes). -/
theorem cyclic_extension_cocycle
    {A : Type u} [CommRing A] {P : Type v} [AddCommGroup P] [Module A P]
    (t : ℕ) (ht : 1 ≤ t) (f : Fin t → A)
    (J : Ideal A) (hJ : J = Ideal.span (Set.range f))
    (F : Type w) [AddCommGroup F] [Module A F] (e : Module.Basis (Fin t) A F)
    (W : Submodule A F)
    (hW : W = Submodule.span A (Set.range (fun ij : Fin t × Fin t =>
      f ij.1 • e ij.2 - f ij.2 • e ij.1)))
    (μ : (F ⧸ W) →ₗ[A] A) (hμ : ∀ i, μ (W.mkQ (e i)) = f i) :
    let Z_f : Set (Fin t → P) := {x | ∀ i j, f i • x j = f j • x i}
    let admissible : (Fin t → P) → Prop := fun x => x ∈ Z_f ∧
      ∃ xhat : (F ⧸ W) →ₗ[A] P, (∀ i, xhat (W.mkQ (e i)) = x i) ∧
        ∀ k, k ∈ LinearMap.ker μ → xhat k = 0
    let W_x : (Fin t → P) → Submodule A (P × A) := fun x =>
      Submodule.span A (Set.range (fun i => (x i, -f i)))
    let E_f := fun x => (P × A) ⧸ W_x x
    let iota := fun x => (W_x x).mkQ.comp (LinearMap.inl A P A)
    ∃ pi : ∀ x, admissible x → E_f x →ₗ[A] A ⧸ J,
      (∀ x hx p a, pi x hx ((W_x x).mkQ (p, a)) = Ideal.Quotient.mk J a) ∧
      (∀ x hx, Function.Injective (iota x) ∧ Function.Exact (iota x) (pi x hx) ∧
        Function.Surjective (pi x hx)) ∧
      (∀ (E : Type z) [AddCommGroup E] [Module A E]
        (j : P →ₗ[A] E) (q : E →ₗ[A] A ⧸ J),
        Function.Injective j → Function.Exact j q → Function.Surjective q →
        ∀ lift : E, q lift = Ideal.Quotient.mk J 1 →
        ∃ x : Fin t → P,
          (∀ i, j (x i) = f i • lift) ∧
          (∀ y : Fin t → P, (∀ i, j (y i) = f i • lift) → y = x) ∧
          x ∈ Z_f ∧
          ∃ (hx : admissible x) (theta : E_f x ≃ₗ[A] E),
            (∀ p a, theta ((W_x x).mkQ (p, a)) = j p + a • lift) ∧
            (∀ p, theta (iota x p) = j p) ∧
            (∀ y, q (theta y) = pi x hx y)) ∧
      (∀ x (hx : admissible x) (m : P),
        let x' := fun i => x i - f i • m
        ∃ (hx' : admissible x') (change_iso : E_f x ≃ₗ[A] E_f x'),
          (∀ p a, change_iso ((W_x x).mkQ (p, a)) =
            (W_x x').mkQ (p + a • m, a)) ∧
          (∀ p, change_iso (iota x p) = iota x' p) ∧
          (∀ y, pi x' hx' (change_iso y) = pi x hx y)) := by
  classical
  have _ht := ht
  dsimp only
  let d : F →ₗ[A] A := e.constr A f
  let g : (Fin t → P) → F →ₗ[A] P := fun x ↦ e.constr A x
  let r : (Fin t → P) → F →ₗ[A] P × A := fun x ↦ (g x).prod (-d)
  let V : (Fin t → P) → Submodule A (P × A) := fun x ↦
    Submodule.span A (Set.range (fun i ↦ (x i, -f i)))
  have hd : μ.comp W.mkQ = d := e.ext fun i ↦ by simpa [d] using hμ i
  have hdr : LinearMap.range d = J := by
    rw [hJ]
    exact e.constr_range A
  have hr (x : Fin t → P) : LinearMap.range (r x) = V x := by
    have heq : r x = e.constr A (fun i ↦ (x i, -f i)) := by
      apply e.ext
      intro i
      simp [r, g, d]
    rw [heq]
    exact e.constr_range A
  have hgen (i : Fin t) : f i ∈ J := by
    rw [hJ]
    exact Ideal.subset_span (Set.mem_range_self i)
  let proj : P × A →ₗ[A] A ⧸ J := J.mkQ.comp (LinearMap.snd A P A)
  have hproj (x : Fin t → P) : V x ≤ LinearMap.ker proj := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change J.mkQ (-f i) = 0
    exact (Submodule.Quotient.mk_eq_zero J).mpr (J.neg_mem (hgen i))
  let pi : ∀ x : Fin t → P, (P × A) ⧸ V x →ₗ[A] A ⧸ J :=
    fun x ↦ (V x).liftQ proj (hproj x)
  have hpi (x : Fin t → P) (p : P) (a : A) :
      pi x ((V x).mkQ (p, a)) = Ideal.Quotient.mk J a := rfl
  have hkill (x : Fin t → P)
      (hx : ∃ xhat : (F ⧸ W) →ₗ[A] P,
        (∀ i, xhat (W.mkQ (e i)) = x i) ∧
        ∀ k, k ∈ LinearMap.ker μ → xhat k = 0) :
      ∀ b, d b = 0 → g x b = 0 := by
    obtain ⟨xhat, hxe, hxk⟩ := hx
    have hg : xhat.comp W.mkQ = g x :=
      e.ext fun i ↦ by simpa [g] using hxe i
    intro b hb
    rw [← hg]
    exact hxk _ (by change μ (W.mkQ b) = 0; rw [← LinearMap.comp_apply, hd, hb])
  refine ⟨fun x _ ↦ pi x, fun x _ p a ↦ hpi x p a, ?_, ?_, ?_⟩
  · intro x hx
    have hk := hkill x hx.2
    constructor
    · apply (LinearMap.ker_eq_bot).mp
      apply le_antisymm _ bot_le
      intro p hp
      have hpV : (p, (0 : A)) ∈ V x := (Submodule.Quotient.mk_eq_zero (V x)).mp hp
      rw [← hr] at hpV
      obtain ⟨b, hb⟩ := hpV
      have hb1 : g x b = p := congrArg Prod.fst hb
      have hb2 : d b = 0 := by
        have := congrArg Prod.snd hb
        simpa [r] using this
      simp [← hb1, hk b hb2]
    constructor
    · intro y
      obtain ⟨⟨p, a⟩, rfl⟩ := (V x).mkQ_surjective y
      constructor
      · intro hy
        have ha : a ∈ J := (Submodule.Quotient.mk_eq_zero J).mp hy
        rw [← hdr] at ha
        obtain ⟨b, hb⟩ := ha
        refine ⟨p + g x b, ?_⟩
        change (V x).mkQ (p + g x b, 0) = (V x).mkQ (p, a)
        apply (Submodule.Quotient.eq (V x)).mpr
        have hm : r x b ∈ V x := by rw [← hr]; exact ⟨b, rfl⟩
        convert hm using 1; simp [r, hb]
      · rintro ⟨p', hp'⟩
        rw [← hp']
        exact map_zero J.mkQ
    · intro y
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact ⟨(V x).mkQ (0, a), rfl⟩
  · intro E _ _ j q hj hex hq lift hlift
    have hfi (i : Fin t) : q (f i • lift) = 0 := by
      rw [map_smul, hlift]
      change J.mkQ (f i * 1) = 0
      simpa using (Submodule.Quotient.mk_eq_zero J).mpr (hgen i)
    choose x hx using fun i ↦ (hex (f i • lift)).mp (hfi i)
    have hcycle : ∀ i k, f i • x k = f k • x i := by
      intro i k
      apply hj
      simp only [map_smul, hx, smul_smul, mul_comm]
    have hgj : j.comp (g x) = (LinearMap.toSpanSingleton A E lift).comp d := by
      apply e.ext
      intro i
      simpa [g, d] using hx i
    have hWg : W ≤ LinearMap.ker (g x) := by
      rw [hW]
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨i, k⟩, rfl⟩
      change g x (f i • e k - f k • e i) = 0
      simp only [map_sub, map_smul, g, Module.Basis.constr_basis, sub_eq_zero]
      exact hcycle i k
    let xhat := W.liftQ (g x) hWg
    have hxadm : (∀ i k, f i • x k = f k • x i) ∧
        ∃ xhat : (F ⧸ W) →ₗ[A] P,
          (∀ i, xhat (W.mkQ (e i)) = x i) ∧
          ∀ k, k ∈ LinearMap.ker μ → xhat k = 0 := by
      refine ⟨hcycle, xhat, ?_, ?_⟩
      · intro i
        simp [xhat, g]
      · intro k hk
        obtain ⟨b, rfl⟩ := W.mkQ_surjective k
        apply hj
        change j (g x b) = j 0
        have hb : d b = 0 := by
          rw [← hd]
          exact hk
        change (j.comp (g x)) b = _
        rw [hgj]
        simp [hb]
    let h : P × A →ₗ[A] E :=
      j.comp (LinearMap.fst A P A) +
        (LinearMap.toSpanSingleton A E lift).comp (LinearMap.snd A P A)
    have hkillr : V x ≤ LinearMap.ker h := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      change j (x i) + (-f i) • lift = 0
      simp [hx]
    have hqh (p : P) (a : A) : q (h (p, a)) = Ideal.Quotient.mk J a := by
      change q (j p + a • lift) = _
      rw [map_add, hex.apply_apply_eq_zero, map_smul, hlift, zero_add]
      change J.mkQ (a * 1) = J.mkQ a
      rw [mul_one]
    have hker : LinearMap.ker h ≤ V x := by
      rintro ⟨p, a⟩ hpa
      have ha : a ∈ J := by
        apply (Submodule.Quotient.mk_eq_zero J).mp
        change Ideal.Quotient.mk J a = 0
        rw [← hqh, show h (p, a) = 0 from hpa, map_zero]
      rw [← hdr] at ha
      obtain ⟨b, hb⟩ := ha
      have hp : p = -g x b := by
        apply hj
        rw [map_neg]
        have hgb : j (g x b) = a • lift := by
          change (j.comp (g x)) b = _
          rw [hgj]
          simp [hb]
        rw [hgb]
        exact eq_neg_of_add_eq_zero_left hpa
      rw [hp]
      have hm : r x (-b) ∈ V x := by rw [← hr]; exact ⟨-b, rfl⟩
      convert hm using 1; simp [r, hb]
    have hsurj : Function.Surjective h := by
      intro y
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (q y)
      have hy : q (y - a • lift) = 0 := by
        rw [map_sub, map_smul, hlift]
        change q y - J.mkQ (a * 1) = 0
        simp [ha]
      obtain ⟨p, hp⟩ := (hex _).mp hy
      exact ⟨(p, a), by change j p + a • lift = y; rw [hp]; abel⟩
    let theta : ((P × A) ⧸ V x) ≃ₗ[A] E :=
      LinearEquiv.ofBijective ((V x).liftQ h hkillr)
        ⟨LinearMap.ker_eq_bot.mp ((V x).ker_liftQ_eq_bot h hkillr hker),
          fun y ↦ by obtain ⟨pa, hpa⟩ := hsurj y; exact ⟨(V x).mkQ pa, hpa⟩⟩
    refine ⟨x, hx, ?_, hcycle, hxadm, theta, ?_, ?_, ?_⟩
    · intro y hy
      funext i
      exact hj ((hy i).trans (hx i).symm)
    · intro p a
      rfl
    · intro p
      change j p + (0 : A) • lift = j p
      simp
    · intro y
      obtain ⟨⟨p, a⟩, rfl⟩ := (V x).mkQ_surjective y
      exact hqh p a
  · intro x hx m
    let x' : Fin t → P := fun i ↦ x i - f i • m
    have hcycle' : ∀ i k, f i • x' k = f k • x' i := by
      intro i k
      dsimp [x']
      rw [smul_sub, smul_sub, hx.1 i k, smul_smul, smul_smul, mul_comm (f i)]
    obtain ⟨xhat, hxe, hxk⟩ := hx.2
    let xhat' : (F ⧸ W) →ₗ[A] P :=
      xhat - (LinearMap.toSpanSingleton A P m).comp μ
    have hxadm' : (∀ i k, f i • x' k = f k • x' i) ∧
        ∃ xhat : (F ⧸ W) →ₗ[A] P,
          (∀ i, xhat (W.mkQ (e i)) = x' i) ∧
          ∀ k, k ∈ LinearMap.ker μ → xhat k = 0 := by
      refine ⟨hcycle', xhat', ?_, ?_⟩
      · intro i
        change xhat (W.mkQ (e i)) - μ (W.mkQ (e i)) • m = x i - f i • m
        rw [hxe, hμ]
      · intro k hk
        change xhat k - μ k • m = 0
        rw [hxk k hk, show μ k = 0 from hk, zero_smul, sub_zero]
    let shear : (P × A) ≃ₗ[A] P × A :=
      { toFun := fun pa ↦ (pa.1 + pa.2 • m, pa.2)
        invFun := fun pa ↦ (pa.1 - pa.2 • m, pa.2)
        left_inv := by intro pa; ext <;> simp
        right_inv := by intro pa; ext <;> simp
        map_add' := by
          intro pa qa
          ext <;> simp [add_smul, add_assoc, add_left_comm]
        map_smul' := by
          intro a pa
          ext <;> simp [smul_add, smul_smul] }
    have hshear : (V x).map shear.toLinearMap = V x' := by
      change (Submodule.span A (Set.range (fun i ↦ (x i, -f i)))).map _ = _
      rw [Submodule.map_span, ← Set.range_comp]
      congr 1
      ext i
      simp [shear, x', sub_eq_add_neg]
    let changeIso := Submodule.Quotient.equiv (V x) (V x') shear hshear
    refine ⟨hxadm', changeIso, ?_, ?_, ?_⟩
    · intro p a
      rfl
    · intro p
      change (V x').mkQ (p + (0 : A) • m, 0) = (V x').mkQ (p, 0)
      simp
    · intro y
      obtain ⟨⟨p, a⟩, rfl⟩ := (V x).mkQ_surjective y
      rfl

end Paper
