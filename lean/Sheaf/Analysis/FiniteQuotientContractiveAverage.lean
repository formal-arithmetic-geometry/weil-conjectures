/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q67
-/
module

public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Algebra.BigOperators.Finprod

import Mathlib.Algebra.CharP.Algebra

/-!
# Contractive averaging on finite quotient functions

Source: blueprint, `sec-six-functors-basics`, `sk-thm-sf-ctf-stability`,
direct-images proof, paragraph (3), auxiliary scalar tame-kernel analytic input
(blueprint: lem-sfb-finite-quotient-contractive-average).
The finite-sum argument is the auxiliary DAG proof; an exact literature reference
for this auxiliary assertion is WANTED, as recorded in the node.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace ContinuousMap

private noncomputable def quotientAverage {B : Type v} [Field B] {Q : Type u}
    (g : Q → B) : B := (Nat.card Q : B)⁻¹ * ∑ᶠ q, g q

private theorem quotientAverage_add {B : Type v} [Field B] {Q : Type u} [Finite Q]
    (g h : Q → B) : quotientAverage (g + h) = quotientAverage g + quotientAverage h := by
  classical
  let := Fintype.ofFinite Q
  simp [quotientAverage, finsum_eq_sum_of_fintype, Finset.sum_add_distrib, mul_add]

private theorem quotientAverage_smul {B : Type v} [Field B] {Q : Type u} [Finite Q]
    (b : B) (g : Q → B) : quotientAverage (b • g) = b * quotientAverage g := by
  classical
  let := Fintype.ofFinite Q
  simp [quotientAverage, finsum_eq_sum_of_fintype, Pi.smul_apply, smul_eq_mul,
    ← Finset.mul_sum, mul_left_comm]

private theorem quotientAverage_const {B : Type v} [Field B] [CharZero B]
    {Q : Type u} [Finite Q] [Nonempty Q] (b : B) :
    quotientAverage (fun _ : Q ↦ b) = b := by
  classical
  let := Fintype.ofFinite Q
  have hn : (Fintype.card Q : B) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp [quotientAverage, finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card,
    nsmul_eq_mul, hn]

private theorem quotientAverage_comp {B : Type v} [Field B] [CharZero B]
    {X Y : Type u} [Group X] [Group Y] [Finite X] [Finite Y]
    (r : X →* Y) (hr : Function.Surjective r) (g : Y → B) :
    quotientAverage (fun x ↦ g (r x)) = quotientAverage g := by
  classical
  let := Fintype.ofFinite X
  let := Fintype.ofFinite Y
  have hsum (y : Y) : (∑ x : X, g (y * r x)) = ∑ x : X, g (r x) := by
    obtain ⟨a, rfl⟩ := hr y
    simpa only [Equiv.coe_mulLeft, ← map_mul] using
      Equiv.sum_comp (Equiv.mulLeft a) (fun x ↦ g (r x))
  have hsum' (x : X) : (∑ y : Y, g (y * r x)) = ∑ y : Y, g y := by
    simpa only [Equiv.coe_mulRight] using Equiv.sum_comp (Equiv.mulRight (r x)) g
  have hd : (Fintype.card Y : B) * (∑ x : X, g (r x)) =
      (Fintype.card X : B) * (∑ y : Y, g y) := by
    calc
      _ = ∑ y : Y, ∑ x : X, g (y * r x) := by
        simp only [hsum, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      _ = ∑ x : X, ∑ y : Y, g (y * r x) := Finset.sum_comm
      _ = _ := by
        simp only [hsum', Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have hx : (Fintype.card X : B) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hy : (Fintype.card Y : B) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [quotientAverage, Nat.card_eq_fintype_card, finsum_eq_sum_of_fintype]
  apply (mul_left_cancel₀ hx)
  rw [← mul_assoc, mul_inv_cancel₀ hx, one_mul]
  apply (mul_left_cancel₀ hy)
  rw [hd]
  field_simp [hy]

private theorem nonarchimedean_sum_bound {B : Type v} [NormedField B]
    (hB : IsNonarchimedean (norm : B → ℝ)) {Q : Type u} (s : Finset Q)
    (g : Q → B) (M : ℝ) (hM : 0 ≤ M) (hg : ∀ q ∈ s, ‖g q‖ ≤ M) :
    ‖∑ q ∈ s, g q‖ ≤ M := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hM
  | @insert q s hq ih =>
    rw [Finset.sum_insert hq]
    exact (hB _ _).trans (max_le (hg q (Finset.mem_insert_self _ _))
      (ih fun z hz ↦ hg z (Finset.mem_insert_of_mem hz)))

/-- Open normal quotient functions form precisely a linear subspace of `C(K, B)`.
Their normalized finite sums define a linear contraction, normalized on the unit
and invariant under both left and right translations. No completeness is assumed.
The `finsum` notation is an ordinary finite sum here: every quotient is finite.

Source: blueprint, `sec-six-functors-basics`, `sk-thm-sf-ctf-stability`,
direct-images proof, paragraph (3), auxiliary scalar tame-kernel analytic input;
agent-formulated auxiliary, exact literature reference WANTED
(blueprint: lem-sfb-finite-quotient-contractive-average).

Proof plan (the six steps of the DAG node):
1. Open cosets cover the compact group, so finitely many distinct cosets exhaust
   each quotient. The identity coset proves nonemptiness. The quotient topology
   is discrete, and the projection is continuous and surjective.
2. Intersect two open normal subgroups to put two functions on a common quotient.
   Addition and scalar multiplication then descend. Constants factor through the
   singleton quotient. Left and right translates factor through the same quotient.
3. For `V ≤ U`, multiplication by a lift of `q` bijects `U/V` with the fiber of
   `K/V → K/U` over `q`. Thus all fibers have size `m > 0`; both the quotient order
   and the pulled-back sum multiply by `m`. Characteristic zero, from the embedding
   of `Padic l` (def-weil-l-adic-numbers), permits cancellation and gives refinement.
4. Two representations agree after pullback to the intersection quotient, by
   surjectivity. Refinement makes their averages equal. Distributing finite sums
   on a common quotient proves linearity of the resulting map on the subspace.
5. Coprimality makes the quotient order have l-adic norm one, hence norm one in
   `B` by the isometric embedding. Induction using the ultrametric inequality
   bounds a finite sum by the maximum norm of its terms. Surjectivity of the
   projection identifies this maximum with the supremum norm of the function.
6. Left and right multiplication permute each quotient, so reindexing preserves
   its average. The average of one is `n⁻¹ * n = 1`. Explicit universes implement
   def-weil-size-convention. No limits or completeness are used. -/
theorem exists_finiteQuotientContractiveAverage
    (l : ℕ) [Fact l.Prime] (B : Type v) [NormedField B]
    [NormedAlgebra (Padic l) B]
    (_hB : IsNonarchimedean (norm : B → ℝ))
    (K : Type u) [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] [T2Space K]
    (_h_basis : ∀ W : Set K, IsOpen W → (1 : K) ∈ W →
      ∃ U : OpenNormalSubgroup K, (U : Set K) ⊆ W)
    (_h_order : ∀ U : OpenNormalSubgroup K,
      Nat.Coprime (Nat.card (K ⧸ U.toSubgroup)) l) :
    (∀ U : OpenNormalSubgroup K,
      Finite (K ⧸ U.toSubgroup) ∧ Nonempty (K ⧸ U.toSubgroup)) ∧
    ∃ D : Submodule B C(K, B),
      (∀ f : C(K, B), f ∈ D ↔
        ∃ (U : OpenNormalSubgroup K) (g : K ⧸ U.toSubgroup → B),
          ∀ k : K, f k = g (QuotientGroup.mk k)) ∧
      (∀ b : B, ContinuousMap.const K b ∈ D) ∧
      ∃ A : D →ₗ[B] B,
        (∀ (f : D) (U : OpenNormalSubgroup K) (g : K ⧸ U.toSubgroup → B),
          (∀ k : K, (f : C(K, B)) k = g (QuotientGroup.mk k)) →
          A f = (Nat.card (K ⧸ U.toSubgroup) : B)⁻¹ * ∑ᶠ q, g q) ∧
        (∀ (U V : OpenNormalSubgroup K) (hVU : V ≤ U) (g : K ⧸ U.toSubgroup → B),
          (Nat.card (K ⧸ V.toSubgroup) : B)⁻¹ *
              (∑ᶠ z, g (QuotientGroup.map V.toSubgroup U.toSubgroup (MonoidHom.id K) hVU z)) =
            (Nat.card (K ⧸ U.toSubgroup) : B)⁻¹ * ∑ᶠ q, g q) ∧
        (∀ f : D, ‖A f‖ ≤ ‖(f : C(K, B))‖) ∧
        (∀ f : D, (f : C(K, B)) = 1 → A f = 1) ∧
        (∀ (a : K) (f : D), ∃ fL fR : D,
          (∀ h : K, (fL : C(K, B)) h = (f : C(K, B)) (a * h)) ∧
          (∀ h : K, (fR : C(K, B)) h = (f : C(K, B)) (h * a)) ∧
          A fL = A f ∧ A fR = A f) := by
  classical
  let : CharZero B := charZero_of_injective_algebraMap (algebraMap (Padic l) B).injective
  have hfinite (U : OpenNormalSubgroup K) : Finite (K ⧸ U.toSubgroup) :=
    Subgroup.quotient_finite_of_isOpen U.toSubgroup U.toOpenSubgroup.isOpen
  let (U : OpenNormalSubgroup K) : Finite (K ⧸ U.toSubgroup) := hfinite U
  let rho (U V : OpenNormalSubgroup K) (h : V ≤ U) :=
    QuotientGroup.map V.toSubgroup U.toSubgroup (MonoidHom.id K) h
  have hrho (U V : OpenNormalSubgroup K) (h : V ≤ U) :
      Function.Surjective (rho U V h) := by
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨QuotientGroup.mk k, rfl⟩
  have href (U V : OpenNormalSubgroup K) (h : V ≤ U) (g : K ⧸ U.toSubgroup → B) :
      quotientAverage (fun z ↦ g (rho U V h z)) = quotientAverage g :=
    quotientAverage_comp (rho U V h) (hrho U V h) g
  let Utop : OpenNormalSubgroup K := ⟨⊤, by
    simpa only [OpenSubgroup.toSubgroup_top] using (Subgroup.normal_top (G := K))⟩
  let D : Submodule B C(K, B) :=
    { carrier := {f | ∃ (U : OpenNormalSubgroup K) (g : K ⧸ U.toSubgroup → B),
          ∀ k : K, f k = g (QuotientGroup.mk k)}
      zero_mem' := ⟨Utop, fun _ ↦ 0, fun _ ↦ rfl⟩
      add_mem' := by
        rintro f h ⟨U, g, hg⟩ ⟨V, j, hj⟩
        refine ⟨U ⊓ V, fun z ↦ g (rho U (U ⊓ V) inf_le_left z) +
          j (rho V (U ⊓ V) inf_le_right z), ?_⟩
        intro k
        exact congrArg₂ (· + ·) (hg k) (hj k)
      smul_mem' := by
        rintro b f ⟨U, g, hg⟩
        exact ⟨U, fun z ↦ b * g z, fun k ↦ congrArg (b * ·) (hg k)⟩ }
  have hconst (b : B) : ContinuousMap.const K b ∈ D :=
    ⟨Utop, fun _ ↦ b, fun _ ↦ rfl⟩
  have hind (f : C(K, B)) (U V : OpenNormalSubgroup K)
      (g : K ⧸ U.toSubgroup → B) (j : K ⧸ V.toSubgroup → B)
      (hg : ∀ k, f k = g (QuotientGroup.mk k))
      (hj : ∀ k, f k = j (QuotientGroup.mk k)) :
      quotientAverage g = quotientAverage j := by
    rw [← href U (U ⊓ V) inf_le_left, ← href V (U ⊓ V) inf_le_right]
    congr 1
    funext q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    exact (hg k).symm.trans (hj k)
  let A₀ (f : D) : B :=
    quotientAverage (Classical.choose (Classical.choose_spec f.property))
  have hformula (f : D) (U : OpenNormalSubgroup K) (g : K ⧸ U.toSubgroup → B)
      (hg : ∀ k, (f : C(K, B)) k = g (QuotientGroup.mk k)) :
      A₀ f = quotientAverage g :=
    hind f _ U _ g (Classical.choose_spec (Classical.choose_spec f.property)) hg
  let A : D →ₗ[B] B :=
    { toFun := A₀
      map_add' := by
        intro f h
        obtain ⟨U, g, hg⟩ := f.property
        obtain ⟨V, j, hj⟩ := h.property
        let g' := fun z ↦ g (rho U (U ⊓ V) inf_le_left z)
        let j' := fun z ↦ j (rho V (U ⊓ V) inf_le_right z)
        rw [hformula (f + h) (U ⊓ V) (g' + j') (fun k ↦
          congrArg₂ (· + ·) (hg k) (hj k)), quotientAverage_add,
          href U (U ⊓ V) inf_le_left, href V (U ⊓ V) inf_le_right,
          hformula f U g hg, hformula h V j hj]
      map_smul' := by
        intro b f
        obtain ⟨U, g, hg⟩ := f.property
        rw [hformula (b • f) U (b • g) (fun k ↦ congrArg (b * ·) (hg k)),
          quotientAverage_smul, hformula f U g hg]
        rfl }
  refine ⟨fun U ↦ ⟨hfinite U, inferInstance⟩, D, fun _ ↦ Iff.rfl, hconst, A,
    hformula, href, ?_, ?_, ?_⟩
  · intro f
    obtain ⟨U, g, hg⟩ := f.property
    change ‖A₀ f‖ ≤ ‖(f : C(K, B))‖
    rw [hformula f U g hg]
    have hn : ‖(Nat.card (K ⧸ U.toSubgroup) : B)‖ = 1 := by
      rw [← map_natCast (algebraMap (Padic l) B), norm_algebraMap']
      exact Padic.norm_natCast_eq_one_iff.mpr (_h_order U).symm
    rw [quotientAverage, norm_mul, norm_inv, hn, inv_one, one_mul]
    let := Fintype.ofFinite (K ⧸ U.toSubgroup)
    rw [finsum_eq_sum_of_fintype]
    apply nonarchimedean_sum_bound _hB _ _ _ (norm_nonneg _)
    intro q _
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← hg k]
    exact (f : C(K, B)).norm_coe_le_norm k
  · intro f hf
    change A₀ f = 1
    rw [hformula f Utop (fun _ ↦ 1) (fun k ↦ by rw [hf]; rfl)]
    exact quotientAverage_const 1
  · intro a f
    obtain ⟨U, g, hg⟩ := f.property
    let fL : C(K, B) := ⟨fun h ↦ (f : C(K, B)) (a * h),
      f.val.continuous.comp (continuous_const.mul continuous_id)⟩
    let fR : C(K, B) := ⟨fun h ↦ (f : C(K, B)) (h * a),
      f.val.continuous.comp (continuous_id.mul continuous_const)⟩
    let gL := fun q ↦ g (QuotientGroup.mk a * q)
    let gR := fun q ↦ g (q * QuotientGroup.mk a)
    have hL : ∀ k, fL k = gL (QuotientGroup.mk k) := by
      intro k
      simpa only [fL, coe_mk, gL, QuotientGroup.mk_mul] using hg (a * k)
    have hR : ∀ k, fR k = gR (QuotientGroup.mk k) := by
      intro k
      simpa only [fR, coe_mk, gR, QuotientGroup.mk_mul] using hg (k * a)
    refine ⟨⟨fL, U, gL, hL⟩, ⟨fR, U, gR, hR⟩, fun _ ↦ rfl, fun _ ↦ rfl, ?_, ?_⟩
    · change A₀ ⟨fL, _⟩ = A₀ f
      rw [hformula ⟨fL, _⟩ U gL hL, hformula f U g hg]
      unfold quotientAverage gL
      congr 1
      simpa only [Equiv.coe_mulLeft] using
        finsum_comp_equiv (Equiv.mulLeft (QuotientGroup.mk a)) (f := g)
    · change A₀ ⟨fR, _⟩ = A₀ f
      rw [hformula ⟨fR, _⟩ U gR hR, hformula f U g hg]
      unfold quotientAverage gR
      congr 1
      simpa only [Equiv.coe_mulRight] using
        finsum_comp_equiv (Equiv.mulRight (QuotientGroup.mk a)) (f := g)

end ContinuousMap
