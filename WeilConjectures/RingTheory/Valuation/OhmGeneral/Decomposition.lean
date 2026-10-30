/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Invariant.Profinite
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.Valuation.Basic

/-!
# Galois actions on integral closures inside a separably closed field

Let `Ω` be separably closed and separable over a subfield `F`, and `R ⊆ F` a subring.

- `integralClosureMulSemiringAction`: `Gal(Ω/F)` acts on the integral closure of `R` in `Ω`.
- `Algebra.IsInvariant.exists_smul_of_under_eq_of_stabilizer`: the stabiliser of `a ∈ Ω` acts
  transitively on the primes of the integral closure lying over a given prime of its fixed points.
-/

@[expose] public section

open scoped Pointwise

variable {Ω : Type*} [Field Ω] {F : Subfield Ω}

/-- A separably closed field which is separable over `F` is Galois over `F`. -/
lemma IsSepClosed.isGalois_of_isSeparable [IsSepClosed Ω] [Algebra.IsSeparable F Ω] :
    IsGalois F Ω :=
  have : IsSepClosure F Ω := ⟨inferInstance, inferInstance⟩
  inferInstance

/-- Automorphisms of `Ω` over `F` preserve integrality over subrings of `F`. -/
lemma IsIntegral.algEquiv_apply {R : Subring Ω} (hR : R ≤ F.toSubring) (σ : Ω ≃ₐ[F] Ω) {b : Ω}
    (hb : IsIntegral R b) : IsIntegral R (σ b) :=
  hb.map ({ σ.toRingHom with commutes' := fun r ↦ σ.commutes ⟨r, hR r.2⟩ } : Ω →ₐ[R] Ω)

/-- `Gal(Ω/F)` acts on the integral closure in `Ω` of a subring `R ⊆ F`. -/
@[implicit_reducible]
def integralClosureMulSemiringAction {R : Subring Ω} (hR : R ≤ F.toSubring) :
    MulSemiringAction (Ω ≃ₐ[F] Ω) (integralClosure R Ω) where
  smul σ b := ⟨σ b, IsIntegral.algEquiv_apply hR σ b.2⟩
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero σ := Subtype.ext (map_zero σ)
  smul_add σ _ _ := Subtype.ext (map_add σ _ _)
  smul_one σ := Subtype.ext (map_one σ)
  smul_mul σ _ _ := Subtype.ext (map_mul σ _ _)

/-- **Transitivity for the stabiliser of an element.** Let `Ω` be separably closed and separable
over `F`, `R ⊆ F`, `B` the integral closure of `R` in `Ω` and `H ⊆ Gal(Ω/F)` the stabiliser of
`a ∈ Ω`. If `P` is a maximal and `Q` a prime ideal of `B` whose contractions to the `H`-invariants
of `B` satisfy `P ∩ Bᴴ ⊆ Q ∩ Bᴴ`, then `P` and `Q` are conjugate under `H`. -/
theorem exists_smul_of_under_eq_of_stabilizer [IsSepClosed Ω] [Algebra.IsSeparable F Ω]
    {R : Subring Ω} (hR : R ≤ F.toSubring) (a : Ω) (P Q : Ideal (integralClosure R Ω))
    [P.IsMaximal] [Q.IsPrime]
    (hPQ : ∀ b : integralClosure R Ω, (∀ σ : Ω ≃ₐ[F] Ω, σ a = a → σ b = b) → b ∈ P → b ∈ Q) :
    ∃ g : Ω ≃ₐ[F] Ω, g a = a ∧ ∀ b : integralClosure R Ω,
      b ∈ Q ↔ (⟨g⁻¹ b, IsIntegral.algEquiv_apply hR g⁻¹ b.2⟩ : integralClosure R Ω) ∈ P := by
  let := integralClosureMulSemiringAction hR
  let : TopologicalSpace (integralClosure R Ω) := ⊥
  have : DiscreteTopology (integralClosure R Ω) := ⟨rfl⟩
  have := IsSepClosed.isGalois_of_isSeparable (F := F) (Ω := Ω)
  set H := MulAction.stabilizer (Ω ≃ₐ[F] Ω) a
  have : CompactSpace H := isCompact_iff_compactSpace.1
    (Subgroup.isClosed_of_isOpen _ (stabilizer_isOpen_of_isIntegral a)).isCompact
  have : ContinuousSMul H (integralClosure R Ω) := by
    refine continuousSMul_iff_stabilizer_isOpen.2 fun b ↦ ?_
    have := (stabilizer_isOpen_of_isIntegral (K := F) (b : Ω)).preimage
      (continuous_subtype_val (p := (· ∈ H)))
    convert this using 1
    ext g
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff, Set.mem_preimage]
    exact Subtype.ext_iff
  let A := FixedPoints.subring (integralClosure R Ω) H
  have : Algebra.IsInvariant A (integralClosure R Ω) H :=
    ⟨fun b hb ↦ ⟨⟨b, hb⟩, rfl⟩⟩
  have hPQ' : P.under A = Q.under A := by
    have := Algebra.IsInvariant.isIntegral_of_profinite (A := A) (B := integralClosure R Ω) (G := H)
    refine Ideal.IsMaximal.eq_of_le (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P)
      (inferInstance : (Q.under A).IsPrime).ne_top ?_
    rintro ⟨b, hb⟩ hbP
    exact hPQ b (fun σ hσ ↦ congrArg Subtype.val (hb ⟨σ, hσ⟩)) hbP
  obtain ⟨g, hg⟩ :=
    Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite (A := A) (G := H) P Q hPQ'
  refine ⟨g, g.2, fun b ↦ ?_⟩
  rw [hg, Ideal.pointwise_smul_eq_comap, Ideal.mem_comap]
  rfl

/-- If every element of a multiset has valuation `< g`, so does its sum. -/
lemma Valuation.map_multiset_sum_lt {K Γ : Type*} [Ring K] [LinearOrderedCommMonoidWithZero Γ]
    (v : Valuation K Γ) {g : Γ} (hg : g ≠ 0) (s : Multiset K) (hs : ∀ y ∈ s, v y < g) :
    v s.sum < g := by
  induction s using Multiset.induction_on with
  | empty => simpa [zero_lt_iff] using hg
  | cons y s ih =>
    rw [Multiset.sum_cons]
    exact v.map_add_lt (hs y (Multiset.mem_cons_self y s))
      (ih fun z hz ↦ hs z (Multiset.mem_cons_of_mem hz))

/-- **Sum of conjugates.** Let `Ω` be separably closed and separable over `F`, `R ⊆ F` and `x`
integral over `R` such that every conjugate `σ x ≠ x` has `v (σ x) < 1`. Then the sum of the
conjugates of `x` is an element `c ∈ F`, integral over `R`, with `v (c - x) < 1`. -/
theorem exists_mem_isIntegral_valuation_sub_lt_one [IsSepClosed Ω] [Algebra.IsSeparable F Ω]
    {R : Subring Ω} (hR : R ≤ F.toSubring) {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation Ω Γ) {x : Ω} (hx : IsIntegral R x)
    (hconj : ∀ σ : Ω ≃ₐ[F] Ω, σ x ≠ x → v (σ x) < 1) :
    ∃ c ∈ F, IsIntegral R c ∧ v (c - x) < 1 := by
  classical
  have := IsSepClosed.isGalois_of_isSeparable (F := F) (Ω := Ω)
  set f := (minpoly F x).map (algebraMap F Ω)
  have hsep : f.Separable := Polynomial.Separable.map (Algebra.IsSeparable.isSeparable F x)
  have hspl : f.Splits := IsSepClosed.splits_of_separable f hsep
  have hroot (y : Ω) (hy : y ∈ f.roots) : ∃ σ : Ω ≃ₐ[F] Ω, σ x = y := by
    rw [Polynomial.mem_roots_map (minpoly.ne_zero (Algebra.IsIntegral.isIntegral x))] at hy
    have := minpoly.eq_of_irreducible_of_monic
      (minpoly.irreducible (Algebra.IsIntegral.isIntegral x)) hy
      (minpoly.monic (Algebra.IsIntegral.isIntegral x))
    exact (Normal.minpoly_eq_iff_mem_orbit Ω).1 this.symm
  have hx0 : x ∈ f.roots := by
    rw [Polynomial.mem_roots_map (minpoly.ne_zero (Algebra.IsIntegral.isIntegral x))]
    exact minpoly.aeval F x
  refine ⟨f.roots.sum, ?_, ?_, ?_⟩
  · rw [← neg_neg f.roots.sum, ← hspl.nextCoeff_eq_neg_sum_roots_of_monic
      ((minpoly.monic (Algebra.IsIntegral.isIntegral x)).map _),
      Polynomial.nextCoeff_map (algebraMap F Ω).injective]
    exact F.neg_mem (Subtype.mem _)
  · refine multiset_sum_mem (S := integralClosure R Ω) _ fun y hy ↦ ?_
    obtain ⟨σ, rfl⟩ := hroot y hy
    exact IsIntegral.algEquiv_apply hR σ hx
  · rw [← Multiset.sum_erase hx0, add_sub_cancel_left]
    have hlt (y : Ω) (hy : y ∈ f.roots.erase x) : v y < 1 := by
      obtain ⟨hyx, hy⟩ := (Polynomial.nodup_roots hsep).mem_erase_iff.1 hy
      obtain ⟨σ, rfl⟩ := hroot y hy
      exact hconj σ hyx
    exact Valuation.map_multiset_sum_lt v one_ne_zero _ hlt
