/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.RingTheory.Regular.Flat
public import Mathlib.RingTheory.Smooth.Fiber
public import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
public import WeilConjectures.RingTheory.Purity.FreeOfRegularPair
public import WeilConjectures.RingTheory.Purity.NormalRegularPair
public import WeilConjectures.RingTheory.Purity.UnramifiedOfRegularPair
public import WeilConjectures.RingTheory.RegularLocalRing.IsRegularRing

/-!
# Zariski–Nagata purity of the branch locus

Let `(A, 𝔪)` be a regular local ring of dimension `d ≥ 2` and `A ⊆ B` a finite extension with
`B` an integrally closed domain. If `A → B` is étale at every prime of `B` not lying over `𝔪`,
then `A → B` is étale ([Stacks 0BMA], `Algebra.Etale.of_isRegularLocalRing`). This is an input of
blueprint `sbc-thm-spreading-finite-etale-galois` (through [Stacks 0EYE]).

We require `B` to be a domain containing `A` (`FaithfulSMul A B`): for `B = A × κ` with `κ` the
residue field, `B` is normal and étale over the punctured spectrum but not étale over `A`.

## Dimension two (`Algebra.Etale.of_isRegularLocalRing_of_ringKrullDim_eq_two`)

Let `𝔪 = (x, y)`.
1. `[x, y]` is a regular sequence on `B`: by going down the maximal ideals of `B` have height `≥ 2`,
   so they are not associated to `B / xB` as `B` is normal
   (`IsIntegrallyClosed.isWeaklyRegular_pair_of_isIntegral`).
2. Hence `B` is a free `A`-module (`Module.free_of_isWeaklyRegular_of_maximalIdeal_eq_span_pair`),
   and `[x, y]` is regular on `B ⊗[A] B`.
3. `B` is unramified over `A` on `D(x) ∪ D(y)`, and the separability idempotents glue across the
   regular pair (`Algebra.FormallyUnramified.of_isWeaklyRegular_tensorProduct`); being flat, `B`
   is étale over `A`.

## Higher dimension (`IsRegularLocalRing.hasPurityOfBranchLocus`)

By induction on `d`, choosing `f ∈ 𝔪 \ 𝔪²`, so that `A ⧸ (f)` is regular of dimension `d - 1`, and
using the reduction step [Stacks 0BLS] (`IsRegularLocalRing.hasPurityOfBranchLocus_of_quotient`),
which is not formalized yet: its proof needs the Lefschetz-type comparison of finite étale covers
of the punctured spectrum of `A` with those of the formal completion along `V(f)` [Stacks 0BLM],
using `H¹_𝔪(A) = H²_𝔪(A) = 0`, and the henselian pair `(Â, fÂ)`.
-/

@[expose] public section

universe u v

open IsLocalRing RingTheory.Sequence

/-- **Zariski–Nagata purity in dimension two** [Stacks 0BMA]. Let `(A, 𝔪)` be a regular local ring
of dimension two and `A ⊆ B` a finite extension by an integrally closed domain `B` which is étale
at every prime of `B` not lying over `𝔪`. Then `B` is étale over `A`. -/
theorem Algebra.Etale.of_isRegularLocalRing_of_ringKrullDim_eq_two {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [Algebra A B] [IsRegularLocalRing A] (hd : ringKrullDim A = 2)
    [Module.Finite A B] [IsDomain B] [IsIntegrallyClosed B] [FaithfulSMul A B]
    (h : ∀ (Q : Ideal B) [Q.IsPrime], Q.comap (algebraMap A B) ≠ maximalIdeal A →
      Algebra.IsEtaleAt A Q) :
    Algebra.Etale A B := by
  have : IsNoetherianRing B := isNoetherian_of_tower A inferInstance
  -- a regular system of parameters `x, y`
  obtain ⟨rs, hreg, hspan, hlen⟩ := IsRegularLocalRing.exists_isRegular_ofList_eq_maximalIdeal A
  have hlen2 : rs.length = 2 := by
    have := IsRegularLocalRing.spanFinrank_maximalIdeal (R := A)
    rw [hd] at this
    rw [hlen]
    exact_mod_cast this
  obtain ⟨x, y, rfl⟩ := List.length_eq_two.1 hlen2
  have hm : maximalIdeal A = Ideal.span {x, y} := by
    rw [← hspan, Ideal.ofList]
    congr 1
    ext
    simp
  have hx : x ≠ 0 := by
    rintro rfl
    have h0 := hreg.toIsWeaklyRegular
    rw [isWeaklyRegular_cons_iff] at h0
    exact one_ne_zero (h0.1 (show (0 : A) • (1 : A) = (0 : A) • 0 by simp))
  have h2 : 2 ≤ (maximalIdeal A).height := by
    have : ((maximalIdeal A).height : WithBot ℕ∞) = 2 := by
      rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim, hd]
    have h' : ((2 : ℕ∞) : WithBot ℕ∞) ≤ (maximalIdeal A).height := by
      rw [this]; norm_num
    exact WithBot.coe_le_coe.1 h'
  -- `[x, y]` is regular on `B`, so `B` is free
  have hregB : IsWeaklyRegular B [x, y] :=
    IsIntegrallyClosed.isWeaklyRegular_pair_of_isIntegral hx (by rw [hm]; exact Ideal.le_radical)
      h2
  have : Module.Free A B := Module.free_of_isWeaklyRegular_of_maximalIdeal_eq_span_pair hm hregB
  -- `[x, y]` is regular on `B ⊗[A] B`
  have hregF : IsWeaklyRegular (R := A) (TensorProduct A B B) [x, y] :=
    (isWeaklyRegular_map_algebraMap_iff B (TensorProduct A B B) [x, y]).1
      (IsWeaklyRegular.of_flat_of_isBaseChange (TensorProduct.isBaseChange A B B) hregB)
  have hxB : IsSMulRegular B x := by
    rw [isWeaklyRegular_cons_iff] at hregB
    exact hregB.1
  -- `B` is unramified over `D(x)` and `D(y)`
  have hunr : ∀ t ∈ maximalIdeal A, ∀ (Q : Ideal B) [Q.IsPrime], algebraMap A B t ∉ Q →
      Algebra.IsUnramifiedAt A Q := by
    intro t ht Q _ htQ
    have : Q.comap (algebraMap A B) ≠ maximalIdeal A := fun heq ↦ htQ (by
      rw [← heq] at ht
      exact ht)
    have := h Q this
    infer_instance
  have hxm : x ∈ maximalIdeal A := hm ▸ Ideal.subset_span (by simp)
  have hym : y ∈ maximalIdeal A := hm ▸ Ideal.subset_span (by simp)
  have : Algebra.FormallyUnramified A B :=
    Algebra.FormallyUnramified.of_isWeaklyRegular_tensorProduct hregF hxB (hunr x hxm)
      (hunr y hym)
  have : Algebra.FinitePresentation A B := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact Algebra.Etale.of_formallyUnramified_of_flat

/-- A local ring `A` has **purity of the branch locus** (for normal domains in universe `v`) if
every finite extension `A ⊆ B` by an integrally closed domain `B` which is étale over the punctured
spectrum of `A` is étale. -/
def IsLocalRing.HasPurityOfBranchLocus (A : Type u) [CommRing A] [IsLocalRing A] : Prop :=
  ∀ (B : Type v) [CommRing B] [Algebra A B] [Module.Finite A B] [IsDomain B]
    [IsIntegrallyClosed B] [FaithfulSMul A B],
    (∀ (Q : Ideal B) [Q.IsPrime], Q.comap (algebraMap A B) ≠ maximalIdeal A →
      Algebra.IsEtaleAt A Q) → Algebra.Etale A B

/-- **Reduction step for purity** [Stacks 0BLS]. Let `(A, 𝔪)` be a regular local ring of dimension
at least three and `f ∈ 𝔪 \ 𝔪²`, so that `A ⧸ (f)` is a regular local ring of dimension
`dim A - 1 ≥ 2`. If `A ⧸ (f)` has purity of the branch locus, so does `A`.

Not formalized yet. Stacks' proof: given `A ⊆ B` étale over the punctured spectrum `U`, restrict
`V = Spec B ×_X U → U` to `U₀ = U ∩ V(f)`; by purity for `A ⧸ (f)` (via [Stacks 0BLR], `A ⧸ (f)`
being normal) it extends to a finite étale cover of `Spec (A ⧸ f)`, which lifts to the completion
`Â` along the henselian pair `(Â, fÂ)`; since `depth A ≥ 3`, i.e. `H¹_𝔪(A) = H²_𝔪(A) = 0`,
finite étale covers of `U` and of the formal completion of `U` along `U₀` agree
([Stacks 0BLM], [Stacks 0BL8]), so `V` extends to a finite étale cover of `Spec A`, which is
`Spec B` as `B` is normal. -/
theorem IsRegularLocalRing.hasPurityOfBranchLocus_of_quotient {A : Type u} [CommRing A]
    [IsRegularLocalRing A] (hd : 3 ≤ ringKrullDim A) {f : A} (hf : f ∈ maximalIdeal A)
    (hf2 : f ∉ maximalIdeal A ^ 2) [IsLocalRing (A ⧸ Ideal.span {f})]
    (h : HasPurityOfBranchLocus.{u, v} (A ⧸ Ideal.span {f})) :
    HasPurityOfBranchLocus.{u, v} A := by
  sorry

/-- **Zariski–Nagata purity** [Stacks 0BMA], by induction on the dimension `n + 2`. -/
theorem IsRegularLocalRing.hasPurityOfBranchLocus :
    ∀ (n : ℕ) (A : Type u) [CommRing A] [IsRegularLocalRing A],
      ringKrullDim A = (n + 2 : ℕ) → HasPurityOfBranchLocus.{u, v} A
  | 0, A, _, _, hd => fun _ _ _ _ _ _ _ h ↦
    Algebra.Etale.of_isRegularLocalRing_of_ringKrullDim_eq_two (by exact_mod_cast hd) h
  | n + 1, A, _, _, hd => by
    set m := maximalIdeal A
    have hne : m ≠ ⊥ := by
      intro h0
      have := IsRegularLocalRing.spanFinrank_maximalIdeal (R := A)
      rw [hd] at this
      have h' : (maximalIdeal A).spanFinrank = n + 1 + 2 := by exact_mod_cast this
      rw [show maximalIdeal A = ⊥ from h0, Submodule.spanFinrank_bot] at h'
      omega
    obtain ⟨f, hfm, hf2⟩ : ∃ f ∈ m, f ∉ m ^ 2 := by
      by_contra! hle
      exact hne (Submodule.eq_bot_of_le_smul_of_le_jacobson_bot m m m.fg_of_isNoetherianRing
        (by rwa [smul_eq_mul, ← pow_two]) (by rw [jacobson_eq_maximalIdeal ⊥ bot_ne_top]))
    obtain ⟨_, _, hrank⟩ := IsRegularLocalRing.quotient_span_singleton hfm hf2
    refine hasPurityOfBranchLocus_of_quotient ?_ hfm hf2
      (hasPurityOfBranchLocus n (A ⧸ Ideal.span {f}) ?_)
    · rw [hd]
      exact_mod_cast (show 3 ≤ n + 1 + 2 by omega)
    · have h1 := IsRegularLocalRing.spanFinrank_maximalIdeal (R := A)
      have h2 := IsRegularLocalRing.spanFinrank_maximalIdeal (R := A ⧸ Ideal.span {f})
      rw [hd, ← hrank] at h1
      rw [← h2]
      have : (maximalIdeal (A ⧸ Ideal.span {f})).spanFinrank + 1 = n + 1 + 2 := by
        exact_mod_cast h1
      exact_mod_cast (show (maximalIdeal (A ⧸ Ideal.span {f})).spanFinrank = n + 2 by omega)

/-- **Zariski–Nagata purity of the branch locus** [Stacks 0BMA]. Let `(A, 𝔪)` be a regular local
ring of dimension at least two and `A ⊆ B` a finite extension by an integrally closed domain `B`
which is étale at every prime of `B` not lying over `𝔪`. Then `B` is étale over `A`.

This is an input of blueprint `sbc-thm-spreading-finite-etale-galois` (through [Stacks 0EYE]).
In dimension two the proof is complete; in higher dimension it depends on the reduction step
`IsRegularLocalRing.hasPurityOfBranchLocus_of_quotient` ([Stacks 0BLS]). -/
theorem Algebra.Etale.of_isRegularLocalRing {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [Algebra A B] [IsRegularLocalRing A] (hd : 2 ≤ ringKrullDim A) [Module.Finite A B]
    [IsDomain B] [IsIntegrallyClosed B] [FaithfulSMul A B]
    (h : ∀ (Q : Ideal B) [Q.IsPrime], Q.comap (algebraMap A B) ≠ maximalIdeal A →
      Algebra.IsEtaleAt A Q) :
    Algebra.Etale A B := by
  have h1 := IsRegularLocalRing.spanFinrank_maximalIdeal (R := A)
  set k := (maximalIdeal A).spanFinrank
  rw [← h1] at hd
  have hk : 2 ≤ k := by exact_mod_cast hd
  obtain ⟨n, hn⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
  rw [hn] at h1
  exact IsRegularLocalRing.hasPurityOfBranchLocus n A h1.symm B h
