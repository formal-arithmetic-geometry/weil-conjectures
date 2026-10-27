/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Nakayama

/-!
# Completed prefix multiplication kernels

Source: Stacks Project, algebra.tex, Tags 00MA, 00MB, 05GG, 00DV and 00LF
(blueprint: lem-trf-completion-prefix-kernel-comparison).

## Main definitions

* `AdicCompletion.prefixMultiplication`: multiplication on a prefix quotient.
* `AdicCompletion.prefixQuotientEquiv`: the canonical completed quotient identification.
* `AdicCompletion.completedPrefixMultiplication`: multiplication on the extended quotient.

## Main statements

* `AdicCompletion.completionPrefixKernelComparison`: kernel comparison, zero-kernel
  reflection, and preservation and reflection of regularity, including the empty list.
-/

@[expose] public section

universe u

namespace AdicCompletion

/-- Multiplication by the next entry on `R/(f₁,…,fᵢ)`.

Source: Stacks Project, algebra.tex, Tag 00LF, the prefix nonzerodivisor tests
(blueprint: lem-trf-completion-prefix-kernel-comparison). -/
def prefixMultiplication {R : Type u} [CommRing R] (fs : List R) (i : Fin fs.length) :
    (R ⧸ Ideal.ofList (fs.take i)) →ₗ[R] (R ⧸ Ideal.ofList (fs.take i)) :=
  LinearMap.lsmul R (R ⧸ Ideal.ofList (fs.take i)) fs[i]

/-- The canonical isomorphism from the completion of a prefix quotient to the quotient
of the completion by the extended prefix ideal. It is the inverse of the canonical
tensor-to-completion map followed by `s ⊗ r̄ ↦ s c(r)` modulo the extended ideal.

Source: Stacks Project, algebra.tex, Tag 00MA (3), specialized to a cyclic quotient
(blueprint: lem-trf-completion-prefix-kernel-comparison). -/
noncomputable def prefixQuotientEquiv (R : Type u) [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] (fs : List R) (i : ℕ) :
    AdicCompletion (IsLocalRing.maximalIdeal R) (R ⧸ Ideal.ofList (fs.take i)) ≃ₗ[
      AdicCompletion (IsLocalRing.maximalIdeal R) R]
      (AdicCompletion (IsLocalRing.maximalIdeal R) R ⧸
        (Ideal.ofList (fs.take i)).map
          (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))) :=
  (ofTensorProductEquivOfFiniteNoetherian (IsLocalRing.maximalIdeal R)
    (R ⧸ Ideal.ofList (fs.take i))).symm.trans
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot
        (AdicCompletion (IsLocalRing.maximalIdeal R) R)
        (Ideal.ofList (fs.take i))).symm.toLinearEquiv

/-- Multiplication by the completed next entry on `S/PᵢS`, for `S` the completion of `R`.

Source: Stacks Project, algebra.tex, Tag 00MA (3), its naturality for multiplication
(blueprint: lem-trf-completion-prefix-kernel-comparison). -/
noncomputable def completedPrefixMultiplication {R : Type u} [CommRing R] [IsLocalRing R]
    (fs : List R) (i : Fin fs.length) :
    (AdicCompletion (IsLocalRing.maximalIdeal R) R ⧸
      (Ideal.ofList (fs.take i)).map
        (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))) →ₗ[
          AdicCompletion (IsLocalRing.maximalIdeal R) R]
    (AdicCompletion (IsLocalRing.maximalIdeal R) R ⧸
      (Ideal.ofList (fs.take i)).map
        (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))) :=
  LinearMap.lsmul (AdicCompletion (IsLocalRing.maximalIdeal R) R) _
    (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R) fs[i])

/-- Completion identifies every prefix multiplication kernel with the corresponding
kernel over the completed ring, detects its vanishing, and preserves and reflects
regularity of lists in the maximal ideal, including the empty list.

Source: Stacks Project, algebra.tex, Tags 00MB (2), 00MA (3), 05GG (2), 00DV (2),
05GI (1), and 00LF (blueprint: lem-trf-completion-prefix-kernel-comparison).

Proof:
1. For each prefix quotient `M`, put `K = ker(f : M → M)`, `J = fM`, and `C = M/J`.
   The cyclic modules `M,C` are finite, and `K,J` are finite by
   `lem-weil-pbc-noetherian-submodule-finite`. The maps give short exact sequences
   `0 → K → M → J → 0` and `0 → J → M → C → 0`, without assuming regularity.
2. By `lem-weil-pbc-completion-finite-module-tensor`, the canonical completion
   comparison identifies `M̂` with `S ⊗[R] M`. The balanced map `s ⊗ r̄ ↦ s c(r)`
   modulo `P S` has inverse `s̄ ↦ s ⊗ 1`. Their composites are identities on quotient
   representatives and pure tensors. Naturality sends completed multiplication to
   multiplication by `c(f)`. These are exactly the maps defining `prefixQuotientEquiv`.
3. Apply `lem-weil-pbc-completion-exact-finite-modules` to both short exact sequences.
   The completed inclusion of `K` is injective; its image is the kernel of `M̂ → Ĵ`.
   Since `Ĵ → M̂` is injective, this is also the kernel of their composite, completed
   multiplication. Step 2 transports that kernel to the asserted quotient of `S`.
4. By `lem-weil-pbc-module-completion-complete` at `n=1`, zero completion of `K`
   implies `K/mK=0`. Since `K` is finite and `m` is the Jacobson radical,
   `lem-weil-pbc-nakayama-jacobson` gives `K=0`. Conversely a zero module has zero
   completion since all its quotient modules are zero.
5. The prefix injectivity tests are thus equivalent. The final prefix ideals lie
   in `m` and `mS`, respectively. By `lem-weil-pbc-local-completion-local-ring`,
   `mS` is maximal; both final quotients are nonzero. The definition
   `def-weil-pbc-regular-sequence` now gives regularity equivalence. For the empty
   list there are no prefix tests, and both final quotients are the nonzero local rings.
-/
theorem completionPrefixKernelComparison {R : Type u} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (fs : List R)
    (hfs : ∀ f ∈ fs, f ∈ IsLocalRing.maximalIdeal R) :
    (∀ i : Fin fs.length,
      Function.Injective
        (map (IsLocalRing.maximalIdeal R) (prefixMultiplication fs i).ker.subtype) ∧
      LinearMap.range
          ((prefixQuotientEquiv R fs i).toLinearMap.comp
            (map (IsLocalRing.maximalIdeal R) (prefixMultiplication fs i).ker.subtype)) =
        (completedPrefixMultiplication fs i).ker ∧
      (prefixQuotientEquiv R fs i).toLinearMap.comp
          (map (IsLocalRing.maximalIdeal R) (prefixMultiplication fs i)) =
        (completedPrefixMultiplication fs i).comp
          (prefixQuotientEquiv R fs i).toLinearMap ∧
      (Subsingleton (AdicCompletion (IsLocalRing.maximalIdeal R)
          (prefixMultiplication fs i).ker) ↔
        Subsingleton (prefixMultiplication fs i).ker)) ∧
    (RingTheory.Sequence.IsRegular R fs ↔
      RingTheory.Sequence.IsRegular (AdicCompletion (IsLocalRing.maximalIdeal R) R)
        (fs.map (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)))) := by
  sorry

end AdicCompletion
