/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q60
-/
module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Flat.Stability
import Sheaf.RingTheory.ProjectiveOfFlatOfNilpotentQuotient

/-!
# Projective short exact sequences at every adic quotient

Source: Stacks Project, Algebra, Tag 05D3, `lemma-split-completed-sequence`,
the quotient sequences and their projective last terms
(blueprint: lem-trf-adic-quotient-projective-short-exact).
-/

@[expose] public section

universe u vK vE vM

open scoped Pointwise

namespace Module

/-- A short exact sequence with flat last term and projective reduction modulo `I`
induces short exact sequences with projective last terms modulo every positive power of `I`.
The induced maps commute with the reduction maps as `R`-linear maps.
Source: Stacks Project, Algebra, Tag 05D3, `lemma-split-completed-sequence`
(blueprint: lem-trf-adic-quotient-projective-short-exact).

Proof plan:
1. Every linear map carries `I^n L` into `I^n L'`, by linearity on the generators
   `r • x`. This defines the quotient-ring-linear maps `LinearMap.reduceModIdeal`.
   The inclusions `I^(n+1) L ≤ I^n L` define `Submodule.factorPowSucc`.
2. By `lem-weil-pbc-flat-quotient-tensor-injective`, tensor the given short exact
   sequence with `R/I^n`. By clause (1) of `lem-weil-pbc-tensor-over-quotient-ring`,
   identify `(R/I^n) ⊗ L` with `L/I^n L` via `r ⊗ x ↦ [r • x]`.
   This identification respects `R/I^n` scalars and sends the tensor maps to the
   displayed quotient maps, as checked on `1 ⊗ x`. This gives the three exactness clauses.
3. By `lem-weil-pbc-flat-module-base-change`, `M/I^n M` is flat over `R/I^n`.
   Let `J` be the image of `I` in `R/I^n`. Then `J^n = 0`, and the natural
   identifications `(R/I^n)/J ≃ R/I` and `(M/I^n M)/J(M/I^n M) ≃ M/IM`
   preserve scalars, by their formulas on representatives. Apply
   `lem-trf-local-nilpotent-projective-flat-lift` to obtain projectivity over `R/I^n`.
4. On `[k]` the first two composites both give `[u k]`; on `[e]` the last two
   composites both give `[v e]`. Every class has a representative, proving both
   identities of `R`-linear maps. -/
theorem adic_quotient_projective_short_exact
    {R : Type u} [CommRing R] (I : Ideal R)
    {K : Type vK} [AddCommGroup K] [Module R K]
    {E : Type vE} [AddCommGroup E] [Module R E]
    {M : Type vM} [AddCommGroup M] [Module R M]
    (u : K →ₗ[R] E) (v : E →ₗ[R] M)
    (hu : Function.Injective u) (hv : Function.Surjective v)
    (hex : Function.Exact u v) [Module.Flat R M]
    [Module.Projective (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M)))] :
    ∀ n : ℕ, 1 ≤ n →
      Function.Injective (u.reduceModIdeal (I ^ n)) ∧
      Function.Surjective (v.reduceModIdeal (I ^ n)) ∧
      Function.Exact (u.reduceModIdeal (I ^ n)) (v.reduceModIdeal (I ^ n)) ∧
      Module.Projective (R ⧸ I ^ n) (M ⧸ (I ^ n • (⊤ : Submodule R M))) ∧
      (Submodule.factorPowSucc I E n).comp
          ((u.reduceModIdeal (I ^ (n + 1))).restrictScalars R) =
        ((u.reduceModIdeal (I ^ n)).restrictScalars R).comp
          (Submodule.factorPowSucc I K n) ∧
      (Submodule.factorPowSucc I M n).comp
          ((v.reduceModIdeal (I ^ (n + 1))).restrictScalars R) =
        ((v.reduceModIdeal (I ^ n)).restrictScalars R).comp
          (Submodule.factorPowSucc I E n) := by
  sorry

end Module
