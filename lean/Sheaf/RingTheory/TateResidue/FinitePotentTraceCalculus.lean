/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.RingTheory.TateResidue.FinitePotent
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Trace

/-!
# Trace calculus for finite-potent endomorphisms

Source: J. Tate, *Residues of differentials on curves*, §1, pp. 149–150, (T1)–(T5),
with (T4) specialized to pairwise products of finite rank
(blueprint: lem-pc-finite-potent-trace-calculus).

The finite-potency predicate and the canonical scalar are the existing
`Module.End.IsFinitePotent` and `Module.End.tateTrace`. This statement includes
finite potency of the restrictions, quotients, cyclic composites and finite sums,
in addition to the trace identities.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace Module.End

/-- Trace calculus on arbitrary-dimensional vector spaces over any field.
Source: Tate, *Residues of differentials on curves*, §1, pp. 149–150, (T1)–(T5)
(blueprint: lem-pc-finite-potent-trace-calculus).

Proof plan, following the seven steps of the node:
1. For finite-potent `T`, choose `n` with finite-dimensional `U₀ = range (T ^ n)`.
   This subspace is stable since powers commute with `T`; take its ordinary trace
   (`def-weil-finite-dimensional-subspace`, `def-weil-endomorphism-trace`).
2. For another permitted `U` containing `range (T ^ N)`, put `m = max n N` and
   `R = range (T ^ m)`. Both `U₀/R` and `U/R` have nilpotent induced operator.
   Apply `lem-pc-finite-dimensional-trace-exact` and
   `lem-pc-finite-dimensional-nilpotent-trace` to their exact sequences with `R`.
   The two traces equal the trace on `R`, proving independence and uniqueness.
   The existing construction `tateTrace` makes the same choice with the least `n`.
3. Take `U = V` for a finite-dimensional space, and `U = 0` for a nilpotent map.
   Its zero-space trace is the empty diagonal sum (`def-weil-endomorphism-trace`).
4. For stable `L`, put `A = U₀ ∩ L` and `B = q(U₀)` in `V/L`. These are finite
   dimensional, stable, and contain the respective nth power images. This proves
   both finite-potency conclusions. The sequence `0 → A → U₀ → B → 0` is exact;
   `lem-pc-finite-dimensional-trace-exact` and step 2 give trace additivity.
5. The same `U₀` is stable under `cT` and contains its nth power image because
   `(cT)^n = c^n T^n`. The diagonal entries on `U₀` scale by `c`, proving scalar
   linearity (`def-weil-endomorphism-trace`), including `c = 0`.
6. For `ba`, take `A = range ((ba)^n)` and `B = a(A)`. The identity
   `(ab)^(n+1) = a (ba)^n b` gives finite potency of `ab`. The restricted maps
   between finite-dimensional `A` and `B` have composites the restricted `ba, ab`.
   Apply `lem-pc-finite-dimensional-trace-cyclic` and then step 2.
7. For a finite family take `U = Σᵢⱼ range (Tᵢ Tⱼ)`. It is finite dimensional
   and stable under every `Tₗ` since `Tₗ Tᵢ Tⱼ x ∈ range (Tₗ Tᵢ)`.
   Both `Tᵢ²(V)` and `(Σᵢ Tᵢ)²(V)` lie in `U`, proving finite potency.
   All traces are computed on `U`; their sum identity follows by adding diagonal
   entries (`def-weil-endomorphism-trace`). The empty family gives `U = 0`.
-/
theorem finitePotent_trace_calculus (k : Type u) [Field k] (V : Type v)
    [AddCommGroup V] [Module k V] :
    (∀ (T : Module.End k V), T.IsFinitePotent →
      ∀ (U : Submodule k V), FiniteDimensional k U →
        ∀ (hU : ∀ x ∈ U, T x ∈ U) (N : ℕ), 1 ≤ N →
          LinearMap.range (T ^ N) ≤ U →
            T.tateTrace = LinearMap.trace k U (T.restrict hU)) ∧
    (∀ (T : Module.End k V), T.IsFinitePotent →
      ∃! t : k, ∀ (U : Submodule k V), FiniteDimensional k U →
        ∀ (hU : ∀ x ∈ U, T x ∈ U) (N : ℕ), 1 ≤ N →
          LinearMap.range (T ^ N) ≤ U →
            t = LinearMap.trace k U (T.restrict hU)) ∧
    (∀ [FiniteDimensional k V] (T : Module.End k V),
      T.tateTrace = LinearMap.trace k V T) ∧
    (∀ (T : Module.End k V), IsNilpotent T → T.IsFinitePotent ∧ T.tateTrace = 0) ∧
    (∀ (T : Module.End k V), T.IsFinitePotent →
      ∀ (L : Submodule k V) (hL : ∀ x ∈ L, T x ∈ L),
        IsFinitePotent (T.restrict hL) ∧ IsFinitePotent (L.mapQ L T hL) ∧
          T.tateTrace = tateTrace (T.restrict hL) + tateTrace (L.mapQ L T hL)) ∧
    (∀ (T : Module.End k V), T.IsFinitePotent → ∀ c : k,
      (c • T).IsFinitePotent ∧ (c • T).tateTrace = c * T.tateTrace) ∧
    (∀ (W : Type w) [AddCommGroup W] [Module k W]
      (a : V →ₗ[k] W) (b : W →ₗ[k] V),
        IsFinitePotent (b ∘ₗ a) → IsFinitePotent (a ∘ₗ b) ∧
          tateTrace (b ∘ₗ a) = tateTrace (a ∘ₗ b)) ∧
    (∀ (r : ℕ) (T : Fin r → Module.End k V),
      (∀ i j : Fin r, FiniteDimensional k (LinearMap.range (T i * T j))) →
        (∀ i : Fin r, (T i).IsFinitePotent) ∧
          (∑ i : Fin r, T i).IsFinitePotent ∧
            (∑ i : Fin r, T i).tateTrace = ∑ i : Fin r, (T i).tateTrace) := by
  sorry

end Module.End
