/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.RingTheory.TateResidue.TateIdeals
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Sheaf.RingTheory.TateResidue.FinitePotentTraceCalculus
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Tate endomorphism ideals and traces of mixed commutators

Source: J. Tate, *Residues of differentials on curves*, §1, pp. 150–151,
Propositions 1 and 2 (blueprint: lem-pc-tate-endomorphism-ideals).

The predicates `TateResidue.E`, `TateResidue.E₁`, `TateResidue.E₂` and
`Submodule.AlmostLE` are the existing upstream definitions. Almost-containment
uses the finite-error-space characterization, equivalent over a field to the
finite dimension of `(X + Y) / Y` stated on p. 150. The theorem supplies the
subalgebra and submodules with exactly these carriers. Their intersection is E₀.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace TateResidue

/-- Tate's endomorphism algebra, its two ideals, their sum, finite-rank products,
and the finite-potent trace on their intersection, for an arbitrary subspace.
Source: Tate, *Residues of differentials on curves*, §1, pp. 150–151,
Propositions 1 and 2 (blueprint: lem-pc-tate-endomorphism-ideals).

Proof plan, following the nine steps of the node:
1. Almost-containment is equivalent to containment in the second space plus a
   finite-dimensional error space: lift a finite spanning family of the quotient.
   Images and sums of finite-dimensional spaces remain finite-dimensional
   (`def-weil-finite-dimensional-subspace`). Subspace finiteness follows from a
   complement and its projection (`lem-trf-vector-subspace-complement`).
2. The identity preserves A. Addition and scalar multiplication preserve finite
   error spaces. If R(A) ⊆ A + W_R and T(A) ⊆ A + W_T, then
   RT(A) ⊆ A + W_R + R(W_T). These give the unital subalgebra B with carrier E.
3. If T(V) ⊆ A + W_T, then T belongs to E. For R in E,
   RT(V) ⊆ A + W_R + R(W_T), while TR(V) ⊆ T(V).
   Sums and scalars give the submodule I₁; these inclusions give both ideal laws.
4. If T(A) is finite-dimensional, T belongs to E. The images RT(A) and
   TR(A) ⊆ T(A) + T(W_R) are finite-dimensional for R in E.
   Closure under sums and scalars gives I₂ and the two ideal laws.
5. Choose V = A ⊕ C by `lem-trf-vector-subspace-complement`, with projection P
   onto A. For T in E, PT lies in I₁ and (1-P)T lies in I₂, since its image
   on A is contained in (1-P)(W_T). Thus I₁ + I₂ = B.
6. For S in I₂ and T in I₁, ST(V) ⊆ S(A) + S(W_T), which is finite-dimensional.
   Every U in I₁ ∩ I₂ therefore has finite-dimensional square image and is
   finite-potent (`lem-pc-finite-potent-trace-calculus`).
7. For U,V in the intersection all four pairwise products have finite-dimensional
   image. The final clause of `lem-pc-finite-potent-trace-calculus` gives trace
   additivity, and its scalar clause gives homogeneity, including scalar zero.
   This constructs the linear map agreeing with the existing `Module.End.tateTrace`.
8. If S lies in the intersection and T lies in B, both ST and TS lie in the
   intersection by the ideal laws. Cyclicity from
   `lem-pc-finite-potent-trace-calculus` gives equal traces; linearity gives zero
   trace for their difference.
9. If S lies in I₁ and T lies in I₂, both products again lie in the intersection.
   The product TS has finite-dimensional image by step 6, so cyclicity applies.
   Equal traces and linearity give zero trace of ST-TS, without asserting that
   ST itself has finite-dimensional image.
-/
theorem tate_endomorphism_ideals (k : Type u) [Field k] (V : Type v)
    [AddCommGroup V] [Module k V] (A : Submodule k V) :
    ∃ (B : Subalgebra k (Module.End k V))
      (I₁ I₂ : Submodule k (Module.End k V)),
      (∀ T : Module.End k V, T ∈ B ↔ E A T) ∧
      (∀ T : Module.End k V, T ∈ I₁ ↔ E₁ A T) ∧
      (∀ T : Module.End k V, T ∈ I₂ ↔ E₂ A T) ∧
      I₁ ≤ B.toSubmodule ∧ I₂ ≤ B.toSubmodule ∧
      (∀ R : Module.End k V, R ∈ B →
        ∀ T : Module.End k V, T ∈ I₁ → R * T ∈ I₁ ∧ T * R ∈ I₁) ∧
      (∀ R : Module.End k V, R ∈ B →
        ∀ T : Module.End k V, T ∈ I₂ → R * T ∈ I₂ ∧ T * R ∈ I₂) ∧
      I₁ ⊔ I₂ = B.toSubmodule ∧
      (∀ S T : Module.End k V, S ∈ I₂ → T ∈ I₁ →
        FiniteDimensional k (LinearMap.range (S * T))) ∧
      (∀ U : Module.End k V, U ∈ I₁ ⊓ I₂ → U.IsFinitePotent) ∧
      (∃ tr : ↥(I₁ ⊓ I₂) →ₗ[k] k,
        ∀ U : ↥(I₁ ⊓ I₂), tr U = Module.End.tateTrace (U : Module.End k V)) ∧
      (∀ S T : Module.End k V,
        ((S ∈ I₁ ⊓ I₂ ∧ T ∈ B) ∨ (S ∈ I₁ ∧ T ∈ I₂)) →
          S * T - T * S ∈ I₁ ⊓ I₂ ∧ (S * T - T * S).tateTrace = 0) := by
  sorry

end TateResidue
