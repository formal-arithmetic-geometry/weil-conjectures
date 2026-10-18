/-
Copyright (c) 2026 The SHEAF contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.RingTheory.Algebraic.Defs
import Sheaf.AlgebraicGeometry.GeometricIrreducibilityFiniteSeparableTest

/-!
# Algebraic closure in a field extension implies geometric irreducibility

Source: Stacks Project, Algebra, Tag 037P (lemma-field-extension-geometrically-irreducible)
(blueprint: lem-zl-field-extension-algebraically-closed-geometric).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- If a field extension has no new elements algebraic over its base, its spectrum is
geometrically irreducible over the base.

Source: Stacks Project, Algebra, Tag 037P (lemma-field-extension-geometrically-irreducible)
(blueprint: lem-zl-field-extension-algebraically-closed-geometric).

Proof (blueprint, step by step):
1. Apply the finite-separable geometric-irreducibility criterion to reduce to showing that
   `Spec (K ⊗[k] E)` is irreducible for every finite separable extension `E/k`; identify this
   spectrum with the corresponding affine base change.
2. Choose a primitive element `α` of `E/k`, and let `P` be its monic irreducible minimal
   polynomial; use the quotient presentation `E ≃ k[T]/(P)`.
3. Identify `K ⊗[k] E` with `K[T]/(P_K)` by the two mutually inverse maps on coefficients and
   on `T`.
4. A factorization of `P_K` into monic nonconstant factors has coefficients algebraic over `k`
   by the monic-divisor coefficient lemma. The hypothesis puts those coefficients in `k`, which
   contradicts irreducibility of `P`.
5. The quotient by the irreducible positive-degree polynomial is a nonzero field by the PID
   Bezout argument. Its spectrum is one point, hence irreducible, and the criterion gives the
   result.
-/
theorem geometricallyIrreducible_of_isAlgebraic_mem
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    (h : ∀ x : K, IsAlgebraic k x → ∃ y : k, algebraMap k K y = x) :
    GeometricallyIrreducible
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
  sorry

end AlgebraicGeometry
