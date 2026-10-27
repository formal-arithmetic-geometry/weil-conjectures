/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Lie.Semisimple.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Trace
import WeilConjectures.Mathlib.Algebra.Lie.CartanCriterion
import WeilConjectures.Mathlib.Algebra.Lie.Radical

/-!
# Trace forms of faithful representations of semisimple Lie algebras

Source: Milne, Algebraic Groups (2017), §22c, printed p.475, The Casimir operator
(blueprint: lem-sfb-faithful-semisimple-trace-form).
-/

@[expose] public section

universe u v w

set_option autoImplicit false

namespace LieAlgebra

/-- The trace form of an injective representation of a finite-dimensional semisimple Lie algebra
in characteristic zero is nondegenerate. Semisimplicity is expressed as having no nonzero solvable
ideal, by `HasTrivialRadical`. The trace form is evaluated explicitly, so the conclusion is the
left-radical condition in the source.

Source: Milne, Algebraic Groups (2017), §22c, printed p.475, The Casimir operator
(blueprint: lem-sfb-faithful-semisimple-trace-form).

Proof plan:
1. Linearity of ordinary trace (`def-weil-endomorphism-trace`) and bilinearity of composition
   make the displayed pairing bilinear. Trace cyclicity
   (`lem-pc-finite-dimensional-trace-cyclic`, `LinearMap.trace_comp_comm'`) makes it symmetric.
2. Let R consist of the elements x with Tr(ρ(x)ρ(y)) = 0 for every y. This is a linear subspace.
   For x in R, bracket preservation and cyclicity give
   B([z,x],y) = Tr(ρ(z)ρ(x)ρ(y) - ρ(x)ρ(z)ρ(y)) = B(x,[y,z]) = 0.
   Thus R is an ideal (`def-wf-lie-algebra`).
3. The image A = ρ(R) is a Lie subalgebra of End(M), and Tr(XY) = 0 on all of A × A, hence on
   [A,A] × A. Cartan's criterion (`lem-sfb-cartan-trace-criterion-characteristic-zero`,
   `LieSubalgebra.isSolvable_of_trace_mul_eq_zero`) implies that A is solvable.
4. Inductively, ρ(DʲR) = DʲA: the initial case is the definition of A, and the successor case
   uses preservation of linear spans and brackets. A term of the derived sequence of A is zero;
   injectivity of ρ makes the corresponding term for R zero, so R is solvable. Semisimplicity
   (`def-wf-semisimple-lie-algebra`, `hasTrivialRadical_iff_forall_isSolvable_eq_bot`) gives R = 0.
   An element orthogonal to every y lies in R and therefore vanishes. -/
theorem trace_pairing_nondegenerate_of_faithful
    (F : Type u) [Field F] [CharZero F]
    (L : Type v) [LieRing L] [LieAlgebra F L] [FiniteDimensional F L]
    [HasTrivialRadical F L]
    (M : Type w) [AddCommGroup M] [Module F M] [FiniteDimensional F M]
    (ρ : L →ₗ[F] Module.End F M)
    (hbracket : ∀ x y : L, ρ ⁅x, y⁆ = ρ x ∘ₗ ρ y - ρ y ∘ₗ ρ x)
    (hfaithful : Function.Injective ρ) :
    ∀ x : L, (∀ y : L, LinearMap.trace F M (ρ x ∘ₗ ρ y) = 0) → x = 0 := by
  sorry

end LieAlgebra
