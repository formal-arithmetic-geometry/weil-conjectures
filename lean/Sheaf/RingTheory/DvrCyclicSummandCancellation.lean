/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.Prod
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Cancellation of a cyclic summand over a discrete valuation ring

Source: the agent scalar calculation accompanying Hemo--Richarz--Scholbach,
Example 3.1 and Theorem 6.12(2), extracted from the local Smith argument;
Stacks Project, Algebra, Tag 00E9 supplies the local-ring unit criterion
(blueprint: lem-sfb-dvr-cyclic-summand-cancellation).

A binary direct sum is represented by the product of its two modules, with
componentwise operations, as in the node's proof. Ideal quotients are the
corresponding submodule quotients. No basis or freeness is assumed.
-/

@[expose] public section

universe u v w

namespace IsDiscreteValuationRing

/-- Cancel the common summand `A / (π^e)` from an isomorphism of finitely generated
`A`-modules. The exponent may be zero.

Source: agent scalar calculation accompanying Hemo--Richarz--Scholbach, Example 3.1
and Theorem 6.12(2), extracted from the local Smith argument; Stacks Project,
Algebra, Tag 00E9 for the unit criterion
(blueprint: lem-sfb-dvr-cyclic-summand-cancellation).

Proof plan (the node's four steps):
1. If `e = 0`, the quotient is zero and the given equivalence identifies `M` and `N`.
   Otherwise put `C = A / (π^e)`. Write the equivalence and its inverse in blocks
   `F = (a,b;c,d)` and `G = (a',b';c',d')`. Since `C` is cyclic, `a` and `a'` are
   multiplication by representatives `u,v` in `A`. The first block of `GF = 1`
   gives `b'c = 1 - vu`.
2. The maximal ideal is `πA`. By `IsLocalRing.notMem_maximalIdeal` (the node
   `lem-weil-pbc-local-ring-unit-criterion`), if `u` is outside it, `a` is invertible.
   Otherwise `w = 1 + (1-v)u` is outside it and is a unit. Postcompose `F` with
   the shear `(x,n) ↦ (x+b'(n),n)`, whose inverse subtracts `b'(n)`. The new
   upper-left block is multiplication by `w`. Thus obtain `F₁ = (p,q;r,s)` with
   `p` invertible.
3. Precompose with `(x,m) ↦ (x-p⁻¹q(m),m)` and postcompose with
   `(x,n) ↦ (x,n-rp⁻¹(x))`. Replacing minus by plus gives the inverse shears.
   Direct substitution gives the diagonal equivalence `D(x,m) = (p(x),h(m))`,
   where `h = s-rp⁻¹q`. Its inverse `J` is the composite of the known inverses.
4. Define `t(n)` as the second component of `J(0,n)`. The second components of
   `DJ(0,n) = (0,n)` and `JD(0,m) = (0,m)` give `h(t(n)) = n` and `t(h(m)) = m`.
   These linear maps give the required equivalence. All operations are operations
   on pairs; neither freeness nor a basis is used. -/
theorem nonempty_linearEquiv_of_cyclic_prod
    {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (π : A) (hπ : IsLocalRing.maximalIdeal A = Ideal.span {π}) (e : ℕ)
    (M : Type v) (N : Type w) [AddCommGroup M] [AddCommGroup N]
    [Module A M] [Module A N] [Module.Finite A M] [Module.Finite A N]
    (h : Nonempty (((A ⧸ Ideal.span {π ^ e}) × M) ≃ₗ[A]
      ((A ⧸ Ideal.span {π ^ e}) × N))) :
    Nonempty (M ≃ₗ[A] N) := by
  sorry

end IsDiscreteValuationRing
