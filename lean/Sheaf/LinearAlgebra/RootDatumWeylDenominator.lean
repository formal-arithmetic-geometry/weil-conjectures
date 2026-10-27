/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N6
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.RootSystem.Base
public import Mathlib.LinearAlgebra.RootSystem.WeylGroup
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.BigOperators.Finprod

/-!
# The Weyl denominator in an integral character lattice

Source: Milne, Algebraic Groups (2017), Appendix C.19--C.22, pp. 611--612,
and Section 22d, p. 480, antisymmetry operator preceding Theorem 22.50
(blueprint: lem-sfb-root-datum-weyl-denominator).

The statement uses Mathlib's root pairing, simple base, Weyl group and additive group algebra.
The rational spanning conditions allow a nontrivial quotient of the character lattice by the
root lattice. The integral determinant equals the determinant after rational scalar extension.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open scoped TensorProduct

namespace RootPairing

open Classical in
/-- The alternating orbit sum at negative rho equals the integral Weyl denominator.

Source: Milne, Algebraic Groups (2017), Appendix C.19--C.22, pp. 611--612,
and Section 22d, p. 480, antisymmetry operator preceding Theorem 22.50.
This is the agent-supplied denominator argument using those root-system results
(blueprint: lem-sfb-root-datum-weyl-denominator).

Proof plan:
1. If there are no roots, rational spanning and freeness force both lattices to have rank
   zero. Then rho is zero, the Weyl group is trivial and both sides are one. Otherwise
   extend the lattices to real vector spaces. Average a coordinate inner product over W;
   it is positive definite and invariant. Invariance gives the usual orthogonal reflection
   formula for the given coroots. Rational spanning and reducedness persist over the reals,
   and the simple-root base becomes a real basis. Determinants are unchanged by extension.
2. Reflection in a simple root delta permutes the positive roots other than delta: some
   other simple coordinate of any such root is positive and unchanged by that reflection.
   Summing gives s_delta(rho) = rho - delta, so each simple coroot evaluates to one on rho.
   Thus rho belongs to the open positive chamber and is regular.
3. Put D = e^rho times the product of (1 - e^(-alpha)) over the positive roots. The preceding
   permutation gives s_delta(D) = -D. Simple reflections generate W by
   lem-sfb-simple-root-reflection-generation. Their determinants are -1, so w(D) = det(w) D.
   Consequently coefficients satisfy c_(w nu) = det(w) c_nu.
4. A weight fixed by a root reflection has c_nu = -c_nu, hence c_nu = 0 over the integers.
   Every weight with nonzero coefficient is therefore regular. Expanding D shows that its
   support consists of weights rho minus a sum over a subset of positive roots.
5. Chamber transitivity (lem-sfb-root-chamber-simple-transitivity) moves any such weight to
   a weight mu in the open positive chamber with nonzero coefficient. Integrality gives
   each simple coroot a value at least one on mu. For eta = mu - rho, its inner products
   with all positive roots are nonnegative. Since rho - mu is a sum of positive roots,
   the inner square of eta is nonpositive. Positive definiteness forces mu = rho.
6. The coefficient of e^rho in D is one: only the empty subset of positive roots sums to
   zero. Simple transitivity on chambers makes the stabilizer of the regular weight rho
   trivial. The coefficient transformation from step 3 and the support calculation in step 5
   now give D = sum over w in W of det(w) e^(w rho).
7. Apply the group-algebra automorphism e^x maps to e^(-x). The result is exactly the claimed
   identity at negative rho, including its sign. Empty sums and products have their usual
   values, so this also agrees with step 1. -/
theorem weyl_denominator
    {ι : Type u} {X : Type v} {Y : Type w}
    [Fintype ι] [AddCommGroup X] [AddCommGroup Y]
    [Module.Free ℤ X] [Module.Finite ℤ X] [Module.Free ℤ Y] [Module.Finite ℤ Y]
    (P : RootPairing ι ℤ X Y) [P.IsReduced]
    (hX : Submodule.span ℚ (Set.range (fun i : ι ↦ (1 : ℚ) ⊗ₜ[ℤ] P.root i)) = ⊤)
    (hY : Submodule.span ℚ (Set.range (fun i : ι ↦ (1 : ℚ) ⊗ₜ[ℤ] P.coroot i)) = ⊤)
    (b : P.Base) (ρ : X)
    (hρ : (2 : ℤ) • ρ = ∑ i ∈ Finset.univ.filter b.IsPos, P.root i)
    [Finite P.weylGroup] :
    (∑ᶠ g : P.weylGroup,
      AddMonoidAlgebra.single (g • (-ρ)) (LinearMap.det (P.weylGroupRootRep g))) =
      (AddMonoidAlgebra.single (-ρ) 1 : AddMonoidAlgebra ℤ X) *
        ∏ i ∈ Finset.univ.filter b.IsPos, (1 - AddMonoidAlgebra.single (P.root i) 1) := by
  sorry

end RootPairing
