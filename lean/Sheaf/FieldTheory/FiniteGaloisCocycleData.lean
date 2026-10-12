/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker V1
-/
module

public import Sheaf.FieldTheory.BrauerScalarDefect

/-!
# Finite quotient data for a continuous Galois two-cocycle

Source: Stacks Project, Theorem 03R7, surjectivity, and Section 0DVG.
(blueprint: lem-sc-finite-galois-cocycle-data).
-/

@[expose] public section

universe u

namespace Field

/-- A prescribed continuous two-cocycle factors through a finite group quotient.

Proof: put G = Gal(Ksep/K) and c(g,h) = z(1,g,g*h). Uncurry the iterated
continuous homogeneous cochain by the exponential law for compact Hausdorff G.
Evaluation at (1,g,g*h) is continuous. The coefficient representation is discrete,
so compactness gives finite image and local constancy. Cover G^2 by finitely many
clopen rectangles on which c is constant. In each coordinate refine the resulting
finite clopen partition by cosets of an open subgroup, and intersect the normal
cores of those subgroups. The resulting open normal N has c constant on pairs
of N-cosets. Its finite quotient is nonempty. Transport its group law and quotient
map to Fin n using a finite enumeration; n is nonzero. Define d on quotient pairs
by c on representatives; coset constancy makes this independent of representatives,
and the quotient map q is locally constant because its fibres are open cosets.

The homogeneous cycle equation evaluated on (1,g,g*h,g*h*j), together with
homogeneous equivariance, yields c(g,h)c(g*h,j) = g(c(h,j))c(g,h*j).
For any quotient index j choose a representative r. Substitute r for j in that
identity and use the factorization of c and q(g*h)=q(g)q(h). Commutativity of
units reorders the two factors on the right. This gives the last displayed
identity for d. The construction concerns the prescribed cocycle itself, not
only its class. It needs no normalization, no division by the group order, and
no matrix algebra. For a trivial quotient one may have d(1,1) different from 1.

Source: Stacks Project, Theorem 03R7 surjectivity sketch and Section 0DVG;
finite coset refinement and the homogeneous-coordinate calculation are expanded
by an agent.
(blueprint: lem-sc-finite-galois-cocycle-data). -/
theorem exists_finite_galois_cocycle_data (K : Type u) [Field K]
    (z : ContinuousCohomology.cocycles (galoisUnitsTopRep K) 2) :
    ∃ (n : ℕ) (_ : n ≠ 0) (grp : Group (Fin n)),
      letI := grp
      ∃ (q : (SeparableClosure K ≃ₐ[K] SeparableClosure K) →* Fin n)
        (d : Fin n → Fin n → (SeparableClosure K)ˣ),
        IsLocallyConstant q ∧
        (∀ g h, galoisUnitsCocycleValue K z g h = d (q g) (q h)) ∧
        (∀ g h j, d (q g) (@Mul.mul (Fin n) grp.toMul (q h) j) * Units.map g.toRingHom (d (q h) j) =
          d (q g) (q h) * d (q (g * h)) j) := by sorry

end Field
