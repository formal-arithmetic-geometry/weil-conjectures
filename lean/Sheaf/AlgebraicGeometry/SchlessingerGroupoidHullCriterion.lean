module

public import Sheaf.AlgebraicGeometry.ClassicalDeformationHull
import Sheaf.RingTheory.ArtinCompletedPolynomialTestRing
import Sheaf.AlgebraicGeometry.ArtinMinimalLiftableIdeal
import WeilConjectures.RingTheory.CompleteLocalQuotient
import Sheaf.RingTheory.DescendingIdealAdicTopology
import Sheaf.AlgebraicGeometry.ArtinLocalTestAlgebra
import Sheaf.AlgebraicGeometry.ArtinSmallExtensionEssential
import Sheaf.AlgebraicGeometry.ArtinTangentRingLiftCriterion

/-! # Schlessinger's hull criterion for deformation groupoids

Source: Stacks Project, formal-defos.tex, Tags 06J7, 06IX, 06IZ, 06K0 and 06JL,
with coefficient ring Lambda = k
(blueprint: lem-sfb-schlessinger-groupoid-hull-criterion).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory

namespace AlgebraicGeometry.ArtinDeformation

/-- A classical predeformation groupoid with (RS) and finite tangent dimension has
a hull; if its infinitesimal automorphism group is trivial, every hull is a natural
isomorphism. The target tangent structures are explicitly the deformation operations.
Source: Stacks, Tags 06J7, 06IX, 06IZ, 06K0 and 06JL, Lambda = k
(blueprint: lem-sfb-schlessinger-groupoid-hull-criterion).

Proof:
1. Choose a basis theta_i of T, of size d, including d = 0. By
lem-sfb-artin-completed-polynomial-test-ring form S = k[[X_1,...,X_d]]. The
square-zero tensor identification of lem-sfb-artin-rs-tangent-tensor gives the
initial class with coefficients theta_i over S/m^2. Its tangent map is a bijection
because Der_k(k,k) = 0, and it has exactly the stated vector operations.
2. Construct compatible objects over S/J_n. Apply
lem-sfb-artin-minimal-liftable-ideal to S/(m J_n) → S/J_n to obtain the least
ideal through which the object lifts; take its preimage J_(n+1). Then
m J_n ≤ J_(n+1) ≤ J_n and m^(n+1) ≤ J_(n+1), so these are Artinian tests.
3. Set J = intersection J_n and B = S/J. Since J ≤ m^2 it is proper.
lem-weil-pbc-complete-local-quotient makes B complete Noetherian local with
residue k. The cofinality theorem lem-sfb-artin-descending-ideal-adic-topology
and lem-sfb-artin-formal-filtration-comparison turn the compatible objects into
a formal object over the maximal-ideal quotients of B.
4. For a small extension A' → A and a compatible map B → A, choose n large
enough that it factors through S/J_n and that m^(n+1) dies in A'. Form the
Artinian pullback E = S/J_n ×_A A'. By lem-sfb-artin-local-test-algebra it is
a small extension of S/J_n. If it has a section, lift immediately. Otherwise
lem-sfb-artin-small-extension-essential makes the lifted map S → E surjective.
Its kernel K contains m J_n; leastness yields J_(n+1) ≤ K. This gives the
required underlying ring lift. Apply lem-sfb-artin-tangent-ring-lift-criterion
to obtain versality, and pass to isomorphism classes (Tag 06IZ). The unchanged
tangent bijection is linear, giving the asserted hull.
5. If Inf(D) is trivial, lem-sfb-schlessinger-automorphism-kernel makes reduction
on automorphisms injective across each small extension. Factor Artinian
surjections into small extensions using lem-sfb-artin-local-test-algebra. Since
D(k) is terminal, induction makes every automorphism trivial. (RS) now descends
to bijective fibre-product gluing on isomorphism classes, so pi_0 D is a
set-valued deformation functor (Tag 06K0).
6. Fix any hull. Induct on Artinian length as in Tag 06JL. Both functors are
singletons at k. Smoothness gives surjectivity across a small extension.
By lem-sfb-deformation-marked-lift-torsor the nonempty lifting fibres are
torsors for their tangent spaces tensored with the kernel, and the hull map is
equivariant for the tangent linear isomorphism. Thus it is injective too.
7. Every component is bijective; its inverses satisfy naturality by the
naturality of the original map. This proves the final clause for every hull. -/
theorem schlessinger_groupoid_hull_criterion
    {k : Type u} [Field k] (D : CofibredGroupoids.{u, v, w} k k)
    (hpre : IsPredeformation D) (hRS : IsRimSchlessinger D)
    [AddCommGroup (tangentSet D)] [Module k (tangentSet D)]
    (hoperations : HasClassicalTangentOperations D) [FiniteDimensional k (tangentSet D)] :
    (∃ (B : CompleteLocalAlgebra k k) (η : ClassicalClassMap D B), IsClassicalHull η) ∧
    (∀ x₀ : fibre D (residueTest (R := k) (k := k)),
      Subsingleton (Aut ((push D (classicalZeroArrow (k := k))).obj x₀)) →
      ∀ (B : CompleteLocalAlgebra k k) (η : ClassicalClassMap D B),
        IsClassicalHull η → IsClassicalClassIso η) := by
  sorry

end AlgebraicGeometry.ArtinDeformation
