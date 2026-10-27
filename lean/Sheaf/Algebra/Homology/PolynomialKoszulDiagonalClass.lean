/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q151
-/
module

public import Sheaf.Algebra.Homology.PolynomialKoszulDiagonalSystem
import Sheaf.Algebra.Homology.TotalTensorSignedCoherence
import Sheaf.TraceFormula.AlgebraicShriekRelativePerfect
import Sheaf.Algebra.Homology.CoinductionTotalHomModel
import Sheaf.TraceFormula.FlatPolynomialQuotientPerfect
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Flat.Localization
import Mathlib.Algebra.Module.LocalizedModule.Exact

/-! # The Koszul-normalized polynomial diagonal class

Source: Stacks Project, dualizing.tex, Tag 0E2E, with Tags 0A70, 0A71, 0BZI, 0BZJ;
the explicit graph construction and scalar-extension assertion of the DAG node.
(blueprint: lem-sfb-polynomial-koszul-diagonal-class).
-/

@[expose] public section
set_option autoImplicit false
universe u
namespace AlgebraicGeometry

/-- For every flat finitely presented algebra B over a Noetherian commutative base R,
the polynomial and localized polynomial charts carry the specified graph-normalized
isomorphism kappa and its adjunct class. Multiplication by the class is invertible.
All evaluation-counit scalar comparisons preserve this class, including nonflat changes
of Noetherian base, identity and successive changes, both-factor localization, and
localization of the ambient polynomial ring at elements invertible on B.
One-variable evaluation refinements preserve the class with the new differential last;
their maps are independent of the lift, commute with scalar extension and localization,
and have coherent ordered iterates. Every normalization is an equation on the existing
derived coinduction counit or on the ordered graph Koszul complex.

Source: Stacks 0E2E, 0A70, 0A71, 0BZI, 0BZJ; the node's explicit compatibility argument
(blueprint: lem-sfb-polynomial-koszul-diagonal-class).

Proof:
1. Finite type over Noetherian R makes B Noetherian. By
lem-trf-flat-polynomial-quotient-perfect choose a bounded finite-projective P-resolution F
of B. The differential basis identifies the coefficient with the ordered top volume.
Perfect coinduction exchange (lem-sfb-perfect-coinduction-tor-independent-exchange)
applies to P -> B and P -> T = P tensor_R B_2: B is R-flat and derived tensor is A.
Its evaluation-counit equation fixes the exchange and the first coprojection.
2. Paste the two coinduction adjunctions for T -> A -> B
(lem-trf-derived-coinduction-adjunction, lem-cat-right-adjoint-composition).
The graph equations x_i - bar(x_i) give the ordered finite-free Koszul resolution of B.
The graph-coinduction calculation and lem-sfb-koszul-evaluation-pasting identify its
trace with B, sending the dual top graph wedge times the differential volume to 1.
This gives precisely kappa, retaining the B-action and cohomological signs.
3. Define xi as the adjunct of kappa inverse. On the total Hom model the adjunct sends
u to (b -> u(b)(1)); its inverse sends h to (b -> (b' -> h(b'b))). Multiplication by xi
is thus kappa inverse after restriction, hence an isomorphism. No perfect diagonal is used.
4. For any R -> R', R' Noetherian, the same F extends to a resolution of B' since B is
R-flat. Perfect exchange therefore gives the normalized comparison C tensor_B^L B' -> C'.
Over T, A and B are B_2-flat, so their scalar extensions to T' also have no higher Tor.
Likewise B tensor_A^L A' = B', since A' = A tensor_R^L R'. Differential base change
identifies the ordered coefficient volumes. No flatness of R' over R is needed.
5. Exchange is the mate of the extended counit. Pasting counits evaluates at 1 twice,
the same as direct evaluation. The graph trace commutes with scalar extension by
lem-sfb-koszul-evaluation-pasting. Taking adjuncts proves the class square. The same
mate uniqueness proves identity and successive comparison equations.
6. Localization is flat and exact. At an ambient element mapping to a unit on B the
localized graph still resolves B. Simultaneous localization localizes both copies of B
and the corresponding graph ring. Localized differential volumes give the same trace.
Finite lists compose; base localization is already a scalar change.
7. For Q=P[t] evaluate t at a lift a. The two-term resolution on t-a and its top form
give the boundary-normalized coefficient contraction (lem-trf-coinduction-polynomial-refinement).
In the graph ring the tuples (f,t-bar(a)) and (f,t-a(x)) differ by a unit triangular
matrix. The last top differential stays d(t-a); its wedge with the old volume equals
the volume with dt last. Koszul evaluation pasting with the new block initially first,
then the cyclic permutation and the signed total-tensor shift/symmetry coherence,
gives the graph trace with the new block last. Pasting counits proves preservation of xi.
8. Polynomial relative perfectness gives the scalar isomorphism B -> RHom_B(C,C)
(lem-trf-algebraic-shriek-relative-perfect). Two class-preserving comparisons differ
by a scalar b. Multiplication by xi is invertible, so b xi = xi forces b=1.
This proves lift independence and equality of ordered iterated comparisons. The same
argument after base change proves the refinement-change square. When n=0 the Koszul
resolution and volume are the unit in degree zero; when B=0 all maps are the unique
maps of zero objects. No properness or global dualizing pair enters the construction. -/
theorem polynomial_koszul_diagonal_class :
    ∃ K : PolynomialKoszulDiagonalAssignment.{u}, IsPolynomialKoszulDiagonalSystem K := by
  sorry

end AlgebraicGeometry
