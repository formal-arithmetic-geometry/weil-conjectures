module

public import Mathlib.Algebra.Algebra.Subalgebra.Operations
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Trace-one finiteness over an invariant subring

Source: ILO, Travaux de Gabber, Exposé VI 3.7(b), printed p.75, motivates the finite
strict-local invariant quotient. The general trace-one algebraic assertion below and its
skew-group proof are agent-supplied, as recorded in the DAG, not a quotation from ILO.
(blueprint: lem-per-trace-one-noetherian-invariant-finiteness)
-/

@[expose] public section

universe u v

namespace FixedPoints

/-- A commutative Noetherian ring with a finite group action and a trace-one element is
finite over its Noetherian fixed subring. Neither faithfulness nor invertibility of the
group order nor a finite-type base algebra is assumed.

Source: ILO, Travaux de Gabber, Exposé VI 3.7(b), printed p.75, motivates the finite
strict-local quotient; this general algebraic statement and proof are agent-supplied.
(blueprint: lem-per-trace-one-noetherian-invariant-finiteness)

Proof plan, following the six reviewed DAG steps:

1. Form the skew group ring S with multiplication (r[g])(s[h]) = r g(s)[gh].
   Associativity follows on basis terms from the action law and then by distributivity.
   Its unit is 1[1]. As a right R-module it is finite free on [g], because
   r[g] = [g] g⁻¹(r). Use the equivalent left R-module structure r • s = sr;
   commutativity of R makes this a module (def-weil-finitely-generated-module).
2. Choose a with group trace one and put e = sum_g g(a)[g]. Reindexing gives [h]e = e,
   hence e² = e. Coefficient sum sends re to r, so r ↦ re is injective.
   Also (sum_g r_g[g])e = (sum_g r_g)e, so Se = Re.
3. The corner C = eSe is a ring with unit e. Write c = re uniquely. Since [h]c = c
   and [h]re = h(r)e, injectivity forces r into A = R^G. Conversely b in A commutes
   with R and every [g], so be = ebe. Thus C = Ae and b ↦ be is a ring isomorphism.
   The map r ↦ re identifies the A-module R with the right C-module Se.
4. The two-sided ideal I = SeS is a right R-submodule of the finite R-module S.
   Apply lem-trf-noetherian-submodule-finitely-presented to get finite R-generators y_j.
   Expand each y_j as a finite sum of terms n_jk s_jk with n_jk in Se. Collect the
   finitely many n_jk as n_i. Their right S-span is exactly I, since it contains the
   y_j and all their right R-linear combinations, and is contained in I.
5. Multiplication by e gives Se = Ie = sum_i n_i Se. Since n_i = n_i e,
   each n_i s e = n_i (ese). Write n_i = r_i e and ese = b e with b in A.
   Every re is therefore a sum of r_i b_i e. Injectivity of r ↦ re shows that the
   r_i generate R over A, as in def-weil-finitely-generated-module.
6. Define rho(r) = sum_g g(ar). Reindexing makes its values invariant, and it is
   A-linear and restricts to the identity on A. For any ideal J of A, Noetherianity
   of R (def-weil-pbc-noetherian-ring) gives finite generators of JR. Expand them in
   elements of J and collect j_i in J generating JR. For b in J write b = sum_i j_i r_i;
   applying rho gives b = sum_i j_i rho(r_i). Thus every ideal of A is finitely
   generated, so A is Noetherian by def-weil-pbc-noetherian-ring. -/
theorem isNoetherianRing_and_finite_of_trace_one (R : Type u) [CommRing R]
    [IsNoetherianRing R] (G : Type v) [Group G] [Fintype G] [MulSemiringAction G R]
    (htrace : ∃ a : R, ∑ g : G, g • a = 1) :
    IsNoetherianRing (FixedPoints.subring R G) ∧ Module.Finite (FixedPoints.subring R G) R := by
  sorry

end FixedPoints
