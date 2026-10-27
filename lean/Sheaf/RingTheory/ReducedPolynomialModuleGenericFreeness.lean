module

public import Sheaf.RingTheory.PolynomialModuleGoodLocus
import Sheaf.TraceFormula.PolynomialShearLeadingCoefficient
import Sheaf.RingTheory.FinitelyPresentedOverSubring
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Ideal.Operations

/-!
# Generic freeness of polynomial modules over a reduced ring

Source: Stacks Project, Algebra, Tag 051Z (lemma-generic-flatness-reduced),
polynomial-algebra case (blueprint: lem-sfb-reduced-polynomial-module-generic-freeness).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace MvPolynomial

/-- The good locus of a finite polynomial module over a reduced ring is open and dense.

Source: Stacks Project, Algebra, Tag 051Z (lemma-generic-flatness-reduced),
polynomial-algebra case (blueprint: lem-sfb-reduced-polynomial-module-generic-freeness).

Proof:
1. The locus is a union of principal opens, hence open. The zero ring has empty spectrum.
Use strong induction on the number `n` of variables, simultaneously over all reduced rings.
Finite generation and reducedness persist under localization, by the fraction formulas.
2. By `lem-sfb-polynomial-good-locus-localization`, density on principal charts of a dense
open implies density globally. For every open `V`, the union of `V` and the complement of its
closure is dense: no nonempty open can lie in the boundary of `V`.
3. Filter the finite module by its finitely many generators. Each successive quotient is
`P / J` for an ideal `J` of the polynomial ring. By
`lem-sfb-polynomial-good-locus-extension`, the intersection of the two end good loci is
contained in the middle good locus. Finite intersections of dense opens are dense, so it
suffices to treat cyclic modules; no finite generation of `J` is required.
4. Let `I` be the ideal of all coefficients of elements of `J`. Cover the complement of
`V(I)` by opens `D(a)` for actual coefficients `a`, giving a relation with a unit coefficient.
On the complement of the closure of that open, every coefficient vanishes after localization:
`lem-weil-pbc-zero-locus-eq-iff-radical-eq` makes it nilpotent, and reducedness makes it zero.
There `J` is zero and the module is the polynomial ring, free on its monomials.
5. For a relation with a unit coefficient, induct on the number of nonzero nonunit
coefficients. If all coefficients are units and the relation is constant, the module is zero.
This includes the outer base case `n = 0`.
6. For a nonconstant relation with all coefficients units, use
`lem-trf-polynomial-shear-leading-coefficient` and the invertible triangular coordinate change
to make the relation monic in the last variable. Powers below its degree generate the quotient
over the polynomial ring in one fewer variable, so the outer induction applies.
7. On the dense open from the outer induction, use `lem-trf-finitely-presented-over-subring`
to transfer finite presentation from the smaller polynomial ring to the original one, a
finite type algebra over it. Transport through the coordinate isomorphism preserves the
presentation and the base action.
8. For a nonunit coefficient `a`, split a dense open into `D(a)` and the complement of its
closure. On the former it becomes a unit; on the latter it becomes zero by the radical
calculation and reducedness. The number of nonzero nonunit coefficients drops in both cases.
The inner induction and the localization lemma assemble the dense good loci.
9. The cyclic filtration completes the induction for every finite module and every `n`.
All bases over the localized base may be infinite or empty. No domain, nonzero-ring,
Noetherian, or finite-presentation hypothesis on the original module is used.
-/
theorem isOpen_dense_polynomialModuleGoodLocus
    (R : Type u) [CommRing R] [IsReduced R] (n : ℕ) (M : Type v) [AddCommGroup M]
    [Module (MvPolynomial (Fin n) R) M] [Module.Finite (MvPolynomial (Fin n) R) M] :
    IsOpen (polynomialModuleGoodLocus R n M) ∧
      Dense (polynomialModuleGoodLocus R n M) := by
  sorry

end MvPolynomial
