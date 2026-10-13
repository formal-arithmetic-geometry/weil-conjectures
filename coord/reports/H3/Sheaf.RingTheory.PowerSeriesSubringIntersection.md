## What changed

Proved `RingTheory.powerSeriesSubringIntersection` with its original signature and
visibility, in `lean/Sheaf/RingTheory/PowerSeriesSubringIntersection.lean`.
All added helpers are private and proved. Added proof-only imports of
`Mathlib.RingTheory.MvPowerSeries.Expand`, `Mathlib.Algebra.CharP.Algebra`, and
`Mathlib.LinearAlgebra.Basis.Basic`. No public imports or existing definitions changed.
Updated the existing node's proof and proof_origin to describe the implemented argument;
its proof_deps are retained.

The coefficient-field proof spans the bounded basis monomials avoiding J, reduces
exponents modulo p, and uses span induction for multiplication. Inversion uses
x⁻¹=(x^p)⁻¹*x^(p-1), so no finite-dimensional multiplication argument is required.
The finite union of supports of the basis coordinates of c eliminates all nonconstant
coordinates. Frobenius fixes natural-number casts, proving that the intermediate field
of scalars is contained in its field range.

The power-series proof constructs coefficients at divided indices using the assumed
coefficient roots and proves equality with Mathlib's Frobenius expansion formulas.
Each polynomial monomial has a root; summing the finitely many roots works by
`sum_pow_char`. The reverse implication uses coefficientwise polynomial and series
Frobenius and `Subfield.subset_closure`.

## Proved and sorry left

Closed the sole original hole, `RingTheory.powerSeriesSubringIntersection`
(node `lem-weil-pbc-power-series-subring-intersection`). No holes added; none remain.
This is a complete proof, not a decomposition. The final theorem's `#print axioms`
output is exactly `[propext, Classical.choice, Quot.sound]`.

The private helpers `pBasisCoefficientIntersection`, `exponent_eq_smul`,
`series_coeff_pow_smul`, `series_coeff_pow_zero`, `series_exists_root`,
`polynomial_exists_root`, and `polynomial_power_coeff`, and the private instance
`seriesCharP`, are all proved. All source signatures, including the public theorem,
remain unchanged. Local compilation passes without warnings.

## No longer needed

No original imports, nodes, or modules are pruned: all four original proof dependencies
are Mathlib leaves used in the proof. No additional Sheaf or WeilConjectures dependency
is imported. The finite-dimensional-subring argument suggested for inversion is no
longer needed; the pth-power inverse identity replaces it within the same proof step.
The explicit proof-only import `Mathlib.RingTheory.MvPolynomial.Expand` tested during
proof development was omitted because `MvPowerSeries.Expand` already imports it.
No new helper module is needed; the completed coefficient-field proof is private in
the assigned module.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface problem was found. The on-disk Stacks source cited by
the DAG is unavailable on this machine, so the source was read at
https://stacks.math.columbia.edu/tag/07P5, proof of (1) and (2), last sentence.
The existing declaration docstring supplies the expanded bounded-monomial argument.

The field proof works for arbitrary I: its only finite set is the union of supports
of the finitely supported basis representation of one element. The constructions
also cover empty I, n=0, m=0, empty J, zero series, and zero polynomial. At zero
coefficients the root is zero; at nonzero coefficients all exponent divisibility is
proved before constructing a monomial root. No arbitrary witness of an unproved
existence theorem is used and no definition contains sorry.

Searches used `msearch.py` leanfinder (complement p-basis field intersection), loogle
(`MvPolynomial.expand`), and grep (`pBasis|p_basis|coeff.*frobenius|range.*expand`),
plus direct searches of both library roots and the pinned Mathlib. The field search
found no matching intersection theorem. The expansion APIs, basis span support
lemma, and Frobenius finite-sum identity supplied all remaining proof ingredients.
The unit sk-thm-p1 and its realized steps are unchanged.

## Second reading by H3

1. **Interface and statements.** Compared the delivered module with the repository version. The public theorem signature and visibility are byte for byte unchanged; only proof-only imports, private helpers, and the proof body were added. The existing DAG statement and unit route remain unchanged.

2. **Proof and trust.** Compiled the module with `lcompile.py` successfully. The file has no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`; no definition contains `sorry`. A probe printing the theorem axioms produced no extra axioms beyond the permitted kernel axioms.

3. **Split statements and truth.** No statements were split off and no new public declarations were added. The private helpers are strictly intermediate facts: bounded p-basis span closure, coefficientwise power-series Frobenius formulas, and polynomial root assembly. Edge cases such as zero coefficients, empty index types, and zero variables are covered by the case splits and finite-support constructions.

4. **Pruning and route.** The three added imports are used only by the proof and are correctly non-public. Existing public imports are needed by the unchanged theorem signature. The proof follows the unit's coefficient and Frobenius route; the finite-dimensional inverse subargument is correctly replaced by the explicit pth-power inverse identity. No proof dependency is unused, so no nodes or modules are pruned.

5. **DAG agreement.** Updated proof and proof_origin text describe the implemented private-helper route, while proof_deps and the target statement remain consistent with the declarations actually used. The unit `sk-thm-p1` route and its realized fields are untouched.

Changed during second reading: no Lean proof changes were necessary; appended this review and verified the delivered module, node metadata, compilation, and axioms.
