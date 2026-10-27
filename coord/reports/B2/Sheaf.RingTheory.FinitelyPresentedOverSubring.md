## What changed

Filled the proof of `Module.FinitePresentation.of_finiteType_subring` in
`Sheaf.RingTheory.FinitelyPresentedOverSubring`, preserving its full statement,
visibility, docstring, and imports. The implementation follows Stacks Algebra
Tag 0561 and the existing node's five steps.

Install the algebra and restricted module structures belonging to the given
ring homomorphism. Choose finite algebra generators of S and finite R-module
generators of M. Mathlib's `Module.FinitePresentation.fg_ker` supplies finite
generation of the relations of this R-presentation. In the finite free S-module,
let L be the sum of the S-span of those relations and the span of the finitely
many algebra-generator action relations. Both summands are finitely generated.
The induced map from the quotient by L to M is surjective. Apply the existing
`Module.exists_eq_sum_smul_of_polynomial_action` to the quotient generators;
it reduces every quotient element to R-coefficients. An element mapping to zero
then has its coefficient vector in the original R-kernel, so it is zero in the
quotient. Transfer the quotient's finite presentation along this linear
equivalence. All constructions allow empty generator families and zero rings;
no nontriviality or injectivity assumption on the ring homomorphism is used.

Validation: the complete delivered module compiled without errors or warnings
through `lcompile.py` (7.9 seconds). Mathlib searches via leanfinder, loogle and
grep found no exact module-transfer theorem. The apparent algebra-transfer
result concerns finitely presented algebras, so the stated module proof was
implemented directly using Mathlib's finite-presentation and quotient APIs.

## Proved and sorry left

Closed 1 of 1 original holes:
`Module.FinitePresentation.of_finiteType_subring`
(node `lem-trf-finitely-presented-over-subring`).

There are zero `sorry` occurrences left in the item and zero holes added.
No statements are split off. The proof uses the already stated dependency
`Module.exists_eq_sum_smul_of_polynomial_action`
(node `lem-trf-polynomial-action-reduction`, module
`Sheaf.RingTheory.PolynomialActionReduction`). Its existing proof remains a
`sorry` outside this delivery; this delivery closes the parent hole from that
existing declaration as required by stage 3.

## No longer needed

None. No imports were removed. All three existing declared proof dependencies
are used: finite type for the algebra generators, finite presentation for the
finitely generated R-kernel, and polynomial-action reduction for injectivity.
No node or module is pruned, and the unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error found. The DAG proof agrees with the Lean
argument, so no node changes are necessary. Mathlib packages the finite relation
vectors as a finitely generated kernel; extending its span to S implements the
same finite relations without choosing an additional indexed generating list.

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
