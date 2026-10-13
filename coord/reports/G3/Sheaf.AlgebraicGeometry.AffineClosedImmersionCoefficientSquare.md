## What changed

Proved `AlgebraicGeometry.affine_closedImmersion_coefficient_square` without
changing its signature or public imports. Four proved private helpers establish
quotient-module coordinate adjustment, chart restriction equivalence, local
surjectivity of the coefficient map, and the quotient spectrum presentation.
Updated the existing node's proof and proof_origin to reflect this route.

The existing quotient restricted isomorphism supplies arbitrary coefficient
coordinates. Full faithfulness transports the epic coefficient map to a
surjective A-linear map f : A → A/I. Its value at 1 is a unit; multiplication
by its inverse adjusts the coordinates to make the square commute.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.affine_closedImmersion_coefficient_square`
(node `lem-sc-affine-closed-immersion-coefficient-square`).
No sorry remains in the delivered module; no holes or modules were added.
Compilation passed. `#print axioms` reports exactly `propext`, `Classical.choice`,
and `Quot.sound`, so this is a proof rather than a decomposition.

## No longer needed

No original import, DAG dependency, or module was removed. The proof retains
`Sheaf.AlgebraicGeometry.AffineQuotientRestrictedIso` and its node
`lem-sc-affine-quotient-restricted-iso`.
The direct basic-open calculation of the coefficient compatibility is unnecessary:
the existential coordinates can be adjusted by a quotient-module automorphism.
A temporary proof import of `WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel`
was removed; local surjectivity uses the Mathlib sheaf criterion directly.

## Where the brief, the DAG or earlier work was wrong

The original plan asks for canonical quotient coordinates and a localization
calculation. The unchanged theorem only asserts existence of commuting coordinates,
so arbitrary quotient coordinates followed by a unit adjustment suffice. No
statement is false or changed. The unit record has no realized node that this
shorter argument bypasses.

## Second reading by G3

1. Compared the delivered module with the repository version. The public theorem signature and existing declarations are unchanged; only private proof helpers and the theorem proof were added. Verdict: pass.
2. Compiled the module with `lcompile.py`, checked there are no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by` declarations, and checked `#print axioms`: only `propext`, `Classical.choice`, and `Quot.sound` occur. Verdict: pass.
3. Reviewed the proof route and the updated node. The quotient-coordinate adjustment is a genuine intermediate argument, the theorem statement is unchanged, and no new split-off statement or node was introduced. The edge cases noted in the theorem docstring remain covered by the categorical argument. Verdict: pass.
4. The proof uses the existing affine quotient restricted isomorphism and all imports remain necessary; no unused import or proof dependency was found. The shorter route does not bypass a realized unit step. Verdict: pass.
5. The node's proof, proof dependencies, proof origin, and Lean declaration agree with the delivered proof. Verdict: pass.

Changed only the proof module and its node metadata, and added this second-reading record. No additional holes or nodes were introduced.
