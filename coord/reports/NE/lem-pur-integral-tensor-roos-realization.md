# Stage-1 report: lem-pur-integral-tensor-roos-realization

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-integral-tensor-roos-realization.json`: the live statement is unchanged; its inherited one-line argument is expanded into four assembly steps and no new node is introduced.
- `citations.json`: verbatim quotes for every node used by every proof step.

## Attachments

None. Searching `lean/WeilConjectures/` for the blueprint id, `pullbackTensorIntegralTensorModel_existsUnique`, and the integral tensor/Roos names found no project declaration. The declaration recorded in the node is present only in the quarantined source and is sorried there, so it is not an attachment.

## WANTED:

None. The split uses the existing Stacks-derived and project DAG statements.

## What was wrong and what changed

The live child node retained the full target statement but had an empty proof, while the archived parent report supplied only the compressed Step 13 argument. I kept the statement byte-for-byte unchanged and wrote the complete assembly: the coherent strict tensor tower and Roos comparison, descent of the completed tensor, localization lift, and uniqueness. No clause was moved into a duplicate helper node. The proof dependencies are exactly the union of the cited uses. No statement dispute was found.

## Review by NE

I read the current item, the `sec-smooth-purity` chapter and `sk-def-purity-conv` unit, the latest blueprint association, and the archived parent report containing old Step 13. I also read every cited statement in full: `def-pur-completed-pullback-tower-core`, `lem-pur-coherent-tensor-tower`, `lem-pur-coherent-reduction-kflat`, `lem-coef-derived-system-evaluation-calculus`, `def-sf-strict-roos-functor`, `def-pur-integral-derived-operations`, `lem-pur-integral-operations-well-defined`, `lem-weil-pbc-localization-universal-property`, `def-weil-abstract-derived-category`, and `lem-weil-pbc-resolving-representative-whiskering`.

Step 1 uses the core's fixed reduction and Roos normalizations, the tensor-tower node's whole strict tower isomorphism with actual quotient transitions, the reduction node's K-flatness conclusion for every good representative, and the evaluation calculus/Roos definitions. These statements supply the entire tower and both cone coordinates required by the displayed definition of `nu`, rather than only finite projections.

Step 2 uses the integral-operation definition and its well-definedness theorem. They state that the quotient-tensor/Rlim construction is a functor independent of good K-flat resolutions and that its values are derived limits of the corresponding towers; this is exactly the role of `epsilon^tensor`.

Steps 3 and 4 use the derived-category localization statement, the explicit localization universal property (existence and unique lifting of natural transformations, including the extensionality clause), and the full-faithful restriction to resolving representatives. The hypotheses are the product localization on good complexes, and the maps on those representatives are the `epsilon` and `nu` maps already established in Steps 1–2. Cancelling `nu` gives the required component formula, and the same universal property gives uniqueness.

I checked edge cases at the level of the argument: zero complexes and empty sites make the displayed component equations vacuous or identity equations; the first quotient is still an actual quotient transition; and no boundedness, constructibility, completeness, or invertibility of `ell` was added. I checked every `citations.json` quote against the current node text. No Lean, compiler, Lake, repository, or launcher file was written.

## Not duplicates

No new nodes were created, so there are no duplicate pairs to report.

## Work left

The theorem remains a stage-1 natural-language statement; later stages must bind and prove the quarantined Lean declaration. This delivery claims only the DAG split.
