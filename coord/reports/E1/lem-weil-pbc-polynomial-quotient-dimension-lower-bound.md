# Worker report: lem-weil-pbc-polynomial-quotient-dimension-lower-bound

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-polynomial-quotient-dimension-lower-bound.json`: split the item into three source-faithful proof steps. No new nodes were created.
- `coord/reports/E1/lem-weil-pbc-polynomial-quotient-dimension-lower-bound.md`: this report.

## Attachments

None.

## Wanted sources

None. The proof was checked against `literature/stacks-project/algebra.tex`, paragraph following Definition 00S9, in the obtained Stacks checkout at `/home/ubuntu/weil-conjectures-sheaf-F2/literature/stacks-project/algebra.tex`, including 00OP and 00KW.

## Findings and changes

The statement agrees with the cited Stacks paragraph: for a nonzero quotient of a polynomial ring in (m) variables by (t) equations, localization at a maximal ideal over the equations has dimension at least (m-t). The imported node had no proof. I supplied the source argument in three steps and used only existing public nodes: maximal-ideal existence; polynomial-localization dimension (00OP); localization dimension as height; the Noetherian finite-type fact; the (t)-equation height bound that packages the iteration of 00KW; dimension at a closed point; and the supremum of local dimensions.

The quotient ideal correspondence in step 1 is written out directly. The passage from the local inequality to the global topological dimension, implicit in the source paragraph, is made explicit with 00OU and Topology 0B7I. The existing three Mathlib searches were retained; they record that Mathlib has the height inequality and polynomial dimension ingredients but no one-line theorem matching the full statement.

No source, blueprint, or statement error was found. The unit route is unchanged.

## Unfinished work

None.

## Review by E1

I read the paragraph after Stacks Algebra Definition 00S9 (`definition-lci-field`) in `algebra.tex`, including the cited 00OP and 00KW route. The item's nonzero quotient, field, variable count, and equation count agree with the source's lower-bound argument; the global dimension conclusion follows from the two existing dimension nodes. There are no new nodes, so B1-B7 and the new-node search issue C5 do not arise; I checked the current DAG for the seven cited ids rather than creating replacements.

Step 1 uses the statement of `proper-ideal-contained-in-maximal` for the nonzero quotient. The inverse-image and quotient-ideal calculations are elementary. Step 2 uses the exact statements of `polynomial-ring-maximal-localization-dimension`, `localization-dimension-chains-below-prime`, `finite-type-algebra-noetherian`, and `noetherian-height-quotient-bound`; the field is Noetherian, the polynomial ring is finite type, and the inverse-image ideal is maximal and contains all t equations. This gives the inequality even for t=0. Step 3 uses `closed-point-dimension-local-ring` for the finitely generated quotient at a maximal ideal and `dimension-supremum-local-dimensions` to pass to the whole spectrum. For m=0 and for a nonzero quotient with t>m, the same inequalities remain valid. No step cites a node's proof, imports another unit's route, or hides a non-elementary assertion. I found no A-F issue to send back; the worker's files needed no mathematical change.
