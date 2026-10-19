# Worker report: lem-trf-torsion-sheaf-complex-representative

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-torsion-sheaf-complex-representative.json`: split into three proof steps; statement, source, blueprint ancestry, and imported searches retained.
- `dag/nodes/sec-trace-formula/lem-trf-torsion-injective-subcomplex.json`: statement-only unsplit node; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-torsion-sheaf-serre.json`: statement-only unsplit node for the Serre closure; no Mathlib match.
- `citations.json`: verbatim statement quotations for every cited node in the item's non-elementary steps.
- `searches.jsonl`: inherited searches plus the current item and child-node searches.

## Attachments

None. No sorry-free declaration in `WeilConjectures/` states this item or the new child node.

## WANTED:

None. The Stacks source is present locally.

## Faults and corrections

The imported item had the correct Tag 0DD7 statement but no proof split. I kept its arbitrary small-site scope, local sectionwise torsion convention, bounded-below hypothesis, and explicit absence of a common annihilator. The proof now follows the source: local torsion is a Serre subcategory; a bounded-below object is represented by a bounded-below injective complex; and the termwise torsion subsheaf is quasi-isomorphic when cohomology is torsion. The middle argument uses the existing enough-injectives and K-injective-resolution nodes. The two new children are strictly smaller than the item and record the source's Serre-closure and torsion-subcomplex lemmas.

No duplicate node states either the torsion-subcomplex quasi-isomorphism or the generic Serre-closure statement; the existing torsion-sheaf characterization is restricted to small etale sites and does not state a result for arbitrary sites or complexes. Whole-DAG and blueprint searches found no equivalent child. The Mathlib results were generic derived-category representatives, injective complexes, and quasi-isomorphism APIs; none asserts the torsion representative theorem.

## Not duplicates

lem-trf-torsion-sheaf-serre vs lem-trf-torsion-sheaf-complex-representative: the Serre node only proves closure of locally torsion sheaves under kernels, cokernels, and extensions; the item proves existence of a bounded-below torsion-term representative for a derived object.

lem-trf-torsion-injective-subcomplex vs lem-trf-torsion-sheaf-complex-representative: the child concerns only the quasi-isomorphism from the torsion subsheaf of one injective complex; the item additionally gives existence of a bounded-below representative for every derived object with torsion cohomology.

## Review by Q60

I read `literature/stacks-project/sites-cohomology.tex` at Tag 0DD7 and the explicit bounded-below use in Tag 0DE5. The item statement matches the source's equivalence for the Serre subcategory of torsion abelian sheaves. Step 1 uses the new Serre-closure node, whose statement exactly supplies closure under kernels, cokernels, extensions and exact inclusion; I read its 0DD7 source argument, including the local lift and product-of-annihilators calculation, and checked that it introduces no uniform exponent.

For step 2 I checked the existing statements `lem-weil-pbc-site-sheaves-enough-injectives` and `prop-pur-kinjective-resolutions-exist`; they supply an abelian sheaf category with enough injectives and K-injective resolutions by injective terms. Starting from a bounded-below representative of the D+ object, the standard resolution construction starts at its lower bound, so the resulting injective complex remains bounded below. Its cohomology is unchanged and hence torsion by the item hypothesis.

For step 3 I read both new child statements: the Serre node used in step 1 and the torsion-subcomplex node used in step 3. The latter is exactly the torsion-subcomplex assertion proved in 0DD7: injectives are divisible, tensoring with Q kills torsion cohomology, and the short exact sequence with quotient `I^bullet tensor Q` shows the torsion-subcomplex inclusion is a quasi-isomorphism. Applying it gives a bounded-below torsion complex and localization identifies its derived object with K. The edge cases K=0, an object concentrated in one torsion sheaf, shifts, the empty site, and unbounded torsion such as Q/Z all satisfy the statement; no step assumes a common annihilator.

I checked every cited quote against the current node files, confirmed the new node's `blueprint.from` follows the ancestor chain, and recorded all current Mathlib searches. No Lean files, compiler, Lake, or build tools were used.

## Unfinished work

None. The two child nodes remain intentionally unsplit for later stage-1 workers.
