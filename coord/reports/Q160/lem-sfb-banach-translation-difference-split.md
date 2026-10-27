# Q160 stage-1 report

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-banach-translation-difference-split.json: item, statement, split in six steps; no exact Mathlib match for the whole statement.
- citations.json: one verbatim statement quotation for every cited node in every step.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0. Existing leaves reused: lem-sfb-banach-mahler-coordinates, lem-sfb-compact-function-space-complete, lem-coef-compact-open-currying.

## Attachments

None. I searched lean/WeilConjectures for the blueprint id, Mahler, fwdDiff and translation/difference concepts. ForwardDiff.lean contains polynomial/natural-number differences, not this Banach-valued topological exact sequence. No project declaration states every clause. Mathlib's Mahler equivalence is already represented by the existing leaf.

## WANTED

None for this proof: the non-elementary facts all have existing nodes and local Mathlib source was read. The analytic expansion is agent-written, not a theorem attributed to Stacks 0DVG. That tag supplies a cochain differential, not the claimed analytic splitting.

## Issues in the imported material and changes

The item was statement-only; there was no previous sandbox node or report to repair, and no released repair note. The statement and stmt_deps are unchanged. All inherited searches and their detailed results are retained and read, including the second Mahler phrasing. Their results provide Mahler coordinates, not the entire exact sequence with equivariance. I also ran and logged topology searches with the mandated msearch.py command; these led me to reuse existing compact-open currying and profinite integer-tower nodes, not create their special cases.

The item's existing blueprint.from.node is null, and blueprint_refs.py ancestor prints None. I preserve that ancestry, fill no invented ancestor, and retain the inherited precise paragraph and via list. Searches of the whole imported blueprint for Mahler, translation, compact group, uniformly continuous, and adic integers found no node restating this item. The latest blueprint direct-images proof paragraph (3) was read; it states the open/proper factorization and does not contain this analytic theorem. The proof_origin therefore honestly says agent and identifies the analytic expansion below that route. No unit route or chapter record is changed. This is not the key node of the unit, so no unit realization file is delivered.

## Not duplicates

No new nodes. In particular I did not create a compactness leaf after searches found PadicInt.compactSpace: the existing lem-sfb-integers-profinite-tower already states the stronger inverse-limit topology and profiniteness result. The existing constant-kernel and Mahler formulas are proved inline rather than made into nodes that restate clauses of the item.

## Review by Q160

I read the latest blueprint proof paragraph (3), the item's chapter and unit records, and every statement quoted in citations.json. I checked delivery-errors B through E against the actual proof, not just its dependency list. I read Mathlib/NumberTheory/Padics/MahlerBasis.lean:346-386, especially the isometry at 357 and its coordinate formula at 382; Mathlib/Topology/CompactOpen.lean:430-467 for currying/evaluation; and Mathlib/NumberTheory/Padics/ProperSpace.lean:44-57 for the compactness search candidate. No new node has an unexamined source.

Step 1 uses lem-sfb-integers-profinite-tower clauses 1 and 2: it explicitly identifies the integer ring with the finite quotient inverse limit and says it is compact Hausdorff. The degree-one extension E=Q_ell is finite, its norm is exactly the given norm and ell is its uniformizer. def-weil-l-adic-numbers identifies its unit ball with Z_ell. The addition estimate is written out. The complete coefficient V satisfies every hypothesis of lem-sfb-compact-function-space-complete; that statement gives the normed function space and the equality with compact-open topology. I declare the integer-tower node as a generic off-unit tool, not a replacement for the unit's direct-image route.

Step 2 uses exactly the two directions of lem-coef-compact-open-currying: uncurry the identity on R to obtain evaluation, compose with addition, then transpose with A=H times R and K=H. The locally compact hypothesis is checked by the explicit small closed-ball argument. This does not assume that R itself is locally compact. Step 1 supplies the equality of topologies used here. Fixed translations are norm isometries by bijectivity. The action identities use the abelian group law of H.

Step 3 needs only pointwise definitions and norm inequalities, which are written explicitly: Delta is contractive, constants are isometric and injective, evaluation is contractive, and Delta commutes with translations. No equivariance of T is asserted or used.

Step 4 uses the actual statement of lem-sfb-banach-mahler-coordinates, including its coefficient formula, isometry, completeness and bounded Z_ell scalar hypotheses. I checked the last hypothesis by restricting the normed Q_ell scalar equality. The cited equivalence is only Z_ell-linear on its face, so I explicitly prove Q_ell-linearity from the difference-coordinate formula, rather than silently strengthening the citation. The shift formula is just iteration of the very same Delta; its n=0 case is included.

Step 5 writes out both shifts on c_0, their tail convergence, linearity, supremum norm bounds and SP=1. It then conjugates P by the isometry already obtained and proves Delta T=1 after applying the injective M. This is elementary assembly from the cited coordinate theorem, not an uncited Banach splitting theorem. Step 6 compares the coefficients of f and const(f(0)); injectivity of the same equivalence identifies them. Thus no dense-integer theorem is needed, and no kernel theorem is smuggled into the proof. Evaluation at zero is the continuous inverse on the kernel by step 3, and the endpoint exactness follows from the explicit injection and right inverse.

I checked V=0, f=0, nonzero constant functions, n=0 in the coordinate formula, and a sequence supported only at coefficient zero. In the latter case P places that value at coefficient one and S recovers it; on a constant f=v the primitive is x mapped to x v, confirming the positive sign convention. The argument does not require finite-dimensional V, and it never uses real/complex Hahn-Banach or a completion of V beyond its stated completeness. Every proof step is under 2000 characters. The full transitive dependency closure of each cited analytic/tool node was checked and none contains the item, so the new citations do not form a cycle. There are no new statements to test or standalone proofs to hide in statement-only nodes. No SGA reference is used.

## Unfinished work

None in the one-level stage-1 split. Independent maintainer review remains part of the delivery process.

## Validation

Server srvcheck review_split passed with 0 new nodes. Required deliver.py dry run and push are recorded by their tool outputs.
