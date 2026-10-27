# Stage-1 delivery: lem-sfb-separated-space-dimension-one-scheme

Group Q79, direct-delivery worker, 2026-10-22. Only stage 1 was performed.

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-separated-space-dimension-one-scheme.json`: statement unchanged; five proof steps following the finite-cover and finite-groupoid proof of Stacks 0ADD, with Zariski globalization written out.
- `dag/nodes/sec-six-functors-basics/lem-sfb-noetherian-space-finite-scheme-cover.json`: statement-only prerequisite; no Mathlib match. A separated Noetherian space admits a finite cover by a separated Noetherian scheme.
- `dag/nodes/sec-six-functors-basics/lem-sfb-space-quasifinite-source-dimension-bound.json`: statement-only prerequisite; no Mathlib match. The scheme source of a representable locally quasi-finite map has dimension bounded by the topological dimension of a quasi-separated space target.
- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-groupoid-codimension-one-invariant-affine.json`: statement-only prerequisite; no Mathlib match. The finite-groupoid invariant affine neighbourhood theorem, under its orbitwise local-dimension hypotheses.
- `dag/nodes/sec-six-functors-basics/lem-sfb-noetherian-space-finite-affine-descent.json`: statement-only prerequisite; no Mathlib match. Chevalley affineness descent for a Noetherian algebraic-space target.
- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-space-morphism-topology.json`: statement-only prerequisite; no Mathlib match. Base change, closedness, finite fibres and local quasi-finiteness for finite maps of algebraic spaces.
- `citations.json`: one verbatim statement quote for every citation of every item proof step.

## Attachments

None. Searches of `lean/WeilConjectures/` for the item tag, algebraic spaces, and dimension-one terminology found no declaration asserting this result. No Lean was written or compiled.

## WANTED

None. All source texts used are present in `literature/stacks-project/`.

## Audit findings and corrections

The imported node has a correct statement but no proof steps. Simply replacing it by an application of a new node stating 0ADD would move all its content into one prerequisite. Instead the item now performs the actual finite-cover argument: reduction to quasi-compact Noetherian pieces, finite scheme cover, dimension bound on its source, relation groupoid, invariant affine open, saturation, open-image descent, finite affineness descent, and representability on an open cover.

The source's statement is pointwise and uses local-ring dimension; the item assumes a global topological dimension bound. This difference is accounted for by a general dimension-comparison prerequisite and the existing scheme-dimension/stalk-dimension node. The proof does not assume that an arbitrary etale quotient of a scheme is a scheme, does not assume a finite cover is flat, and does not replace finite surjectivity by etale descent in the affineness step.

The `blueprint_refs.py ancestor` command reports `None`: the inherited creation chain terminates without a blueprint-kind ancestor. The existing null ancestor is retained, its explicit place and via chain are extended for the new nodes, and `same_as` is empty after searches across all blueprint nodes. The inherited place traces the direct-image preservation route through plurinodal reduction and nodal-curve moduli. This delivery refines only the dimension-one schemehood input along its existing Stacks source. The item is not the key statement of `sk-thm-sf-ctf-stability`, so its unit's realization fields are not changed.

## Searches and reuse

Before proposing nodes I searched all DAG node statements/titles and source places, and the blueprint via `tools/blueprint_refs.py search`, for finite scheme covers, finite surjective maps, algebraic spaces, schematic loci, invariant affine opens, finite groupoids, dimension comparisons, and finite affine descent. Tag searches included 0ADD, 09YC, 0ABI, 0ABW, 0A4J, 07VP, 03ZQ, 03ZS, 0414, 0415, 04NY, and 04NZ. I reused the existing affine-atlas covering, open-image correspondence, point-lifting in fibre products, scheme dimension comparison, and scheme representability criterion.

For each new node `msearch.py` ran two differently phrased LeanFinder requests, a Loogle request, a source grep, and LeanSearch. The exact outputs are retained in the sandbox and copied into `mathlib_searches`; the tool's independent `searches.jsonl` records all calls. Every service returned successfully. The hits are scheme-only finite/proper/base-change or Noetherian facts, ordinary affine neighbourhoods, or unrelated affine convex geometry, not the algebraic-space or scheme-groupoid assertions. In particular `IsAffineHom` for a finite map gives an affine source when the target is already affine: it does not descend affineness to an unknown algebraic-space target. The item's earlier Mathlib searches are retained unchanged; they also find only scheme statements.

## Not duplicates

lem-sfb-noetherian-space-finite-scheme-cover vs lem-sfb-representable-finite-stack-properties: the existing node starts with a representable finite map of stacks and gives its properties. It does not construct any finite surjective scheme cover. The new node constructs that cover using 09YC and uses their common supporting tag 04NZ only to ensure its scheme source is separated.

lem-sfb-finite-space-morphism-topology vs lem-sfb-representable-finite-stack-properties: the existing statement gives properness and local quasi-finiteness of representable finite maps of stacks and preservation of the Deligne--Mumford condition. It does not state finite base-change permanence or finiteness of fibres on point spaces. The new statement concerns ordinary algebraic spaces, includes those missing finite-map properties, and introduces no stack or Deligne--Mumford notions. Their shared sources 04NY and 04NZ do not make these complete statements equal.

lem-sfb-finite-space-morphism-topology vs lem-weil-pbc-finite-closed-map-finite-fibres: the existing statement has scheme source and scheme target; the new result is needed before the target has been proved a scheme. Scheme-target closedness cannot be invoked directly on the algebraic-space target.

lem-sfb-space-quasifinite-source-dimension-bound vs lem-pc-scheme-dimension-local-rings: the existing node compares the dimension of one scheme with the dimensions of its stalks. The new node bounds a scheme's dimension using a locally quasi-finite map to an algebraic space, and cannot be recovered by specializing the existing statement.

lem-sfb-noetherian-space-finite-affine-descent vs lem-a1-finite-flat-affine-relation-quotient: the existing node assumes an affine relation with finite locally free projections. The finite cover here need not be flat. The new statement is finite-surjective affineness descent with a Noetherian target, as in 07VP.

No current node states any of the other new supporting results, and none is a clause of the item: they make no dimension-one schemehood conclusion for the input algebraic space.

## Review by Q79

I read the statement and both paragraphs of the finite-groupoid proof of Stacks 0ADD in `spaces-over-fields.tex`. I also read 09YC in `spaces-limits.tex`, 0ABI and its proof in `more-groupoids.tex`, 07VP and its proof in `spaces-cohomology.tex`, and the dimension statements 0ABW and 0A4J in `decent-spaces.tex`, together with local-dimension and Noetherian conventions in `spaces-properties.tex`. For the finite-map prerequisite I read 03ZQ, 03ZS, 0414, 0415 and 04NY in `spaces-morphisms.tex`; 04NZ and 04ZK justify the additional separatedness and Noetherian properties of the scheme cover. These are the individual sources recorded in each new node, all by tag and source label. I read the inherited chapter, unit, the current blueprint unit and direct-image proof, the three-level route rules in SETUP, GOAL, and delivery-errors B through E in full.

Step 1 uses `pqf-lem-locnoeth-lft` only on schemes: the etale charts over Spec K. It does not treat that scheme lemma as an algebraic-space lemma. Its conclusion is exactly the local Noetherian atlas condition. The affine-atlas covering node gives open subspaces with affine surjective etale atlases; the open-image node explicitly gives quasi-compactness from such an atlas and the equivalence with quasi-compact atlas existence. The local-Noetherian definition explicitly supplies restriction to open subschemes. The closed diagonal restricts on these opens, giving the quasi-separatedness required in the definition of a Noetherian algebraic space. No global quasi-compactness is inferred.

Step 2 uses the finite-cover node with a separated Noetherian piece, not the whole possibly non-quasi-compact X. The finite-topology node explicitly gives local quasi-finiteness. The dimension-bound node has exactly a quasi-separated algebraic-space target, and its representability requirement holds since the map is finite on scheme tests. The existing scheme-dimension node explicitly identifies the supremum of stalk dimensions with topological dimension, so it supplies every orbit-point bound. Dimension of an open is bounded by the ambient dimension by the strict closure-chain argument written in the step. No local-dimension or dimension-invariance assertion is silently borrowed from a definition node.

Step 3 uses diagonal representability to form the scheme relation, and finite base-change permanence to make its two projections finite. The pair formulas verify the groupoid laws rather than appealing to a nonexistent etale presentation of this nonflat cover. I opened the point-lifting node: its statement specifically supplies a point of the fibre product for two points with the same image. It therefore proves both that the orbit is the whole fibre and, in step 4, that W is saturated. The groupoid-affine node states precisely the orbitwise dimension hypothesis available from step 2. U is separated and locally Noetherian because the cover node gives the stronger separated Noetherian conclusion. Neither the groupoid lemma nor its use assumes reducedness or flatness.

Step 4 explicitly computes the complement of f(W) as the closed image of the complement of W. This uses closedness, surjectivity and saturation, not an unjustified assertion that finite maps are open. The cited open-image node includes a general bijection between open subsets and open subspaces, even though other clauses of that node concern etale maps; I use that general clause to construct Z'. Its base-change clause for an open immersion identifies the pullback with W. Consequently the finite map to Z' really is a base change, and not merely a map with the right image. The Noetherian hypothesis for 07VP is checked: Z' inherits local Noetherianity and separatedness and is quasi-compact as a continuous image of the affine W. Thus every hypothesis of the finite-affine-descent node holds.

Step 5 uses the actual clauses of `lem-pc-schemes-criterion`: Zariski sheaf condition, representable open subfunctors, representable inclusions and a covering. I wrote out why the covering holds after testing on any scheme. The algebraic-space definition gives the sheaf condition, and the open-subspace correspondence gives the tested inverse-image point sets. This yields a scheme over Spec K, not just an abstract scheme without its structure map. These general tools from other units are listed in `split_report.tool_uses` with their purpose.

I tested the statements on the empty space, dimension-zero Artinian examples including nilpotents, disconnected unions, and an infinite disjoint union of separated curves. The last example checks why all finite-cover and Noetherian arguments must be made on quasi-compact open pieces. The invariant-affine theorem excludes the empty orbit by choosing u; it permits nilpotents and finite projections without flatness, as its source does. The affine-descent lemma retains its Noetherian and surjective hypotheses; it would not be justified to erase them. General locally quasi-finite dimension comparison is used only with a quasi-separated target. None of the five steps is longer than 2000 characters; no step hides a new independent theorem behind an unproved comparison. The new nodes are statement-only and have no proofs or proof dependencies. Every item proof citation is backed by its exact node statement in `citations.json`.

## Unfinished work

The five new nodes are deliberately unsplit, as required for a one-level stage-1 delivery. Their proofs remain later DAG work. No part of the item's natural-language argument is deferred beyond these explicitly cited prerequisites.
