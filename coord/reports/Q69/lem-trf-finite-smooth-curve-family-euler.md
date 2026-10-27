# Worker report: lem-trf-finite-smooth-curve-family-euler

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-finite-smooth-curve-family-euler.json`: existing statement node, now split in six steps; not a Mathlib leaf.
- `citations.json`: sixteen step/node pairs, each with the verbatim relevant node statement.
- `searches.jsonl`: actual search-command log, retained alongside the report.

No new nodes and no Mathlib leaves. The statement and its statement dependencies are unchanged. No repository file, launcher file or Lean file was written; no compiler or build tool was run.

## Attachments

None. Searching the complete project source for the item id and for its finite-image/curve/Euler notions found no declaration proving the entire item. In particular, the existing affine-morphism cohomology natural isomorphism in `WeilConjectures/AlgebraicGeometry/Cohomology/Affine/AffineMorphism.lean` is useful infrastructure, but does not state all the family, coherence, canonical-edge and Euler assertions together. `GlobalSectionsBijective.of_isAlgClosed` supplies the familiar proper reduced connected special case only. Neither is grounds for ATTACH of this item.

## WANTED

None: the Stacks sources needed for this split are present. No SGA source is used.

## Findings and corrections

The live node was unsplit, with no proof and no existing sandbox attempt. No released repair note exists for this item. Its mathematical statement is correct as written. The proof must not assume that an image is a component, that a finite map is birational, or that the target is a curve. It needs only proper-field Noetherianity, finite coherence and affine cohomology. These restrictions are respected.

I read the chapter and unit records, and the current blueprint at `literature/blueprint/latest/` (snapshot main-20261023-1620, commit 7284bb09daf97437d544c51882b325f9c52cd345). The inherited blueprint provenance is historical: the current locality proof uses contracting correspondences, not the old semistable exceptional-fibre genus/tree reduction. I retain that history, state the distinction in split_report.blueprint, and split only the already-created normalization-Euler helper. I did not change the unit or chapter route, their records, or any target statement. This is not the unit's key node, so no realized fields are due.

## Not duplicates

No nodes are created. Whole-DAG searches by titles, statement concepts and source tags, and whole-blueprint searches for Euler characteristic, finite images, smooth proper curves and finite pushforward, found the precise existing tools. In particular `lem-weil-pbc-affine-morphism-cohomology-edge` states the required actual identity-h-map comparison, whereas `lem-pc-closed-immersion-coherent-cohomology` only states the closed immersion case and `lem-pc-affine-pushforward-cohomology-edge-isIso` concerns a different derived affine-coordinate implication. The latter two are deliberately not substituted for the former. The item is not a duplicate of `lem-trf-finite-ideal-twist-cohomology-comparison`, whose statement concerns ideal products and projection formulas rather than the genus/Euler family calculation. Binary direct-sum closure and sheaf gluing are steps, not new nodes.

## Mathlib searches

I ran the prescribed command with this item's id for LeanFinder twice (family Euler characteristic and affine cohomology), Loogle, LeanSearch, and Mathlib-source grep. The actual signatures returned cover finite coproduct geometry, finite maps being affine, additive module pushforward/pullback, and cochain maps; they do not compute coherent cohomology/genus or identify all the requested maps and Euler sums. The unrelated IncidenceAlgebra Euler characteristic and pre-Galois finite fibre cardinality are different notions. Both semantic phrasings were read. All five services/queries succeeded; no unavailable service was reported as absence. The node retains its older searches and appends exactly these new logged searches.

## Review by Q69

I checked delivery-errors B--E against the actual statement, every cited node statement, and the local Stacks sources. Because no new node is needed, B's self-contained-new-statement, tag-duplicate and Mathlib-leaf requirements are vacuous; all item metadata and recorded old searches are retained. No clause of the item is hidden in a new lemma, and all six steps are below 2000 characters.

Step 1 uses `def-sc-invertible-module` to check that the structure module is invertible (identity rank-one trivialization). `lem-trf-proper-field-invertible-coherent` then says exactly that a proper scheme over a field is Noetherian and has coherent structure module, for X and for each C_i. This avoids silently assuming Noetherianity of the arbitrary proper target. `lem-weil-pbc-finite-pushforward-coherent` explicitly requires a finite map and a locally Noetherian target, both now available, and explicitly includes the structure sheaf. `pqf-lem-coherent-ft-locnoeth` gives quasi-coherence of the coherent source module, which the edge theorem actually needs. I read coherent.tex Tags 01XZ (lemma-coherent-Noetherian), 01Y6 (lemma-finite-pushforward-coherent), and the 01T6 preparation recorded in the proper-field lemma. These support precisely the coherence portion, without borrowing unstated higher-image vanishing from 01Y6's narrower DAG statement.

Step 2 writes the disjoint-union sheaf argument, including its inverse, restrictions and scalar actions. It does not need any scheme-image theorem or coproduct-preservation theorem: sections glue over the disjoint open components. Finite tuples have finite support, which identifies product with sum. `lem-weil-pbc-coherent-kernel-cokernel-locnoeth` explicitly says in clause (1) that binary sums of coherent modules are coherent, so finite induction proves coherence of B. The hypothesis is the locally Noetherian X already checked in Step 1. I read coherent.tex Tag 01Y0 (lemma-coherent-abelian-Noetherian) for this closure. The empty product in modules is zero, coherent directly by the definition.

Step 3 uses `def-weil-finite-integral-morphism`, whose statement makes affineness part of finiteness, and `lem-weil-pbc-affine-morphism-cohomology-edge`. I opened the latter statement: it specifies the identity-h-map edge of def-weil-pbc-module-cohomology-fmap(c), not just existence of an abstract cohomology equivalence, and it states global-section-module linearity. I read coherent.tex Tag 089W (lemma-relative-affine-cohomology) and its proof through 01XC and Leray 01F4. Restriction of this scalar linearity to k is elementary: the two structure maps agree after h_i^sharp because h_i is a k-morphism. The same module-derived cohomology is defined by the injective resolutions used in the item, so no etale/pro-etale or coefficient-category identification is being used.

Step 4 uses the explicit smooth proper connected clause of `lem-sc-global-functions`; no separate smooth-implies-reduced lemma is smuggled in, because that case is in its statement. The conclusion is the structure-map bijectivity as a k-algebra, which is stronger than merely naming a vector-space dimension. I read the current global-functions source and the local varieties.tex regular-functions/proper-geometrically-reduced statements. `def-sc-curves` supplies nonemptiness and dimension one for a connected curve. `lem-sc-noetherian-cohomology-above-dimension` states vanishing for every q larger than dimension, unlike the similarly named dimension-one H^2-only node. The source module is quasi-coherent by Step 1 and the curve Noetherian by Step 1, so all of its hypotheses hold. I read cohomology.tex Tag 02UZ (proposition-vanishing-Noetherian). Thus the proof covers all q>1, not merely q=2.

Step 5 checks `lem-pc-euler-characteristic-well-defined` on the proper schemes X and C_i with the coherent modules already established. Its statement supplies both finite dimensionality and finitely many nonzero degrees, justifying equality of the Euler sums under the linear isomorphisms of Step 3. `def-sc-genus` explicitly defines g_i as dim H^1; the latest blueprint uses the equivalent differential-space presentation, also present in the DAG statement, so this is no change of mathematical genus. I read curves.tex Tag 0BY7 (definition-genus) and the arithmetic-genus discussion immediately following it, as well as the varieties.tex Euler definition and finiteness paragraph. `def-pc-euler-characteristic` then reduces the sum to 1-g_i. Neither the genus nor Euler definition is cited to prove vanishing or finiteness it does not state.

Step 6 uses only the short exact sequence clause of `lem-pc-euler-additive`; I read its entire statement and varieties.tex Tag 08AA (lemma-euler-characteristic-additive), including its long-exact proof. The split sequence is explicitly written, and all partial sums are coherent by Step 2; X is proper by hypothesis. Induction gives the finite sum, and integer arithmetic gives the displayed cardinality-minus-genus formula. For the empty family, sections on the empty scheme are the zero module and the zero injective resolution computes zero cohomology by `def-sc-ringed-space-module-cohomology`; substituting in `def-pc-euler-characteristic` gives zero. Thus neither additivity nor a cohomological finiteness theorem is being applied to an unverified object.

I tested the empty family (even X empty), one curve mapped identically, two copies with the same finite map, and a finite map of degree greater than one to a proper curve. The formula counts source genera and does not multiply by the map's degree; the affine cohomology theorem explains why. A finite map into a higher-dimensional or nonreduced proper target changes none of the hypotheses used. Nonreducedness is allowed on X, while smoothness is used exactly through the smooth-curve clause of global functions on C_i. These checks found no statement dispute.

All off-unit theorem uses are declared as generic tools in split_report.tool_uses, with their precise purpose. There is no change to the trace unit proof. The citations file copies the node statements verbatim; every cited statement was read to ensure it actually contains the clause used (C4), and every non-elementary input appears in uses (C1). No new theorem is an elementary step, duplicate, restated clause, or already-available Mathlib theorem. No prohibited SGA route occurs.

## Unfinished work

None in this stage-1 split; stage-1 delivery validation and push are performed with the required delivery tool.
