# Stage-1 report: lem-a1-space-affine-etale-cover

## Files written

- `dag/nodes/sec-purity-real-sheaves/lem-a1-space-affine-etale-cover.json` — target split, no new child nodes, Mathlib verdict: no exact algebraic-space match.
- `citations.json` — verbatim statement citations for every proof-step use.

## Attachments

No new Lean declaration attachment. Existing declarations/nodes used as statements are cited in the proof.

## WANTED

None.

## Not duplicates

No new nodes were created. The target differs from `lem-a1-space-affine-atlas-open-cover`: that node gives a Zariski family of open subspaces with individual affine etale charts, while this target forms one disjoint-union atlas and proves its quotient topology and functorial point-topology properties.

The target differs from `lem-a1-space-etale-open-image`: that node packages open-subspace correspondence and open images for algebraic-space etale maps; this target additionally constructs the disjoint-union atlas, proves quotient-topology independence, continuity for every scheme map, and openness for representable etale maps.

## Prior review by NY (returned version)

I read the target source in `literature/stacks-project/spaces-properties.tex`: Tag 03FX (the disjoint-union affine etale cover) and Tag 03BX (quotient topology, independence of atlas, continuity, and openness), together with the common-field point formulation in Tag 03H4. I also read the complete statements of every cited node: `lem-a1-space-affine-atlas-open-cover`, `lem-a1-space-etale-open-image`, `lem-a1-space-fibre-product-point`, `def-trf-algebraic-space`, `def-weil-etale-morphism`, `lem-weil-pbc-scheme-coproduct-family`, `lem-weil-pbc-open-immersion-base-change`, `lem-weil-pbc-etale-composition-cancellation`, and `lem-weil-pbc-etale-morphism-open-map`.

Step 1 explicitly forms the coproduct of the affine charts, checks representable etaleness after every scheme base change using open-immersion base change and etale composition, and checks surjectivity pointwise with the fibre-product criterion. It retains the affine-open factorization over $S$. Step 2 checks atlas independence by the scheme fibre product of two etale atlases; both projections are etale and open, and the common-field point relation gives the two quotient preimage equalities. Step 3 verifies continuity by pulling an open subset back to the fibre product and pushing it through the surjective etale projection to the test scheme. Step 4 verifies openness in the same fibre-product square, with the pointwise image equality spelled out. All hypotheses (scheme test objects, representability, surjectivity, and common-field equivalence of points) are used where stated. I kept the imported target statement unchanged and added no clause-restating child node.

The Mathlib searches for this item were rerun with `msearch.py` and recorded in `searches.jsonl`: grep found no algebraic-space declaration, Loogle had no `AlgebraicSpace` identifier, LeanSearch returned only scheme affine-cover declarations, and LeanFinder returned only scheme-cover/immersion declarations. No Mathlib leaf applies to the full statement.

## What could not be finished

No mathematical work remains; the repaired delivery must pass the required remote dry run before pushing.

## Return repair (2026-10-18)

Returned delivery: `9bdbf37c2f`. The first required dry run of the retained split reproduced stale verbatim quotes for `lem-a1-space-fibre-product-point` at old steps 1, 3 and 4. I compared the retained item with current main: the statement, statement dependencies, source, blueprint ancestry and recorded searches agree; only the split-owned proof/status/report fields differ. I retained the previous report above and the search log, read all current cited statements, and regenerated the quote list from those statements. The delivered proof now has five steps.

The changed point lemma was repaired by its maintainer reader: its old TeX contained decoded TABs, its point/field/surjectivity notions now cite their definitions, and it now explicitly says that the sheaf fibre product is represented by a scheme. The common-field lifting and final surjectivity conclusions are unchanged mathematically. New steps 3–5 use precisely these scheme-representability and point-lifting clauses. Step 3 corrects the projection used to transfer openness from V to W: Q to W is the base change of the second atlas p.

Re-reading current nodes also found that `lem-a1-space-etale-open-image` now explicitly depends on this item. I removed its unnecessary citation in atlas independence. The next remote dry run exposed an indirect cycle as well: this item to `lem-a1-space-affine-atlas-open-cover` to `lem-a1-etale-scheme-map-open-image` to `lem-a1-space-etale-open-image` to this item. I read all these current statements and proof dependencies, and removed the affine-atlas-open-cover citation too. New steps 1–2 follow the original Tag 03FX proof directly, starting from the atlas in the definition, refining it by affine opens, and forming a disjoint union. This is the cited source's own construction, with no detour through any open-image theorem. No other node is edited. All remaining previous quotations agree with current statements. `citation-revalidation.json` retains the statements read in this repair.

## Review by NY

I reread Stacks `spaces-properties.tex`, Tag 03FX (`lemma-cover-by-union-affines`, lines 701–723), Tag 03FY (`lemma-union-of-quasi-compact`, lines 726–745), Tag 03BX (`lemma-topology-points`, lines 379–457), and Tag 03H4 (`lemma-points-cartesian`, lines 281–309), checking tag/label pairs in `tags/tags`. I also read the affine-basis assertion in `schemes.tex`, Tag 01IT (`lemma-basis-affine-opens`, lines 1952–1955), and the full statements of the existing affine-basis and open-factorization leaves. The item's statement remains unchanged and matches the same source clauses. No new node, definition or source is introduced. The fixed chapter and unit records are unchanged.

Step 1 takes an atlas from `def-trf-algebraic-space`, affine opens of S and of inverse images in V from `lem-weil-pbc-affine-opens-basis`, the factorization of each U_v to S_v from `lem-weil-pbc-morphism-factors-through-open-subscheme`, and the actual coproduct scheme with its disjoint open components from `lem-weil-pbc-scheme-coproduct-family`. The index is the set of points of the atlas scheme; no finite-type or quasi-compact hypothesis is required. This replaces the old affine-atlas-open-cover citation, not a clause of the conclusion.

Step 2 uses the scheme-test clauses in `def-trf-algebraic-space` to get the surjective etale P to T, open-immersion base change from its named lemma, open-immersion etaleness and composition from `lem-weil-pbc-etale-composition-cancellation`, the coproduct-scheme statement, and the affine-local definition of etaleness in `def-weil-etale-morphism`. The representation of T times_E W is checked by decomposing a test scheme into its inverse images of the disjoint open components. The pullbacks P_v cover P, so their coproduct surjects onto T. Taking a field-valued scheme test proves point-surjectivity of the atlas separately. These are routine gluing and point arguments written out; no non-elementary source descent is inferred.

Step 3 cites the current `lem-a1-space-fibre-product-point` for scheme representability and compatible point lifting, `def-trf-algebraic-space` for both projections being surjective etale, and `lem-weil-pbc-etale-morphism-open-map` for openness of each projection. The image/inverse-image equality is proved pointwise. A lift of x in W uses p, the other atlas; swapping atlases proves both directions. There is no dependency on an algebraic-space open-image theorem.

Step 4 uses the same three statements: Q is a scheme, Q to T is surjective etale, and images of open subsets of Q are open. The pullback of the atlas-open inverse image is open because morphisms of schemes are continuous, and its image is the desired inverse image on T by point lifting. Step 5 uses representable etaleness of t to make Q to W etale, so its image of the inverse image of B is open; the point lemma identifies that image with the inverse image of t(B). Quotient openness proves the claim without requiring t to be surjective. Both inputs to each application of the point lemma are schemes over the same S; no separatedness or Noetherian hypothesis is used.

I checked the empty algebraic space (empty atlas and empty affine family), the scheme case with identity atlas, a non-surjective etale test map, and point representatives over different fields: 03H4 requires a common extension and does not identify the original residue fields. Every step is below 2000 characters, and no long step hides a separate lemma. For B–E: there are no new-node shape, search or duplicate obligations; all non-elementary uses have existing cited statements, every use has a current verbatim quotation, and both direct and indirect cyclic routes were removed rather than rebased unchanged. The final construction follows 03FX's proof, avoiding the reverse 03FY implication. No statement is disputed and no SGA source is used. The prior four Mathlib searches are reused exactly as logged, not claimed to have run anew; the Lean-source searches for the blueprint tag, algebraic spaces and the affine-atlas notion found no project declaration stating the item. No new nodes or Mathlib leaves were added.
