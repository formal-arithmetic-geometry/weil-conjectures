# Worker report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-line-quotient-chart-inverse-pullback.json`: item, statement, split into eight steps; not a Mathlib leaf. Statement and statement dependencies unchanged. No new nodes and no Mathlib leaves created.
- `citations.json`: 24 entries, one for every step/node citation, checked literally against the current cited statement.
- `report.md`: this report. `searches.jsonl` is the search command's unmodified log; `write_split.py` is sandbox-only preparation code, not a delivery node.

## Attachments

None for the item. Searches in the whole upstream `lean/WeilConjectures/` tree for the blueprint id, tautological quotients, line quotients, and projective-bundle notions found no declaration giving the item. `ProjectiveSpace/OfInvertible.lean` constructs maps from generating sections to free projective space and its twist isomorphism, not the arbitrary quasi-coherent symmetric-Proj statement with both inverse identities and arbitrary pullback. No claim is based on a sorried upstream theorem. I reuse the existing invertible-pullback node (already audited closed) and the existing map-gluing theorem through their nodes.

## WANTED

None. All mathematical sources used are available in `literature/stacks-project/`.

## Issues found and corrected

The imported item had a detailed true statement and no proof. Its neighboring fraction-map construction is sufficient to establish the inverse identities by calculations, without adding another classification lemma that merely restates an item clause. No statement dispute or change was needed. A source citation drafted as Tag 01M9 was corrected to Tag 01M4 after checking the tag-label table: 01M9 is an unrelated global-sections remark. The final steps name tags and labels, not mutable section numbers.

## Unfinished work

None within stage 1. This delivery does not assert any new Lean proof. The statement-only fraction-map prerequisite remains another item's responsibility, as permitted by a one-level split.

## Not duplicates

No new nodes. Whole-blueprint searches for `projective bundle`, `invertible quotient`, `pullback invertible`, and `homogeneous fraction` found no imported node equivalent to this item. The projective-bundle hit concerns a Thom class, and the homogeneous-fraction hit concerns a Rees-algebra blowup chart; neither states the present inverse operations. DAG searches found and reused the existing pullback, chart, twist, and module-map gluing nodes. The parent `lem-trf-projective-bundle-quotient-geometry` uses this item and is not used back in this proof; no cycle is introduced. The sibling tautological-chart-gluing node is not used to infer properties for an arbitrary datum from the existence of one datum: Step 2 derives the needed frames directly from the normalization definition and twist formulas.

## Mathlib searches

The inherited five records are retained. I ran five further queries through the required `msearch.py` command and read their results in `searches.jsonl`: two LeanFinder phrasings, the Loogle query for `AlgebraicGeometry.Proj.fromOfGlobalSections_morphismRestrict`, a grep in `AlgebraicGeometry`, and a LeanSearch query for the inverse classification and pullback identities. Every service answered. I read `Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Basic.lean` around lines 250-305 and 440-515. `pullbackAwayιIso` concerns the intersection of absolute Proj charts. `fromOfGlobalSections` and its restriction lemma construct an absolute Proj map from a ring map into global functions. These do not state the line-sheaf inverse comparison for an arbitrary quasi-coherent module, so the item is not a Mathlib leaf. The other hits concern categorical quotients, functor pullbacks, or unrelated inverse natural transformations. No unrun search was added, and the command's log was not edited.

## Review by Q48

I read the chapter and unit records, the item's ancestor/parent route, the normalization definition, and every cited node's statement. The item is the projective-bundle tool needed by the already recorded fibrewise-ampleness route below the local-term ancestor. It does not change the chapter or the smooth-curve unit's route. I read Stacks `constructions.tex`, Tag 01OA (section-projective-bundle), particularly its explicit allowance of arbitrary quasi-coherent E and its two inverse quotient operations, and Tag 01O4 (lemma-apply-relative). The explicit coordinate expansions are agent-written, recorded as such in `proof_origin`. No SGA source is used.

For Step 1 I checked that the definition provides both invertibility and a surjection. The invertible-pullback node explicitly allows every scheme morphism and gives local triviality on inverse-image opens. Clause (1) of the epi/direct-sum node preserves epimorphisms, with no flatness assumption. The composition node supplies a natural isomorphism, not an unjustified equality of functors. Its naturality identifies the pulled quotient used here. I also read Modules Tags 0B8L (lemma-pullback-invertible), 01AJ (lemma-exactness-pushforward-pullback), and Sheaves Tag 0097 (lemma-push-pull-composition-modules).

For Step 2 the relative-Proj definition supplies the absolute models on all affine base opens. The canonical symmetric grading specifies its degree-d part as products of degree-one images, so the standard-open covering criterion applies even for an infinite module. The standard-open node gives both the affine coordinate ring and the covering criterion. The quotient-datum definition specifies its isomorphism to the degree-one twist and its images of module sections. The twist definition specifies exactly the degree-one localization module. Thus multiplication/division by e proves the frame formula for ANY normalized datum; this is a two-line calculation in a ring where e is inverted, valid also for empty charts. I read Constructions Tag 01M4 (lemma-standard-open) and checked its label against the tags table. I do not invoke an existence theorem as uniqueness of all normalized data.

Step 3 uses the fraction-map statement's actual covering and formula, not anything hidden in its proof. Its rho sends iota(v)/e to b_v/b_m. The affine-sections node states the natural isomorphism with pure tensors and sends a tensor to the scalar times the pulled section, so it supplies the pulled-frame interpretation. I read Schemes Tag 01I9 (lemma-widetilde-pullback). The local comparison and its inverse are explicitly written; cancellation of b_m is legal only on D(b_m). The quotient equality follows on pure tensors and therefore everywhere. This is elementary once those stated interfaces are used.

Step 4 first computes the overlap ratio, using the fraction-map statement, and checks the equality on frames. For different base/frame choices it uses cancellation of the pulled surjection, whose preservation under restriction is precisely clause (1) of the cited epi node applied to an open immersion. The cited Hom-cover gluing node asserts existence AND uniqueness of local module maps; the object-gluing node alone would not have sufficed. I read Sites Modules Tag 03EM (lemma-internal-hom) and the existing upstream `SheafOfModules.existsUnique_hom_of_cover` interface. The Zariski site has all the required intersections/fibre products and its open family covers T. Gluing inverses proves the global map is an isomorphism, rather than assuming gluing preserves isomorphisms. Arbitrary overlaps are handled by refinements, never by an assumption that intersections of affines are affine.

Step 5 again uses affine-section naturality, the specified symmetric grading, and the complete fraction-map statement. The coefficient of e is 1 in the frame a*e. I checked products of degree-one generators, scalars, and their sums: the degree-d coefficient is exactly a*(c/e^d). Every degree-zero localized element has that form, so both scheme maps have precisely the same chart maps in the fraction-map construction; its uniqueness applies. No separate classification theorem, parent node, or sibling inverse lemma is assumed. Step 6 uses that same construction's uniqueness of the induced graded map and of the glued morphism. In the frames l and v(l) all coefficients agree, which proves invariance directly. These steps establish the two inverse identities, not copies of them under new node names.

For Step 7 the affine-sections node and the natural composition isomorphism apply to arbitrary u and to affine refinements W' of u^{-1}W; no claim that the full inverse image is affine is made. I checked b'_m=t(b_m), and checked b'(z)=t(b(z)) first on products, then on their finite sums. The composite localized ring map sends b(z)/b_m^d to t(b(z))/t(b_m)^d because units and their inverses are preserved. Thus the fraction-map node's actual chart maps coincide, including their domains D(t(b_m)), and its gluing uniqueness proves the morphism equality. Step 8 compares both module maps on the frame e and uses exactly uniqueness in the cited Hom-cover gluing statement. It proves the theta pullback equality and the value u*q(m), rather than asserting vaguely that a comparison transports.

I checked empty S and T, E=0, the rank-one case, infinitely generated M, nilpotent/zero b_m, and the non-flat map Z -> Z/2 on chart coefficients. For E=0, P is empty and a surjection 0 -> L to a line forces T empty; the claims become the unique empty maps. A zero or nilpotent b_m gives an empty chart, on which its displayed localization and module maps remain valid. For rank one the single normalized coefficient is 1 and both recovered maps are identities locally. Surjectivity supplies an open cover, not a chosen finite generating set for E. Under Z -> Z/2 the same fraction formula is defined on D(image b_m), possibly empty; none of the arguments tensors a kernel or uses left exactness. Changes of frame by a unit cancel with the appropriate homogeneous degree. These checks found no missing hypothesis.

I checked delivery-errors B-E point by point: no statement-only node contains a proof, no new undefined notions or duplicate nodes were added, every non-elementary input is a cited statement, all cited statements were opened, no proof text is used as an unstated interface, and the only elementary steps are the written scalar/frame calculations. All eight steps have fewer than 2000 characters; none hides a new comparison lemma or a source's omitted standard argument. The generic off-unit tools are explained individually in `split_report.tool_uses`; the delivery does not write top-level `tool_uses`.

## Validation

The server `review_split` check passed before this report was written, with zero new nodes. The final required `deliver.py --no-push` and direct push are run after this report and the citation correction are complete.
