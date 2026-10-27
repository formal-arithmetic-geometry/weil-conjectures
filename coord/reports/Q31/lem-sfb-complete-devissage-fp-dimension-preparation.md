# Stage-1 report: lem-sfb-complete-devissage-fp-dimension-preparation

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-complete-devissage-fp-dimension-preparation.json`: statement, split; all needed facts already have DAG nodes. No new nodes and no new Mathlib leaves.
- `citations.json`: one verbatim statement quotation for every node used by every proof step.
- `searches.jsonl`: searches run with the required msearch.py command; the item's earlier search records are retained, and this worker's actual logged searches are appended to its mathlib_searches.
- `report.md`: this report. `write_split.py` is a sandbox-only writing helper, not a delivered node or modified launcher script.

## Attachments

None. Searches of `lean/WeilConjectures/` by the item's blueprint tag and by algebra/complete-devissage terminology found no declaration stating the item. The existing `lean/Sheaf/TraceFormula/CompleteAlgebraDevissage.lean` defines the input structure; it does not prove the preparation theorem. It is not an attachment. No Lean was written and no compiler or Lake was run.

## WANTED

None. All Stacks sources needed for this split are present locally.

## Corrections and scope

The statement is unchanged. The imported proof was empty, so it did not justify either the module finite-presentation propagation or the base shrinking. The new proof supplies both. In particular it does not identify fibre dimension at a point with the dimension of a local ring. It uses local topological fibre dimension and smooth relative dimension, then the theorem giving global topological dimension over a field.

The source is `flat.tex` Tag 05HY, Remark `remark-finite-presentation`, read together with Definition 05HX and the preliminary dimension discussion in Lemma 05UF. I also read Algebra 00F4, 0564, 0519, 00CS, 00E3, Morphisms 01TQ, 01VF, 056G, 02G1, 02G2, 02NK, 01S7, 01S8, Varieties 056T and 0A21, and Schemes 01I4. The quotient-presentation argument and open-image shrinking argument are written explicitly, with agent proof origin. The local smoothness/dimension statements and the field-extension dimension theorem are cited through their existing nodes; the source Lean theorem `topologicalKrullDim_eq_of_smoothOfRelativeDimension` was read at its current lines 304ff, rather than trusting the older line numbers in its node.

The whole-DAG/blueprint searches found existing general results for all ingredients. Blueprint searches used `tools/blueprint_refs.py search` with devissage, finite presentation, and smooth relative dimension; the current blueprint's constructible-stability direct-image paragraph and smooth local-constancy proof were read from `literature/blueprint/latest/`. There is no other blueprint statement equivalent to the complete preparation item. The ancestor command reports null, consistent with the inherited created-item chain; its existing detailed from.place and via fields are retained. No unit or chapter record was changed.

## Not duplicates

There are no new nodes. In particular, I reused the finite-extension equivalence, finite-presentation permanence, local fibre-dimension constancy, smooth connected-fibre integrality, smooth relative-dimension base change, affine fibre-product formula, and closed irreducible dimension/transcendence nodes. I did not create a node for the finite-relations quotient calculation or the two-open-set constancy argument: each is an elementary step from the cited definitions and results.

## Review by Q31

I read delivery-errors B through E in full and checked the actual cited statements, not just their titles or their proofs. Every proof dependency is an existing unmerged node, and citations.json quotes its statement verbatim. No new statement-only node, duplicated source-tag node, or clause of the item has been manufactured. The largest step is under 1300 characters, so there is no non-elementary step above the 2000-character review threshold.

Step 1 takes smoothness and the displayed surjective finite-presentation maps from `def-trf-complete-algebra-devissage`. `lem-pc-smooth-flat` really supplies both flatness and local finite presentation. `lem-weil-pbc-lfp-affine-opens-finite-presentation` applies to the entire affine source and target, and clause (2) of `lem-weil-pbc-finite-presentation-base-change-composition` supplies exactly the compositions needed for A_1 and the later A_i. The zero-length case is separated before indexed choices.

Step 2 uses the statement of `lem-weil-pbc-finite-presentation-over-finite-type-algebra`, with R as base, B_i as finite type intermediate algebra and A_i as finitely presented target. This is not an inference that finite algebras are automatically finitely presented. Finite presentation of the target over R was established in step 1. The algebra definition supplies the finite generating set of B_i.

Step 3 writes out the elementary finite-relations argument from `def-sc-finitely-presented-module`: append lifts of the finitely many images of a free basis to the relation matrix. There is no claim that an arbitrary submodule of a finitely presented module is finitely presented.

Step 4 uses `lem-trf-finite-extension-module-finite-presentation`, whose statement is an equivalence for an arbitrary module under a finite, finitely presented ring map. I checked finiteness and finite presentation each time: A to A_1 and B_i to A_{i+1} are surjective maps, hence finite; B_i to A_i is finite in the definition and finitely presented by step 2. The induction assertion is finite presentation over A_i. It then gives finite presentation over B_i, step 3 gives that of Q_i, and only then is the assertion transferred to A_{i+1}. No coherence or Noetherian assumption is inserted.

Step 5 uses exactly the local constancy and finite differential-rank content in `sbc-lem-smooth-relative-dimension-locally-constant`. Geometric irreducibility comes from the devissage definition, with its meaning supplied by `def-pc-geometrically-irreducible` and `def-weil-irreducible-components`. The latter explicitly includes nonemptiness. The restriction to a fibre is locally constant; two values would separate an irreducible space. This establishes a_i as a finite nonnegative integer and makes no comparison between indices.

Step 6 uses the actual open-map conclusion of `lem-weil-pbc-flat-lfp-open`, whose flat and locally-finite-presentation hypotheses were obtained in step 1. The level-set image is open, contains the specified prime, and has exactly the level set as its inverse image because constancy was proved on each fibre. The common shrinking is one principal open: write the complement of the finite intersection as V(I) and choose f in I outside the prime. This is a finite intersection over the devissage length, not an unjustified infinite shrinking.

Step 7 uses `lem-weil-pbc-localization-spectrum-embedding` for the identification of spectra with the principal open, and `lem-weil-pbc-localization-prime-residue-field-iso` for the residue fields. I added `lem-weil-pbc-fibre-product-affine-spectra` during self-review so the affine fibre-ring identification is supported by an actual theorem, not only the definition of fibre product. The tensor-localization ring isomorphism itself is given on elementary tensors and fractions. Smooth base change is clause (2) of `lem-pc-proper-base-change`, which does state smoothness despite its title. `pqf-lem-affine-local-target` applies to the one-member affine target cover; `lem-weil-pbc-affine-morphism-permanence` then provides quasi-compactness and quasi-separatedness. Together with local finite presentation, these are exactly scheme finite presentation in `def-sbc-locally-finite-presentation`.

Step 8 verifies localization of the first, successor, finite-algebra, cokernel and last-zero conditions. Finite generating lists and surjectivity are checked on fractions; the ring finite-presentation base-change clause has exactly the required hypothesis. `lem-weil-pbc-localization-module-exact` is an algebraic module theorem, not a similarly named sheaf theorem. It identifies the localized cokernel with the cokernel of the localized map. The fibres over surviving base primes have the same residue fields, so their geometric irreducibility persists.

Step 9 verifies the residue-basis condition separately. Nonemptiness of the prime fibre rules out an element outside the base prime becoming an element of its extended ideal: in that fibre it would be both a unit and zero. The prime-localization/residue-field node gives both primality and the field identification. I wrote the tensor identification as m/f^k tensor c mapping to m tensor f^{-k}c, so the localized residue map is the original isomorphism, rather than an unspecified transported map. All eight defining conditions of the devissage have therefore been checked.

Step 10 applies `lem-trf-smooth-connected-fibre-normal-integrality`, whose statement permits arbitrary bases and every extension of the residue fields. Its geometrically connected and nonempty hypotheses follow from geometric irreducibility by the explicit two-closed-set argument. Its stronger normality conclusion is not needed. This avoids treating smoothness as though geometric reducedness were part of its definition.

Step 11 uses `lem-sc-fibre-dimension-after-base-change` for the identification of the fibre over t with the extension of the fibre over its image s. `lem-sbc-smooth-relative-dimension-permanence` applies to the smooth morphism with relative dimension a_i from step 7. The nonemptiness hypothesis of `lem-sbc-smooth-fixed-dimension-over-field` is verified by integrality, not omitted. The arbitrary scheme T need not be Noetherian, quasi-compact, or of finite type.

Step 12 uses the affine fibre-product theorem and the algebra finite-presentation base-change theorem to put the fibre in the finite-type-over-a-field scope of `lem-sc-closed-irreducible-dimension-trdeg`. I checked both applications of that statement: the whole integral fibre with generic point (0), and the closure of an arbitrary point, which is a nonempty irreducible closed subset whose generic point is that point. The inequality for the latter follows by viewing every chain in a closed subset as a chain in the ambient space, directly from `def-kun-topological-krull-dimension`; no open-subspace monotonicity theorem is misapplied to a closed subset.

I tested the zero-length devissage (f=1), a zero-rank free map and zero module, relative dimension zero, field bases, nonreduced/non-Noetherian bases, and arbitrary residue-field extensions. In particular no decreasing-dimension assertion is available from this algebraic definition alone: over a field take N=0, B_1=A_1=A_2=k[t], B_2=k[t,u,v], the identity B_1 to A_2, the quotient B_2 to A_2 killing u,v, zero M_i and r_i=0. This is a length-two devissage with dimensions 1 and 3. The item's explicit refusal to assert inequalities is therefore essential and has been preserved. The split stays on the inherited Stacks 05UF preparation route; off-unit statements are declared as generic tool uses in split_report.

## Unfinished work

None within this stage-1 item. Existing input nodes retain their current status and are not re-split here. Delivery is subject to the required server preflight and independent maintainer review.
