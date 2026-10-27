## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-limit-open-cover-descent.json: statement split into six proof steps; Mathlib has the scheme inputs, not this algebraic-space assertion. No new nodes; no new Mathlib leaves.
- citations.json: verbatim statements for every cited node, indexed by proof step.

## Attachments

None. Searched lean/WeilConjectures by the exact blueprint tag, AlgebraicSpace, algebraic space, descent/open/limit concepts, including AlgebraicGeometry and SixFunctors. The project has no declaration supplying this algebraic-space statement. Mathlib declarations are not attachments.

## WANTED

None. The Stacks source needed here is present.

## Findings

The statement is correct and unchanged. The imported proof was empty. Tag 0827 descends one open; the finite covering and empty-family clauses need an additional argument, supplied here via an affine atlas and scheme eventual full-open descent. Merely choosing open models does not guarantee that they cover at that stage. It is also unnecessary to descend invariance under the atlas relation: taking the image open has the required pullback by arbitrary base-change compatibility.

The inherited blueprint ancestor is null. tools/blueprint_refs.py ancestor reports that same missing ancestor; the existing explicit place and via chain are retained. The latest blueprint sk-thm-sf-ctf-stability-direct-images.proof.md, labelled det-thm-sf-ctf-stability-direct-images, was read: its proof (3) now assembles proper and open direct images via compactification. This auxiliary limit lemma supports the already recorded descendant route; it does not change the unit or chapter route. No unit realization fields are owned by this non-key item. The stale coord/dag-sync.md reference is absent in this read repository; the current brief's live-repository and direct-delivery rules were followed.

## Not duplicates

No new nodes were created. Whole-DAG searches by 0827, 086W, 07SF, lemma-descend-opens, lemma-limit-nonempty, quasi-compact opens and affine limits were read. Whole-blueprint searches for descend opens, 0827, quasi-compact open, affine transition, and affine limit chart were read. The existing pqf-lem-limit-qc-open-descends is a scheme theorem and is used directly; lem-weil-pbc-spectral-limit-descend-finite-cover concerns abstract spectral spaces and would require a separate algebraic-space topology theorem. Neither is a duplicate of the complete present statement. The parent lem-sfb-space-affine-limits-schematic-stages cites this item, so it is deliberately not used in this proof.

## Review by Q138

I read spaces-limits.tex Tag 07SF (lemma-directed-inverse-system-has-limit), Situation 084R, Tag 0827 (lemma-descend-opens), Tag 07SR (lemma-limit-is-scheme), and Tag 086W (lemma-limit-nonempty). I also read limits.tex Tag 01Z4 (lemma-descend-opens), in particular the finite covering clause; spaces-properties.tex Tags 03BZ, 03E4, 03H6 and 03IR; and spaces-morphisms.tex the qcqs permanence and affine base-change statements. All source hypotheses are present: a small nonempty directed index, affine transitions, and qcqs stages. No Noetherian, finite-presentation, transition-surjectivity, or schematic-stage assumption was introduced.

For step 1, I opened the statements of lem-trf-space-qc-finite-affine-atlas-refinement (one affine atlas, including the empty case), lem-sfb-space-affine-locality (affine base change, composition, etale target detection, affine-over-affine and qcqs permanence), lem-weil-pbc-limit-affine-transition (scheme limit, affine projections and affine coordinate limit), lem-trf-space-fibre-products-etale-covers (base-change covers), and lem-weil-pbc-affine-scheme-qcqs. The chart/limit identification is written out on scheme tests as a compatible family together with its common map to the fixed chart; this avoids using the parent theorem circularly. Cofinal-tail extension and independence are explicitly given. These are formal universal-property arguments, not an unproved geometry lemma.

For step 2, lem-sfb-space-integral-qcqs-permanence expressly states that a quasi-compact open subspace of a quasi-separated space is quasi-separated (its integral clauses are not used). lem-sfb-space-qcqs-source-products expressly supplies the qcqs fibre product of three qcqs spaces. Thus W_a, U, X meet every hypothesis before applying it to E_a. def-a1-space-open-subspace identifies E_a as an open subscheme, and pqf-lem-limit-qc-open-descends gives its scheme model. No assertion from a definition is used as a substitute for a theorem.

Step 3 uses lem-weil-pbc-affine-morphism-permanence for affine base change and quasi-compactness, and the later-open clause of pqf-lem-limit-qc-open-descends. Passing finitely many indices to one upper bound and composing inverse-image equalities is elementary; the empty family chooses i_0. Its cited statements contain precisely the needed permanence assertions.

For step 4, I additionally checked lem-weil-pbc-open-immersion-etale and lem-trf-space-chartwise-etale-permanence so that the restricted atlas map is etale. lem-a1-space-etale-open-image explicitly gives an open image, quasi-compactness of that image, surjection onto it, and compatibility with every algebraic-space base change. The base-change cover lemma makes E_a surjective onto W_a. Hence the image identity holds as open subfunctors, with no use of the proofs of those nodes and no finite-stage saturation assumption.

For step 5, lem-weil-pbc-limit-image-contained-in-open states eventual full inverse image for every open of a quasi-compact scheme stage. I read Mathlib/AlgebraicGeometry/AffineTransitionLimit.lean:178-198; its cofiltered diagram is our directed tail with arrows reversed, and its only geometric hypotheses are affine transitions and compact stages, supplied by step 1. Its open need not be quasi-compact. The surjective atlas and lem-a1-space-point-open-calculus show that cover on the atlas implies full open union on X_i. I checked the empty cover separately: the lemma applied to the empty open forces U_i, hence X_i, empty. This also covers a nonempty inverse system whose limit is empty; no inference that every stage was empty is made.

Step 6 uses the open quasi-separatedness clause of lem-sfb-space-integral-qcqs-permanence, followed by the qcqs-source and base-change clauses of lem-sfb-space-affine-locality. The maps to each descended open are literally affine base changes of the given transitions. The final point/open correspondence from lem-a1-space-point-open-calculus supplies the equality after every later pullback. All definitions agree with the statement's scheme-test conventions.

No new lemma statement required a separate small-case test. I tested the item's construction on a constant system, a single open equal to X, empty members of a nonempty cover, an empty limit with zero covering members, and an initially empty atlas. Each construction and choice of index still applies. All six steps are below 2000 characters; none packages an unstated comparison lemma. The proof-dependency union matches the uses arrays, every cited statement is recorded verbatim in citations.json, and traversing statement/proof dependencies found no path back to this item. Generic off-unit atlas, fibre-product, image and etale-permanence tools are declared in split_report.tool_uses, without changing maintainer-owned tool_uses.

The actual msearch.py results are preserved in the sandbox and appended to the item's pre-existing searches. Both phrasings and the available semantic, Loogle and grep searches were read. The hits exists_preimage_eq (AffineTransitionLimit.lean:341-360) and exists_map_eq_top (182-198) are scheme statements and are already represented by the existing DAG inputs. The combined Loogle query returned zero hits. The compact-open topology hits do not identify algebraic-space limits. No search was invented and no compiler or Lean edit was used. I corrected doubled TeX escaping in the newly written steps before validation.

## Unfinished work

None in the stage-1 split. The existing unsplit cited prerequisites remain independent queue items. Delivery validation is performed by the required server dry run.
