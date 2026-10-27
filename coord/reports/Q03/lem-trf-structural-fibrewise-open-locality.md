# Worker report: lem-trf-structural-fibrewise-open-locality

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-structural-fibrewise-open-locality.json`: statement, now split into seven proof steps; no Mathlib declaration states the entire assertion. Its statement and existing metadata are retained.
- `citations.json`: seventeen step/node records, quoting the cited statements verbatim.
- `searches.jsonl`: actual search records from msearch.py; the item's inherited searches and their results are retained in its JSON as well.
- `report.md`: this report. `prepare.py` is the sandbox-only preparation script, not a DAG delivery file.

There are **0 new nodes and 0 new Mathlib leaves**. The proof reuses existing definitions and Mathlib leaves rather than creating nodes for individual clauses or for elementary pullback arguments.

## Attachments

None. I searched `lean/WeilConjectures/` for the item's blueprint tag, structural/fibrewise locality, geometric-fibre/open restriction, smooth-locus and finite-presentation locality terminology. The smooth-locus lemmas in `Mathlib/AlgebraicGeometry/Morphisms/SmoothFiber.lean` and the finite-presentation files in the project give ingredients, not the combined statement with an arbitrary isomorphism-invariant diagram predicate. A project declaration proving only an ingredient is not an attachment for this item.

## WANTED

None.

## Audit of the imported item

No statement dispute or statement change. The original item has no proof steps; its source explicitly calls this an agent-written assembly of the structural and geometric-fibre arguments. The proof now distinguishes finite presentation from local finite presentation, tests the diagonal for quasi-compactness, and identifies whole fibres over a point of an open neighbourhood. The latter cannot be replaced by a claim about just an open part of a fibre.

I read the chapter and unit records, the three-level rule in SETUP.md, and the latest blueprint's `sec-trace-formula/sk-i-curve-zero/_section.md` and `lem-trf-local-term-locality.md`, at the latest snapshot recorded in COMMITS.txt. The current ancestor is a local-term statement rather than a separate geometric locality theorem. This item is the auxiliary open-locality argument in the recorded semistable-marked-curve dependency chain; the split preserves that route and adds no alternative purity or trace source. This item is not the unit's key statement, so no unit record is changed.

## Unfinished work

None for this one-level split. All non-elementary ingredients are already existing nodes, and no new unsplit lemma is required. The proof origin remains agent-written assembly, rather than claiming that Stacks contains the entire combined assertion verbatim.

## Not duplicates

No new nodes. Whole-DAG searches by locality terminology and source tags found and reused `lem-weil-pbc-closed-finite-etale-zariski-local`, `lem-sfb-separated-lfp-target-open-locality`, `lem-pc-quasi-compact-local-on-target`, `lem-weil-pbc-qcqs-morphism-permanence`, `lem-weil-pbc-morphism-factors-through-open-subscheme` and `lem-weil-pbc-smooth-restrict-open-subschemes`. Blueprint searches via `tools/blueprint_refs.py search` for structural, smooth locus, geometric fibre, quasi-compact, finite presentation and flatness did not find a blueprint statement of the whole item. Thus `same_as` is empty. The related broad algebraic-space fppf locality node is unnecessary: the proof works directly with schemes and an arbitrary open cover.

## Mathlib searches

All fresh Mathlib searches used msearch.py, with their actual records appended to searches.jsonl and the item. LeanSearch was available for the geometric-fibre restriction query and returned generic locality/restriction and stalk-isomorphism declarations. Loogle found `AlgebraicGeometry.IsZariskiLocalAtTarget.iff_of_openCover`. The grep found target-locality applications and quasi-separatedness material. The first LeanFinder phrasing returned general morphism-property locality; the second, more specific phrasing returned fibre maps, restricted-cover maps and a diagonal restriction isomorphism. None states the entire item. The inherited unavailable LeanSearch query remains explicitly unavailable; its older failure is not treated as evidence of absence.

I read the returned theorem in `Mathlib/AlgebraicGeometry/Morphisms/Basic.lean:145-166`, the local finite presentation class and locality/base-change setup in `Morphisms/FinitePresentation.lean:35-85`, and the quasi-compact-diagonal definition and locality/base-change setup in `Morphisms/QuasiSeparated.lean:50-125`. The existing Mathlib leaves cover these ingredients. No new Mathlib leaf is asserted.

## Review by Q03

I read delivery-errors B through E in full and checked the seven steps against the node statements, not their proofs. For the item I read Stacks `morphisms.tex`, Tag 01TP (`definition-finite-presentation`) and Tag 01TQ (`lemma-locally-finite-presentation-characterize`), Tag 01U3 (`definition-flat`) and its following flatness locality lemmas, Tag 01QO (`lemma-closed-immersion`), and `definition-smooth`/`lemma-smooth-characterize`. These support the conventions and locality used here. I also read the cited existing nodes, including their Mathlib matches. There are no new nodes needing separate sources or edge-case reviews.

Step 1 cites the fibre-product universal property, the actual definition of open immersion, and the open-factorization lemma. The last lemma explicitly supplies existence AND uniqueness when the image is contained in the open. Applying it to maps to the inverse-image open verifies the pullback identification with both projections. The stalk statement is the elementary cofinal-neighbourhood calculation for an open restriction; it is not a base-change theorem about arbitrary stalks.

Step 2 uses exactly the local-ring criterion stated by `def-weil-flat-morphism`. The source and target local rings and the map between them are unchanged in Step 1. Covering supplies an index for each source point. Neither finite presentation nor any condition on the other structural morphism is used to deduce flatness.

Step 3 uses the finite-presentation definition in `def-sbc-locally-finite-presentation`, the diagonal definition in `def-weil-quasi-separated-morphism`, clause (3) (arbitrary base change) of `lem-weil-pbc-qcqs-morphism-permanence`, the local-finite-presentation clause (not the separatedness clause) of `lem-sfb-separated-lfp-target-open-locality`, and the implication actually stated in `lem-pc-quasi-compact-local-on-target`. The last node is used only for descent. Its first application has target S; its second has target Y ×_S Y, covered by its inverse images of S_i. No affine-intersection or quasi-separated-base hypothesis is used. The identification of the restricted diagonal is written using pairs of maps and the cited fibre-product uniqueness, so it hides no independent diagonal theorem. This repairs the main potential omission: quasi-compactness of the morphism alone does not give finite presentation.

Step 4 uses clauses (1) and (3) of `lem-weil-pbc-closed-finite-etale-zariski-local`. For the first application the target cover is C_i, not S_i; the equality j^{-1}(C_i) = F_i uses the stipulated relation q = p composed with j. For the second application the target is S. The cited node states both equivalences without additional finiteness assumptions.

Step 5 uses `def-pc-fibre-product` to give inverse maps and `def-weil-pure-dimension` to read dimension via chains in irreducible components. The same residue field is used on both bases. The constructed scheme isomorphism preserves the complete fibre, its components and their chains; no dimension theorem for a proper open subset or a field extension is needed.

Step 6 uses `def-sbc-smooth-morphisms` for the smooth notion and clauses (a) and (b) of `lem-weil-pbc-smooth-restrict-open-subschemes`. In the forward direction the neighbourhood is intersected with C_i before restricting the target to S_i. In the reverse direction a neighbourhood open in C_i is open in C, and clause (b) composes its smooth map with the open S_i → S. Thus smooth neighbourhoods correspond at each point, which proves the smooth-locus comparison even when p is not globally smooth, flat or locally finitely presented. Only then is the comparison applied to points of the marking. I did not assume smooth-locus base change for arbitrary base change.

Step 7 uses the geometric-fibre definition, which explicitly fixes an algebraic closure, and the same fibre-product universal property. Both arrows j and r commute with the comparison isomorphisms because their projections agree. The isomorphisms are over the same field Omega. The asserted hypothesis on P suffices; invariance under field extension is never added. The two quantifier implications each locate a point in a member of the cover, and the conjunction assertion follows from the separate equivalences, with no use of one structural condition to prove another.

I tested the empty cover (hence empty base), empty fibres, empty marking, an infinite open cover of a non-quasi-compact base, and nonproper/nonseparated curves. The diagonal argument applies without separatedness; the relative quasi-compactness locality theorem does not claim that the entire source is quasi-compact. Empty marking makes the image-containment condition vacuous. Allowing e > 0 simultaneously with nonempty etale marking may give no examples, but does not affect the separate equivalences or the subset assertion. Every proof step has fewer than 2000 characters; the pullback and diagonal comparisons are elementary universal-property arguments, not suppressed source lemmas. No new clause-restatement node, hollow definition, source-route substitution, or unsupported non-elementary citation was introduced.

All seventeen citations have verbatim statement quotations in citations.json. Off-unit ingredients are Mathlib leaves or definitions, so no off-route statement tool declaration is necessary.
