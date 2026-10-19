# Stage-1 delivery: lem-trf-flatification-horizontal-curve-pair

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-flatification-horizontal-curve-pair.json`: item, statement, split into eight complete steps; original statement unchanged; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-flat-dense-generic-fibre-pure-dimension.json`: one new statement-only unsplit general scheme lemma; no Mathlib match. It has no proof or proof dependencies.
- `citations.json`: verbatim statements for every node citation in every item step.
- `report.md`: this report. `searches.jsonl` is the actual search-command log.

## Attachments

None. I searched the slopmaster2 `WeilConjectures/` tree for the exact blueprint tag, flatification/flattening/strict-transform terminology and pure/equidimensional flat families, and checked the available name map. No project declaration supplies every clause. The master checkout is reference material only. No Lean was written or compiled.

## WANTED

None. I read the local ILO PDF and local Stacks TeX sources. The ILO paragraph refers to Raynaud–Gruson, but the exact flattening theorem needed here is available in the local Stacks source, so the original paper is not required for this split.

## Problems and corrections

The item was a statement-only node with no proof. The statement is correct and is unchanged. I filled in the generic-flat open, a single simultaneous blowup, the projectivity conventions, the generic-closure identification, the pure geometric dimensions, and finiteness of the marking. The marking is not assumed flat before flattening and is not assumed finite merely because its generic fibre is finite. In particular I did not claim that a flat reducible horizontal marking has flat irreducible components; the new lemma applies to the whole flat marking instead.

There is an inherited Lean/DAG coverage discrepancy in the *cited* existing node `sk-lem-nagata-sketch-elimination`. Its statement's second paragraph explicitly asserts general 081R flattening for finite-type quasi-separated W flat and locally finitely presented over U, which is precisely what Step 2 uses. Its attached declaration `AlgebraicGeometry.exists_admissibleBlowup_isOpenImmersion_strictTransformMap` (current read-only source `WeilConjectures/Compactification/EliminationOfIndeterminacy.lean:103`) assumes W is an isomorphism over U and concludes an open immersion. The file's header expressly says it avoids flattening. Hence that declaration does NOT establish the separate, general flattening assertion recorded in the DAG statement, despite the node's inherited closed audit. This delivery makes no attachment claim for that clause. Maintainer action is needed to separate/reopen that existing clause or repair its Lean coverage. I reuse the existing asserted theorem rather than create the duplicate explicitly prohibited by the brief, and verify it directly against Stacks 081R.

I corrected two draft source references before delivery: the closure definition is Divisors 080D, not the strict-transform-is-blowup theorem 080E; the zero-fibre-dimension quasi-finiteness criterion is Morphisms 0397, not an algebra tag. No imported statement, blueprint ancestry, unit binding or maintainer field was changed.

## Unfinished work

No part of this item's split remains unfinished. The one new node is deliberately statement-only, as required for a one-level split. Its full proof is the later worker's task. The cited-node Lean coverage discrepancy above is reported for maintenance; it does not change the true natural-language flattening assertion used here.

## Not duplicates

lem-trf-flat-dense-generic-fibre-pure-dimension vs lem-trf-flatification-horizontal-curve-pair: the new lemma assumes a flat family with dense pure-dimensional generic fibre and gives conservation of pure dimension for any d; it constructs no blowup, no strict transform, no horizontal pair, and proves no projectivity or finiteness. The item's existence construction and all its other clauses remain in the eight proof steps. Shared source tag: 0GSJ.

lem-trf-flat-dense-generic-fibre-pure-dimension vs lem-sbc-cohen-macaulay-equidimensional-fibre-pieces: the latter assumes Cohen–Macaulay fibre local rings on an open and decomposes that open into possibly different dimensions. The new lemma assumes generic density and one generic dimension, with no Cohen–Macaulay hypothesis, and proves uniformity on entire fibres. Shared definition tag: 02NJ.

lem-trf-flat-dense-generic-fibre-pure-dimension vs lem-sbc-smooth-relative-dimension-permanence: the latter assumes smoothness and an already fixed relative dimension; the new result assumes only flatness and determines dimensions from the dense generic fibre. Shared base-change tag: 02NK.

lem-trf-flat-dense-generic-fibre-pure-dimension vs lem-sbc-flat-fibre-dimension-near-zero-dimensional-stalk: the latter gives a local constant-dimensional neighbourhood at a point with a zero-dimensional local ring, and explicitly need not give dimension zero; it does not determine all fibres from the generic fibre. Shared definition tag: 02NJ.

lem-trf-flat-dense-generic-fibre-pure-dimension vs lem-sbc-flat-fibre-dimension-strata-core: the latter gives dense fibre opens of separately constant local dimensions, not uniform pure dimension on all components of all fibres. Shared definition tag: 02NJ.

lem-trf-flat-dense-generic-fibre-pure-dimension vs lem-sbc-cohen-macaulay-fibre-dimension-decomposition: the latter requires Cohen–Macaulayness and decomposes a supplied open into dimension pieces; the new theorem controls the whole family from its generic fibre without that extra hypothesis. Shared definition tag: 02NJ.

lem-trf-flat-dense-generic-fibre-pure-dimension vs lem-zl-affine-geometric-components-finite-extension: the latter descends connected components over finite fields and preserves smooth relative dimension; it does not concern a merely flat family over an integral base. Shared base-change tag: 02NK.

lem-trf-flat-dense-generic-fibre-pure-dimension vs lem-sc-curve-base-change-relative-dimension-one: the latter starts with a fixed smooth curve over a field; the new theorem applies to arbitrary flat families, including singular special fibres and arbitrary d. Shared base-change tag: 02NK.

lem-trf-flat-dense-generic-fibre-pure-dimension vs lem-trf-flat-family-generic-dimension-bound: an upper bound does not imply purity, nor equality of the dimensions of all components. The new theorem uses equidimensionality and density and gives equality and purity.

No new flattening node was created: the blueprint search for 081R finds `sk-lem-nagata-sketch-elimination`, whose statement contains the general flattening assertion used. Whole-DAG searches for 0GSJ/0GSK, their labels, generic pure dimension and flat equidimensionality, and whole-blueprint searches for 0GSJ, 0GSK, equidimensionality, pure dimension and flat dense generic fibres found no existing theorem with the new lemma's hypotheses and conclusion. I opened the statements of all the potentially overlapping nodes listed above. Searches in project Lean likewise found no exact closed declaration for the new theorem.

## Review by Q12

I read ILO Exposé X, Theorem 3.4 proof Step 2 on printed p.160 (PDF p.166), including the preceding definition of the proper transform and §3.2.2 on marked curves. The route is exactly its simultaneous flattening of the curve and horizontal boundary. I read Stacks `flat.tex` lemma-flat-after-blowing-up (081R) in full, `more-morphisms.tex` lemma-flat-associated-equidimensional (0GSJ) and remark-flat-equidimensional (0GSK) in full, and `morphisms.tex` definition-relative-dimension-d (02NJ) and lemma-base-change-relative-dimension-d (02NK). These are the sources of the item and the new node. In 0GSK the second list applies with F=O_X: finite type, full support and flatness hold, and density and dimension are explicit hypotheses. Thus the new statement is not a claim that arbitrary nonflat closures preserve dimension.

Step 1 uses projective-proper and proper permanence exactly for C and its closed H, and generic-flat-finite-presentation for their disjoint union. I checked that this statement assumes finite type and quasi-compactness over an integral base and supplies a nonempty flat locally finitely presented open. Noetherianity of S supplies quasi-compactness of that open. Empty H is permitted. I read the generic-flatness proposition (052A) in the local source as well.

Step 2 uses the general 081R assertion explicitly included in the elimination node's statement, not its specialized open-immersion assertion or a construction in its proof. The chosen W is finite type and quasi-separated, and the chosen U is quasi-compact and has the required flat/lfp restriction. The admissible-blowup definition supplies the ideal and the preserved open, and the strict-transform-closure node supplies the closed closure in the base change. Componentwise kernels justify splitting the transformed disjoint union. I verified the full cited statements and recorded the existing Lean mismatch above.

Step 3 uses relative Proj's stated affine models for the degree-zero localization chart calculation. I read Divisors lemma-blowing-up-affine (0804). Nonzero blowup charts embed into the fraction field of the integral affine base; all contain its generic point, so they give a single integral S1. Unit-ideal Proj verifies preservation of U. The blowup-proper statement applies because I is finite type; properness gives finite type. The cited Noetherian finite-type theorem and excellent finite-type/localization theorem apply to the excellent Noetherian base. I read their statements and the relevant 07QU source; excellence is not inferred from normality or from a completion assertion.

Step 4 uses only the surjective-graded-algebra clause actually stated in relative-proj-functoriality. I read Divisors lemma-blowing-up-projective (02NS) and its displayed Sym(I) to Rees surjection. The definition of projective bundle allows a finite-type quasi-coherent module I, so no global finite free presentation or ample line bundle on S is assumed. Separately, base change preserves the supplied finite-projective-space embedding of C. Closed immersions compose by proper-fp-permanence(e), so the transform remains H-projective. These two projectivity conventions are not silently identified.

Step 5 cites the local-ring definition of flatness and the injectivity definition of a flat module. At a point of either transform, A is a domain since S1 is integral. Applying flatness to A into Frac(A) really gives the written injection B into its generic localization. Every such B is nonzero. The localization therefore has a prime, giving a generic-fibre generalization; the injection also proves schematic density. A closed transform containing its generic fibre schematically densely is its schematic closure in the ambient scheme. This proves the precise generic-fibre closure identification needed by the item, not just equality of topological supports.

Step 6 uses only proper permanence beyond the explicit ring/closure calculations. For C1 its generic localized rings are domains because the original C is integral and its generic fibre is obtained by localization. The generic fibre is irreducible and dense, so C1 is irreducible and reduced. Kernel containment gives H1 as a closed subscheme of C1. Proper base change of v and closed-immersion composition give C1 to C proper; preservation of the nonempty dense open C_U gives birationality. No normality of S or geometrical irreducibility of C_eta is added.

Step 7 applies the new lemma twice with all its hypotheses checked: integral S1; flat finite presentation from Step 2; generic density from Step 5; d=1 for the integral curve and d=0 for the etale marking, the latter supplied by the actual zero-dimensional-fibre statement of the cited etale lemma. The projective-proper statement and closed-image definition of properness ensure that the curve's fibres cannot be empty. The new lemma explicitly includes geometric fibres, so no unsupported field-extension identification is used here.

Step 8 uses proper permanence for the closed marking, the affine zero-fibre-dimension quasi-finiteness criterion, the definition of locally quasi-finite on affine pairs, and proper-lqf-finite. I read Morphisms lemma-locally-quasi-finite-rel-dimension-0 (0397) and checked it requires only local finite type. The proper-lqf-finite node states exactly the final implication. Flatness and finite presentation are retained from Step 2; finiteness is proved here rather than smuggled into flattening.

I checked B through E: the new node is self-contained and statement-only, its notions have definition dependencies, its TeX has single logical backslashes, and its source uses checked Stacks tags and labels. Every node citation has its literal statement in citations.json. No proof-of-a-node, hidden normality, smallness issue, unproved tensor exactness, or route change is used. All eight steps are below 1100 characters; none exceeds the 2000-character threshold or hides the flattening or dimension theorem in prose. The new lemma is non-elementary; the local Rees charts, Sym-to-Rees surjection and flat localization calculation stay in the proof. Generic tools from other units are declared in split_report.tool_uses.

I tested the empty marking, a nonempty finite etale marking with several generic points, S the spectrum of a field (identity blowup), integral nonnormal bases, a smooth irreducible curve that is not geometrically irreducible, and singular/reducible special curve fibres. The dimension lemma allows mixed components only when the generic fibre itself has mixed dimensions, excluded in its hypothesis. It imposes neither smoothness of special fibres nor geometric irreducibility. Thus these cases do not falsify either the item or the new statement. Mathlib searches were run through msearch.py with two natural-language phrasings, Loogle and source grep for the item and the new theorem; I read the returned types. The hits concern definitions, smooth-relative-dimension permanence, universally open flat maps, finite type descent, or unrelated flattening, not these assertions. No search is fabricated and no unavailable response is called a negative match.
