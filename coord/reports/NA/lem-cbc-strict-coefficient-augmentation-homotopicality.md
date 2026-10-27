# Stage-1 report

## Files written

- `dag/nodes/sec-smooth-purity/lem-cbc-strict-coefficient-augmentation-homotopicality.json`: statement, split into eight proof steps; not a Mathlib leaf. Its statement and statement dependencies are unchanged. The existing metadata and searches are retained, and five searches run for this delivery are appended.
- `citations.json`: one entry for every step/node citation, quoting the cited statement verbatim.
- `report.md` and `searches.jsonl`: report and actual search log. `write_split.py` is sandbox-only preparation, not a project-file delivery.

No new nodes; no new Mathlib leaves. No unit or chapter file changed: this item is an auxiliary lemma, not the key statement of its unit.

## Attachments

None. Searches of `lean/WeilConjectures/` for the blueprint tag, strict towers, coefficient augmentations and K-flat towers did not find a declaration giving every clause. The existing `CochainComplex.quasiIso_map_tensorRight_of_kFlat` in `WeilConjectures/Algebra/Category/ModuleCat/Sheaf/Reduction.lean` supplies an individual tensor homological-algebra fact, not the augmented strict-diagram statement. The normalized-tower and derived-base-change files concern more specialized coefficient and tower data; their existence does not attach this item.

## Literature wanted

None. The requested inherited `coord/dag-sync.md` is absent from this clone; the explicit direct-delivery brief supplies the operative read-only/sandbox protocol.

## Corrections and scope

The imported node was statement-only and its statement is correct. The argument is now in the item itself. In particular, it does not replace its clauses by newly named lemmas. The only non-elementary homological input for coefficient reduction is the existing general ringed-site change-of-rings lemma, not the one-point-site lemma `lem-pc-kflat-tensor-quasi-iso` or the constant-coefficient etale lemma `lem-kun-derived-tensor-well-defined`.

The ancestor blueprint proof's final countable-product assertion for open extension is outside this item and is not used. This split proves only the strict tensor tower, augmentation, homotopy/localization and additive-cone assertions assigned to it. It makes no interchange of products, completion or extension by zero. The CBC coefficient typing and route remain untouched.

## Unfinished work

None in this one-level split. The existing dependency `lem-pur-change-of-rings-kflat-quasi-iso` remains its own DAG item with its existing state. The proof does not rely on a sorry-containing Lean declaration as if it were finished.

## Not duplicates

There are no new-node/existing-node pairs. Whole-DAG searches by Tags 06YT and 02MZ and by additive/cone, homology/evaluation and localization/natural-transformation terminology identified the reused nodes. The whole-blueprint searches for `K-flat` and `strict coefficient augmentation` found no blueprint statement with all clauses of this item. `blueprint_refs.py ancestor` confirms `lem-cbc-completed-extension-zero-comparison`; its recorded ancestry and precise place are retained and `same_as` is empty.

## Review by NA

I read the item, its chapter and unit records, the current `main-20261015` CBC unit statement and `lem-cbc-completed-extension-zero-comparison.proof.md`. I read Stacks `sites-modules.tex`, Tag 03EK (`section-tensor-product`), including the sheafification definition of tensor; Tag 03DA (`lemma-abelian`), including the kernel/cokernel description; `sites-cohomology.tex`, Tag 06YT (`lemma-derived-tor-quasi-isomorphism-other-side`) and its K-flat-resolution argument; `homology.tex`, Tag 02MZ (`lemma-inverse-systems-abelian`); and `derived.tex`, the homotopy-category and cone definitions. I also read the Mathlib source for `SheafOfModules.restrictScalars`, the functor-category abelian instance, and `Localization.lift`/`liftNatTrans`. There are no new-node sources to review.

For Steps 1 and 2 I opened the statements of `def-weil-sheaf-of-modules-category`, `def-pc-sheaf-restrict-scalars`, `def-pur-sheaf-tensor-product` and `def-weil-inverse-system`. They give exactly the category, restricted action, sheafified tensor and strict transition/morphism data used. The proof writes the differential, transition, functoriality, coefficient-linearity and unit equations. The equations are proved on presheaf tensors and then sheafified, so no generation claim about global pure-tensor sections is required. The relation `q_n p_{n+1}=p_n` ensures O-linearity, and unitality ensures strict augmentation compatibility.

For Step 3 the same tensor and tower definitions, together with the homotopy-category convention in `def-weil-abstract-derived-category`, support the displayed degree-minus-one homotopy. The crucial transition commutation is checked explicitly. Nothing assumes that a reduced complex remains K-flat over O.

For Step 4 I opened the full statement of `lem-pur-change-of-rings-kflat-quasi-iso`. It concerns arbitrary ring sheaves on a site, not just constants; requires an additive functor agreeing with change of rings; and concludes a quasi-isomorphism between the resulting coefficient-module complexes. Here the functor is exactly change of rings along p_n, with additivity checked on tensor maps. Both input complexes are K-flat by the hypotheses, as defined by `def-pc-kflat-complex`. The conclusion initially lives over B_n. I therefore wrote out, using the kernel/cokernel description in `def-weil-sheaf-of-modules-category` and the unchanged abelian sheaf in `def-pc-sheaf-restrict-scalars`, why restriction to O preserves cohomology and hence this quasi-isomorphism. This is a few-line consequence of the cited statements, not an uncited flatness theorem. This off-unit citation is declared in `split_report.tool_uses`: it is a generic tensor tool needed at each CBC coefficient level.

For Step 5 I opened `lem-weil-tower-category-levelwise-abelian`. Its statement explicitly supplies levelwise kernels and cokernels and exact evaluation. The proof then computes images as kernels of cokernels and cohomology as a quotient. It checks that levelwise inverses commute with transitions. Thus quasi-isomorphism detection is deduced from what the node actually states; it is not attributed to an unsupported assertion in its proof. The module category is abelian by the small-site clause of its cited definition.

For Step 6 I opened `lem-weil-pbc-localization-universal-property`. Clause (1) gives the functors, while clause (2), not merely an objectwise universal property, gives the descended augmentation. Step 5 verifies inversion of the source quasi-isomorphisms. `def-weil-abstract-derived-category` supplies the tower-derived localization Q_t. The target is the derived category of strict towers, rather than a diagram category of individually localized objects.

For Steps 7 and 8 I read `def-sp-abelian` and the tower, shift and cone conventions in the cited definitions. Additivity preserves the homotopy equation and signed differentials. I wrote the biproduct projection/inclusion identities and the cone differential matrix to justify the cone comparison, including the inclusion and signed projection. It is natural for strict transitions because it is defined by projections. These are direct additive calculations; they require neither exactness of E nor preservation of arbitrary products. No fact about a derived E is claimed.

I checked the delivery-errors B--E checklist against these files. B: the statement introduces all objects and retains definition references; TeX is singly escaped after JSON decoding; searches are actual logged msearch calls; there are no new leaves or unsplit-node proof sketches. C: every step's cited node was opened, the exact relevant hypotheses were checked above, and citations.json quotes actual statement text; no proof-only construction is borrowed. The only generic off-unit theorem is declared. D: no new node moves the item or a clause elsewhere, and the proof is the displayed construction and calculations. E: neither coefficient flatness nor post-reduction K-flatness is smuggled in; the B_n/O distinction and strict/homotopy/derived distinctions are explicit.

I tested the small cases O=0, B_n=0, identity coefficient maps, identity/zero chain maps, non-surjective coefficient transitions, and a non-flat map Z to Z/2 on the one-point site. The augmentation need not be invertible, which the statement does not assert. For the non-flat map only quasi-isomorphisms between K-flat inputs are tensor-preserved. Taking E to be an additive nonexact functor (for example Hom(Z/2,-) on abelian groups) still preserves the homotopy and cone formulas, confirming that those clauses do not need exactness. Unbounded complexes cause no totalization convergence issue here: each coefficient B_n is in degree zero, so the reduction differential is simply d tensor 1. The flat-terms condition on the inputs is retained although the cited tensor-preservation theorem only needs K-flatness. Every proof step is below 2,000 characters; none hides a long standard comparison.

The retained delivery passed the initial complete server dry run at `9572129b738` during this repair. A fresh complete dry run follows the repair edits before pushing.

## Repair of the live-promotion return

The return has one point: the previous side-project completion was not promoted into the live DAG read by the queue. I compared the retained delivered item with the current shared live item. The live item is still `unsplit`, with an empty proof and no repair note; its statement, statement dependencies, source, creation record and blueprint ancestry agree exactly with the retained item. The retained differences are the eight-step proof, its proof dependencies and origin, the split report, status, and appended actual search records. The delivery tool constructs the repair on the current `origin/sheaf-dag`, rather than sending the old side-project base.

I re-read all eleven current dependency statements, including the statement-only flatness dependency. In particular the current change-of-rings node requires an additive functor agreeing with extension of scalars and concludes a quasi-isomorphism over the target ring; Step 4 checks that exact hypothesis and separately explains scalar restriction. The tower-category node explicitly gives levelwise kernels and cokernels, supporting Step 5. The current localization node supplies natural isomorphisms for the factorizations and a natural-transformation lifting clause. I adjusted Step 6 to name the localization of the chain-map category, the two factorization isomorphisms, and the conjugation formula for the descended augmentation, so the split uses precisely that current statement without treating an isomorphism of functors as equality. The other construction, homotopy and cone arguments are retained.

All 24 step/node pairs in `citations.json` still have verbatim quotes in the current statements, with no missing or extra citations. I retained the existing searches and read their recorded hits; the statement and search questions have not changed, so no search is repeated. There are still no new nodes or Mathlib leaves. I re-read the current blueprint ancestor proof and the Stacks tensor, module-category, K-flat quasi-isomorphism, inverse-system and cone passages listed above. The source's countable-product assertion remains outside this item's proof. All eight steps remain shorter than 2,000 characters, and the small-case checks in my review continue to apply. This repair changes the proof's localization assembly and the report, and is submitted against the live DAG for promotion.

## Current-head repair verification (2026-10-22)

The required initial dry run for this retry exited successfully: `OK (not pushed)` at `b866c1f8ce7`. I compared the retained item field by field against the current shared live node: only the proof, proof dependencies, proof origin, split report, status and appended Mathlib searches differ. In particular the statement, statement dependencies, source, creation record, chapter, unit and blueprint fields agree. No released repair note exists for this item.

I re-read the current statements of all ten proof dependencies and the additional flatness definition in the statement dependencies. The current localization statement explicitly allows factorization up to natural isomorphism and lifts natural transformations by conjugating with those isomorphisms. Step 6 already uses those clauses. I have now also written its augmentation equation for an inverted quasi-isomorphism: multiply the naturality equation on the two sides by the functor images of its inverse. This checks the descent compatibility concretely against the current universal property, without assuming equality of the factorization functors. It is an elementary consequence of that cited statement, so needs no new node or new search.

All 24 step/node citation pairs and all verbatim quotes were checked anew against current statements; there are no mismatches. The Stacks passages for tensor sheafification, module kernels/cokernels, tensor preservation between K-flat inputs, inverse systems and cone conventions were reopened. The retained non-flat-coefficient and nonexact-additive-functor edge cases continue to satisfy the unchanged statement. All steps remain below 2,000 characters. This retry therefore retains the approved proof and recorded searches while making an actual localization-assembly repair and rebuilding the delivery against the current live DAG. The final dry run is run after these edits, followed by the push.
