# Q116 stage-1 delivery: lem-trf-simplicial-differential-base-change

## Files written

- dag/nodes/sec-trace-formula/lem-trf-simplicial-differential-base-change.json — statement, now split into five proof steps; no exact whole-item Mathlib match. The general termwise theorem is already the Mathlib leaf lem-weil-pbc-kahler-differentials-base-change.
- citations.json — nine verbatim statement excerpts, one for each step/node citation.
- searches.jsonl — actual msearch.py records from this attempt; all entries incorporated into the item in addition to its inherited searches.
- report.md — this report. No new DAG nodes and no new Mathlib leaves.

## Attachments

None. Searched lean/WeilConjectures for the item id, simplicial differential terminology and tensorKaehlerEquivBase. Existing uses in RingTheory/Kaehler/TraceBaseChange.lean concern traces; FiniteUnramifiedPrincipalQuotient.lean concerns a vanishing module. Neither is this augmented simplicial chain statement. No exact declaration was found, and no sorry declaration was treated as a finished proof.

## WANTED

None. The needed Stacks sources are present locally.

## Corrections and provenance

The item statement is unchanged. The sandbox contained only dispatcher markers at resumption, with no prior item, report, search records or delivery process. There was consequently no completed mutation to repeat. Retained all inherited Mathlib searches and blueprint provenance.

Read literature/stacks-project/algebra.tex, Tag 00RV, lemma-differentials-base-change, lines 34212–34233, including the explicit universal derivation, and cotangent.tex, Tag 08QZ, lemma-localize-at-bottom, lines 1544–1572. The hypothesis B = B tensor-derived_A A' in 08QZ is used for its conclusion about full cotangent complexes, not for the displayed ordinary differential identity proved here. In particular this split does not claim a change-of-base isomorphism of full cotangent complexes without that hypothesis.

Read the chapter and unit records and the current latest blueprint lem-trf-local-term-locality statement and proof. The existing blueprint.from describes the historical semistable-modification/lci support chain. The latest ancestor now proves local-term locality by contracting correspondences. I retained this historical metadata; this supporting algebra result neither changes the unit route nor purports to prove its contraction theorem. The immediate inherited place (old Step 3 of localization-cotangent-vanishing) describes exactly the comparison handled here.

The new proof uses the existing differential base-change leaf, rather than creating another 00RV node. Tensor cancellation, generator formulas and simplicial compatibility are explicitly proved from the universal properties. The derived isomorphism is induced by the chain isomorphism; no per-degree surrogate replaces the derived conclusion.

## Not duplicates

No new nodes. Searched DAG statements and sources for 00RV, 08QZ, differentials-base-change, tensorKaehlerEquivBase and simplicial differentials, and searched the whole imported blueprint with blueprint_refs.py for differentials and simplicial. Read the statements of lem-trf-outer-base-change-differential-comparison, lem-trf-base-changed-algebra-differential-generators and lem-weil-pbc-kahler-differentials-base-change. The last is the reused general termwise theorem; the former two are outer-ring comparison and finite algebra generators, not the augmented simplicial assertion. Also read lem-trf-polynomial-differential-base-change: it adds polynomial/K-flat/derived scalar-extension assertions and depends on this item, so citing it back would be circular. No same_as blueprint statement was found.

## Unfinished work

None in this stage-1 split. No Lean was written, no compiler or build was run, and no repository or launcher file was modified.

## Review by Q116

I checked this split against delivery-errors B–E with the cited statements and Stacks sources open. There are no new statement-only nodes to audit for hidden proofs or invented notions, and no clause has been moved into a renamed copy. The proof spells out the comparison instead of quoting 08QZ as a blanket base-change theorem.

Step 1 takes the isomorphism and its linearity for the specified tensor action from the statement of lem-weil-pbc-kahler-differentials-base-change. This node really states arbitrary commutative base change with no flatness assumption. I checked the swap of tensor factors against the bilinearity quotient in def-weil-pbc-module-tensor-product. The action (p tensor b')(omega tensor a') = p omega tensor b'a' agrees with the action in the cited theorem after the swap. This is the only non-elementary input.

Step 2 uses the tensor universal property from def-weil-pbc-module-tensor-product. I checked both Q-balancing and P-balancing explicitly: the common augmentation sends p tensor b' to epsilon(p)b', so both representatives produce omega tensor epsilon(p)b'a't. The inner R relation uses the composite R to R' to T, which is exactly the ring structure already assumed. The displayed maps c and j undo one another on pure tensors; this proves cancellation without an uncited tensor-associativity lemma. Tensoring E and its inverse preserves their composite identities directly, and does not require exactness of tensor.

Step 3 uses the quotient presentation in def-weil-pbc-kahler-differentials: Leibniz and vanishing on R' give d(p tensor a') = a'd(p tensor 1). Its statement includes that precise universal presentation, so generation by differential symbols follows from it. Tensor generation is explicitly in def-weil-pbc-module-tensor-product. This justifies both the claimed inverse formula and checking subsequent equalities on these generators; no finite generation was assumed.

Step 4 again uses those two universal constructions. The induced differential map comes from the derivation d composed with f, not from a definition node silently being treated as a naturality theorem. I verified the derivation and augmentation hypotheses and wrote the equality on d p tensor t: both routes are d(f(p) tensor 1) tensor t. This establishes every face, every degeneracy, and every component of an arbitrary augmentation-preserving simplicial map. The inverse naturality is obtained by composing this actual equality with inverses.

Step 5 uses only the alternating convention stated in lem-trf-cotangent-resolution-coherence and the localization functor stated in def-weil-abstract-derived-category. It does not use the former's substantial polynomial-resolution theorem. The signed sum identity follows term by term from Step 4; the degree-zero outgoing differential is zero rather than an augmentation. I also wrote the cancellation in the square of the differential using the face identity. The inverse identities hold as chain maps, so functoriality of localization gives inverse maps in D(T). No cohomology-only comparison or uncited derived tensor theorem is used.

I tested the formulas on R'=R (identity comparison), constant simplicial algebras (the same module map in each degree, with the alternating convention respected), P_n=R (both differential modules zero), T=0 (all augmented differential terms zero), and non-flat R'=Z/2 over R=Z with T=Z/2 and constant P=Z[x] mapping x to zero. In the last case both degreewise modules are T dx and the displayed comparison is the identity on dx. The formulas allow nilpotents and arbitrary, nonpolynomial terms. All needed compatibilities concern the actual augmentation, not an assumed resolution. The hypotheses are sufficient and no statement dispute was found.

Read Mathlib/RingTheory/Kaehler/TensorProduct.lean:169–217 and 250–263, and RingTheory/Extension/Cotangent/Basic.lean:53–65 against all returned types. tensorKaehlerEquivBase and tensorKaehlerEquiv give the existing termwise leaf; presentation cotangentComplexBaseChange is a conormal-to-differentials linear map, not this full simplicial complex. The second semantic phrasing returned map_D and other generator/termwise statements, still no whole-item match. All recorded services answered successfully. No searches were invented or unavailable services treated as absence.

All five proof steps are below 2000 characters (617, 985, 526, 765 and 856). Their elementary parts are written tensor/generator/chain calculations, not hidden standard lemmas. citations.json was checked by exact substring comparison against each live statement. The item has no new dependencies that point back to it, and no off-unit non-Mathlib proof theorem is imported: the coherence citation supplies only the existing convention in the statement.

The first dry run rejected the short base-change citation excerpt (minimum 40 characters). Expanded it to the entire cited statement, also expanding the tensor and differential excerpts so that every property used is visible. No mathematical change was needed.
