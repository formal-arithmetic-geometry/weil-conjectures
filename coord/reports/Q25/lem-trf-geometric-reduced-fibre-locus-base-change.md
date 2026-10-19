# Q25: lem-trf-geometric-reduced-fibre-locus-base-change

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-geometric-reduced-fibre-locus-base-change.json`: statement, split; no exact Mathlib match. Seven proof steps, with existing dependencies only.
- `citations.json`: 19 verbatim statement quotations, one for each cited node in each step.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. The sandbox initially contained only dispatcher briefs, with no previous node, report, or searches to recover. The existing item statement, source, and Q18 search records are retained; this run adds its actual logged Q25 searches.

## Attachments

None. Searched the slopmaster2 `WeilConjectures/` source for the exact blueprint tag and the geometric-reducedness/fibre notions. No declaration states this equality for arbitrary scheme morphisms. `AlgebraicGeometry.GeometricallyReduced.of_perfectField` in `WeilConjectures/Mathlib/AlgebraicGeometry/Geometrically/Reduced.lean:111` supplies a related scheme theorem, and `AlgebraicGeometry.Scheme.isReduced_baseChange` in the Riemann--Roch source supplies a forward reduced-base-change result; neither gives the item's reflection direction or full pointwise locus statement. No attachment is asserted.

## WANTED

None: all sources used in the proof are in the repository's Stacks checkout.

## Audit of the imported item and route

The statement is correct without flatness, finite presentation, or surjectivity, and has not been changed. Its use of reduced fibres over algebraic closures agrees with Tag 0576's formulation using geometrically reduced scheme-theoretic fibres: Tags 035X and 020I justify this distinction. I read Tag 0576, `more-morphisms.tex`, label `lemma-base-change-fibres-geometrically-reduced`; Tag 0384, `varieties.tex`, label `lemma-geometrically-reduced-upstairs`; and the surrounding Tags 035W, 035X and 020I. The source's proof first identifies the fibre at the new point with scalar extension of the original fibre, and then uses invariance under a field extension.

Here that latter argument is made directly for the two chosen geometric fibres: embed both algebraic closures into a common field and compare their affine chart rings there. This avoids silently identifying independently chosen algebraic closures. I mark `proof_origin.by` as `agent`, since this explicit affine common-overfield proof is a rearrangement of the Stacks inputs rather than a transcription of the point-local proof of 0384. It realizes exactly the good-locus base-change input in the item's inherited Temkin/noetherian-approximation ancestry. I read the chapter record, `sk-i-curve-zero` unit, and the inherited blueprint ancestor information. No chapter, unit, or ancestry metadata is changed.

DAG and blueprint searches for `0576`, `reduced geometric`, and `geometrically reduced`, together with full-statement inspection of the relevant existing nodes, found no imported blueprint node giving this general arbitrary-base equality. `lem-trf-geometrically-reduced-fibre-locus` has a finite-presentation affine statement and is not used to prove the stronger item. The existing `lem-trf-geometric-reducedness-local-base-change` is a point-local ring theorem, and `lem-trf-geometrically-reduced-base-change` is a reduced tensor-product theorem with a geometrically reduced algebra hypothesis. Neither is duplicated. Instead the proof reuses existing common-field, perfect-tensor, affine-product, and faithful-flatness tools.

The actual Q25 search commands are in `searches.jsonl` and are copied without invented queries into `mathlib_searches`: LeanFinder twice with different phrasings, Loogle, LeanSearch, and source grep. All services returned hits. I read Mathlib `AlgebraicGeometry/Geometrically/Reduced.lean`, `Geometrically/Basic.lean`, and `RingTheory/Nilpotent/GeometricallyReduced.lean`. They provide global base-change stability and ring-level algebraic-closure tests; those do not themselves state this arbitrary pointwise scheme-locus equality or produce it in one line. No Mathlib leaf is asserted.

## Not duplicates

No new nodes were created; there are no new/existing node pairs needing separation.

## Review by Q25

I read the statement of every dependency actually used, rather than relying on its title or proof. The quotations in `citations.json` are the full verbatim statements, so their hypotheses remain visible. I also opened the Stacks source for the algebra and scheme lemmas: Fields 0H7K (`lemma-common-extension-field`); Algebra 00I4 (`lemma-perfect-reduced`), 00D2 (`lemma-tensor-with-bimodule`), 00HI (`lemma-flat-base-change`), 00HP (`lemma-ff`), and 05CK (`lemma-faithfully-flat-universally-injective`); Schemes 01JR (`lemma-open-fibre-product`), 01I4 (`lemma-fibre-product-affine-schemes`), and 01J2 (`lemma-affine-reduced`). There are no new statement-only nodes whose sources require a separate review.

Step 1 uses `def-weil-residue-field` for the induced map kappa(t) -> kappa(t'), `def-pc-scheme-fibre` and `def-weil-geometric-fibre` for the exact fibres, and `def-pc-fibre-product` for their universal property. I wrote out the maps represented by each iterated product, including the forced map to T', to check that the base-change fibre is over the correct residue field. This is an elementary application of the stated universal property.

Step 2 uses `lem-weil-common-extension-fields`, whose statement explicitly provides two embeddings agreeing on k. Its hypotheses hold because F is an extension of k through L. The algebraic-closure definition supplies roots of Z^p-a, making both E and F perfect without any assumption that k or L is perfect. The reducedness of the common field is proved by inverses. The common field itself need not be algebraically closed or algebraic over either field.

Step 3 uses precisely the open-chart identification given by `lem-weil-pbc-open-fibre-product` and the tensor ring given by `lem-weil-pbc-fibre-product-affine-spectra`. The base is Spec k and the second factor is the whole Spec H, so all open-containment hypotheses hold. `lem-weil-pbc-affine-scheme-reduced-iff` supplies the ring/scheme equivalence. Locality and invariance of reducedness follow directly from the local-ring definition in `def-pc-reduced-scheme`; all inverse-image charts cover the actual geometric fibre. No quasi-compactness or finite affine cover is used.

Step 4 applies `lem-weil-pbc-perfect-reduced-tensor` over E, with reduced B_i from the assumed original geometric fibre and reduced M from step 2. That node imposes no finite type hypothesis. `lem-weil-pbc-tensor-cancel-base-change` gives the common ring C_i, after the elementary tensor-factor swap. I wrote its formula and inverse, so the isomorphism is one of algebras and preserves nilpotents.

Step 5 uses `lem-weil-pbc-field-extension-base-change-faithfully-flat` with the extension M/F, for the arbitrary F-algebra D_i. It uses `lem-weil-pbc-faithfully-flat-universally-injective` with N=R=D_i, and spells out the identification of R tensor_R S with S; thus this citation really supplies the needed injection, not merely a definition of flatness. Cancellation is cited again to identify the target with the already reduced C_i. Reflection of reducedness is the written two-line nilpotent argument, not an additional unrecorded descent theorem.

Step 6 checks the reverse direction independently: reduced D_i, perfect F, and reduced M permit 00I4, and the extension M/E gives injection from B_i into the same reduced C_i. The same three cited algebra statements give exactly these facts. Nothing requires the map g to hit every point of T: only its particular point t' is used.

Step 7 is subset extensionality applied to the pointwise equivalence already proved. The empty-source/empty-fibre case has an empty affine cover and vacuous reducedness, so it is included. For small cases I also checked a constant dual-number fibre, where epsilon survives the injective field-extension maps and both sides exclude the point; an imperfect-field reduced but geometrically nonreduced example Spec(k[u]/(u^p-a)), with a not a p-th power, where both algebraic closures expose the same nilpotent; and disjoint-component affine covers, where the criterion is componentwise. The identity base change is recovered immediately. These tests confirm why ordinary reducedness of X_t cannot replace reducedness of its geometric fibre.

Against delivery-errors B--E: no new notions or nodes, no clause moved into a child, no undocumented theorem in a step, no proof-of-a-node used instead of its statement, no additional finiteness hypothesis, and no SGA source. All non-elementary steps are marked false for `elementary`, and all are well below 2000 characters. The only inline comparisons are the explicitly written universal-property and tensor-cancellation instances and the elementary nilpotent calculation. All eight off-unit theorem citations are declared in `split_report.tool_uses` as generic tools; they do not replace the unit route. I corrected no mathematical statement; the repair was to supply a complete proof and its exact dependencies where the imported item had none.

## Unfinished work

None in this one-level split. Its existing unsplit algebra dependencies remain the separate items already represented by the DAG. No Lean was written or compiled, and no live project, launcher, chapter, or unit file was modified.
