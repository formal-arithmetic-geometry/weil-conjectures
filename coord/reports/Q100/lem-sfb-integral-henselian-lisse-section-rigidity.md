# Stage-1 delivery: lem-sfb-integral-henselian-lisse-section-rigidity

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-integral-henselian-lisse-section-rigidity.json: statement, split into five proof steps; no Mathlib match for the whole assertion.
- citations.json: one verbatim statement quotation for each citation in each proof step.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0. All the mathematical inputs already have nodes.

## Attachments

None. Searched lean/WeilConjectures for the exact item id and for wStrict/w_strict/wContract, lisse rigidity, and henselian lisse terms. The exact blueprint tag is absent. The hits in ConstructibleSheaf/InternalHom.lean and Rigidity.lean concern finite locally constant modules in the etale setting, not the arbitrary condensed coefficient, pro-etale, derived-section statement here. The ring-theory contractibility criterion is not an attachment for the lisse assertion. Nothing was compiled and no Lean was written.

## WANTED

None for this split. The Stacks sources and both HRS and Bhatt--Scholze PDFs were present and read. This does not assert that HRS literally states the w-strict extension: the split explicitly cites the existing agent-formulated component-cohomology node for that extension.

## Audit and changes

The imported item was statement-only. Its statement, statement dependencies, source, creation metadata and blueprint ancestry are preserved. Its proof now separates integral base change and henselian permanence, finite finitely presented approximation, weak strict locality, the actual map of component spaces, and the unit-normalized derived restriction. No target statement was changed and no unit or chapter route was replaced.

The nearest blueprint ancestor tool reports null for this inherited created-node chain. The existing concrete from.place and via chain are retained, and split_report.blueprint identifies paragraph (3) of the current main-20261015 direct-image proof. Searched the imported blueprint with blueprint_refs.py for henselian, integral, and lisse component, and the whole DAG for the algebraic tags and the topology/cohomology terminology. These searches found the existing nodes used below. No blueprint node states the full combined assertion, and there is no reason to create a duplicate.

The item's existing Mathlib search records were retained. The new searches were run through msearch.py with this item id and copied from searches.jsonl: LeanFinder with two different phrasings, Loogle, grep, and LeanSearch. The first LeanFinder hits concern free sheaf transport, affine limits or tilde sections; the second concerns formal etaleness and standard etale pairs. LeanSearch finds integral quotients, HenselianRing and discrete condensed module characterization. None has the required internal pro-etale lisse derived statement. The four services were available for these queries. The search process whose session disappeared after an interruption had completed and logged its result; its logged result was read rather than rerunning it.

## Not duplicates

No new nodes are proposed. In particular the integral henselian permanence, integral finite-presentation approximation, w-strict ind-finite limit, henselian w-strict invariance, henselian component invariance and w-strict lisse cohomology are all reused instead of recreated.

## Review by Q100

I read Stacks algebra.tex lemma-base-change-integral (Tag 02JK), more-algebra.tex lemma-integral-over-henselian-pair (09XK), properties.tex lemma-integral-algebra-directed-colimit-finite (0817), and schemes.tex lemma-colimit-quasi-coherent (01ID). I also read HRS Lemma 4.1, Proposition 4.3 with equation (4.2), Corollary 4.4 and its proof, and its hyperdescent Corollary 4.7 context, together with Bhatt--Scholze's cofiltered-limit and henselian weak strict locality statements (Lemma 2.1.9, Example 2.2.2, Lemma 2.2.13). The current direct-image proof paragraph (3) and the chapter/unit records fix the route this local calculation serves. There is no SGA input.

Step 1 cites lem-weil-pbc-integral-base-change, whose statement is exactly integrality after tensor base change, and lem-weil-pbc-integral-over-henselian-pair, whose statement accepts an arbitrary integral ring map over a henselian pair. I checked that the tensor flip is a C-algebra isomorphism and that the extended ideal is precisely ID=(IC)D. Injectivity, module-finiteness and finite presentation are not hypotheses of either statement.

Step 2 uses the affine qcqs statement to justify the base-scheme hypothesis of 0817. The tilde-sections statement gives the quasi-coherent underlying module with its localization identifications; ordinary multiplication on those fractions supplies the algebra structure, with global sections D. The affine algebra restriction statement explicitly gives the tensor formula on every affine open, so integral base change verifies the definition of an integral quasi-coherent algebra, not merely integrality on the full affine scheme. The approximation statement gives finite and finitely presented algebras, allowing noninjective maps. Finally lem-weil-pbc-quasi-coherent-algebra-colimit explicitly says that sections on every affine open commute with this directed colimit. Thus taking sections really produces the ring diagram required by the next step. Finiteness and algebra finite presentation of its sections are part of the approximation node's own affine definitions; module finite presentation is not substituted for algebra finite presentation. The indexing data can be chosen in the compatible universes already required in the item. No hidden new comparison lemma is being passed off as a definition.

Step 3 cites lem-sfb-indfinite-contractible-base-wstrict, whose statement requires a nonempty small directed poset, module-finite and algebra-finitely-presented stages, and a w-contractible base. All are supplied by step 2 and the hypothesis on C. It explicitly permits zero algebras and noninjective transitions, and gives only weak strict locality of the colimit. Lemma lem-zl-henselian-wstrict-local-invariance then applies to the henselian pair from step 1 and gives weak strict locality of its quotient. I did not infer w-contractibility of D or apply the contractible cohomology theorem directly to D.

Step 4 uses only the first clause of lem-zl-condensed-henselian-lisse-rigidity. I opened its complete statement: it says that for any henselian pair the actual quotient closed immersion induces a homeomorphism on pi_0; the later condition on contractibility governs the later equivalence, not this first clause. HRS Corollary 4.4(1) confirms this scope in the source proof via unique lifting of idempotents. This supplies the quotient topology and the actual direction of pi_0(a), rather than an abstract bijection of components.

Step 5 uses def-sfb-lisse-coefficient-module for the finite free trivializing cover and lem-weil-pbc-profinite-point-pullback for the canonical coefficient and pullback-composition identifications. Pulling back the cover and the finite basis gives the lisse module M, without assuming fixed rank or positive rank. The statement of lem-sfb-wstrict-lisse-component-cohomology applies to arbitrary morphisms of w-strict affine schemes with a component homeomorphism, for every condensed ring. I checked its conclusion is an isomorphism in the ordinary derived category of abelian groups and explicitly specifies the actual adjunction-unit map and canonical comparisons. It therefore supplies precisely the map asserted here; no abstract cohomology identification or scalar-extension/direct-image commutation is substituted. Its proof carries the w-strict descent extension beyond the contractible hypothesis of HRS Proposition 4.3; the present proof does not relabel that extension as a verbatim HRS theorem.

Every uses entry has its own verbatim statement quotation in citations.json. All substantive steps are marked non-elementary because they apply cited results. There are no new statement-only nodes to test and no step longer than 2000 characters. Off-unit statements are declared as generic tool uses in split_report rather than as a change of route.

For edge cases, I checked I=0 (restriction is the identity), B=0 or C=0 (both spectra empty and section complexes zero), and ID=D (the henselian radical condition forces D=0). An infinite integral algebra is handled by the directed approximation, without inserting finiteness of D/C. A noninjective system is explicitly allowed by the ind-finite input. Rank zero and varying local ranks survive pulling back the trivializing cover. The coefficient ring can be zero, nondiscrete or incomplete; the cohomology input places none of those restrictions on it. The final normalization is the unit map, so no choice of approximation determines the restriction morphism.

I checked delivery-errors B--E: there are no duplicate, elementary or clause-restatement nodes, no missing hypothesis has been introduced, no cited proof is used in place of its statement, and the original statement is intact. The substantive correction during drafting was to make the passage from sheaf-algebra approximation to a ring colimit explicit and to distinguish henselian component invariance from the stronger contractible lisse equivalence.

## Unfinished work

None in this one-level split. The cited existing nodes retain their own proof obligations and independent review status. Server dry-run and delivery results are supplied by the delivery tool.
