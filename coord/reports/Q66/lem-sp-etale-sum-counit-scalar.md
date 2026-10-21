# Worker report: lem-sp-etale-sum-counit-scalar

Group Q66, stage 1, 2026-10-21. Direct delivery; the signature below is this worker's self-review, not an independent second reader.

## Files written

- `dag/nodes/sec-smooth-purity/lem-sp-etale-sum-counit-scalar.json`: existing statement, now split into six steps. The statement and its statement dependencies are unchanged. No Mathlib match for the geometric derived assertion.
- `citations.json`: 27 entries, one for every step/node citation, with verbatim substrings of the cited statements.
- `report.md`: this report. `searches.jsonl` is the required search tool's actual log; `write_split.py` regenerates this sandbox's JSON and citation manifest only.

New nodes: 0. New Mathlib leaves: 0. There was no earlier item copy or report in this sandbox.

## Attachments

None. Searched the project `lean/WeilConjectures/` for the exact blueprint tag and for sum-extension, etale counit and scalar/counit notions. The results include unrelated inverse-image, lower-shriek coefficient and module counits, but no declaration of this item with all its clauses. No Lean was written or compiled.

## WANTED

None. All source material needed for this split was available in the read clone.

## Findings and changes

The imported node had a statement and searches, but no proof. Its source is the current blueprint's Charts paragraph in `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-lem-sp-reduction/sk-lem-sp-reduction-exceptional.proof.md`: the integral summation claim. I read the current chapter and the coefficient-comparison unit, including the unit's second step. This split fills the summation part of that step; it does not replace the chart, Kummer, diagonal or projective-line route.

The proof now makes a common K-flat model explicit, computes the two B-linear chain maps on the same tensor generators, localizes the equality, identifies its adjunction mate with the correct inverse, and gives the actual compact-support counit equation. The compact-support clause uses the coefficient square already stated in lem-sp-et-proet-coefficient-compatibility; it does not assume that an unspecified isomorphism preserves a counit. No statement dispute or mathematical change was needed. The unused twist convention in the inherited statement is retained.

The first server `review_split` check passed. Its route observations concern existing tools from other units and the still-unrealized enclosing unit; I have recorded the generic tool uses in `split_report.tool_uses`. I am not changing the unit realization: this auxiliary item is not the unit's key node.

## Searches and reuse

Read the results of every Q66 command in `searches.jsonl`, and retained the inherited Q36 search records. Ran LeanFinder with both “Derived scalar extension commutes with the summation counit of the etale sum-extension adjunction” and “The left adjoint to restriction to an etale slice has an evaluation counit compatible with change of coefficient rings”; Loogle with `"counit", "tensor"`; grep with `sum.*counit|counit.*sum|lowerShriek|extensionByZero` in `CategoryTheory/Sites`; and LeanSearch with “Etale extension by direct sums scalar extension tensor counit compatibility”. Every service answered. No unavailable response was recorded as absence.

The first semantic results concern etale algebras and differentials, and the second concerns Gamma-Spec, scalar-restriction counits and open module restriction. Loogle's nearest result is `CategoryTheory.Adjunction.map_μ_comp_counit_app_tensor`; I read `Mathlib/CategoryTheory/Monoidal/Functor.lean:1036`. It assumes a monoidal adjunction and does not construct the etale sum-extension/coefficient square. LeanSearch's direct-sum tensor hits are useful ordinary algebra, but do not state the sheaf-derived equality; I read `TensorProduct.directSumLeft` at `Mathlib/LinearAlgebra/DirectSum/TensorProduct.lean:67` and its generator equation at line 97. None is an exact match or a one-line specialization of this item.

Before adding anything, searched the whole DAG and blueprint for sum counits, summation, coefficient counits, scalar summation and sum-extension tensor, and searched the source library. Existing lem-pur-etale-sum-flat-kflat already supplies the model-preservation fact that might otherwise have become a node. The item ancestry command identifies det-sp-reduction-exceptional; its Charts paragraph is recorded in `blueprint.from.place`. The summation search finds the larger parent and a trace-basic node, neither stating this coefficient-counit lemma. Hence `same_as` remains empty. No new node was necessary, and there are no new/existing same-tag pairs to distinguish.

## Review by Q66

I checked the six steps against the actual dependency statements and the source texts, rather than their titles or proof implementations. The principal source is the blueprint Charts claim above, with an agent-written expansion of its integral calculation. I read Stacks `etale-cohomology.tex`, Tag 03S3 (`definition-extension-zero`), its displayed direct-sum presheaf and the following adjunction exercise, as well as 03S5 (`proposition-describe-jshriek`). I also read `more-etale.tex`, Tag 0GKF (`lemma-f-shriek-projection`), whose pure-tensor construction explains the summand-preserving map, and `sites-cohomology.tex`, Tags 06YS (`lemma-K-flat-resolution`), 06YQ (`lemma-bounded-flat-K-flat`), 0G7E (`lemma-pullback-K-flat`), and 07A4 (`lemma-pullback-tensor-product`). For the domain check I read `etale-cohomology.tex`, Tags 095G (`lemma-pullback-constructible`) and 03TT (`lemma-when-ctf`), and the flat-constructible-model statement and docstring in the live Lean source. I used no prohibited SGA route. There are no new nodes requiring separate source audits.

1. **Models and hypotheses.** Opened the statements of lem-weil-pbc-finite-type-over-noetherian, lem-sf-etale-flat-constructible, lem-weil-pbc-independent-bounded-flat-kflat, prop-constructible-pullback, lem-pc-kflat-resolution, prop-weil-pbc-inverse-image-modules-exact, lem-weil-pbc-ringed-topoi-derived-tensor-pullback, lem-pur-etale-sum-flat-kflat, lem-pur-derived-change-of-rings and lem-amb-etale-adjoint-locality. They respectively provide Noetherianity, a bounded flat constructible model, its K-flatness, constructibility under pullback, a common flat-term K-flat resolution, exact inverse image, pullback preservation of K-flat flat-term models, sum-extension preservation of K-flatness, the scalar-extension computation, and the exact degreewise derived sum adjunction. Their hypotheses hold: finite coefficient rings, finite-type schemes over a field, separated etale finite-type e, and the ordinary etale constant-ring categories. I added the domain check during self-review: exact pullback preserves the bounded cohomology interval and constructibility, while the bounded flat pullback model gives finite Tor amplitude against every module sheaf. Thus the input e* K to the coefficient theorem is justified, rather than merely presumed.

2. **The sheaf counit.** Read lem-weil-pbc-etale-inverse-image-restriction, the module-action clauses of prop-weil-pbc-inverse-image-modules-exact, def-weil-pbc-etale-sum-extension and the universal property in def-weil-presheaf-modules-sheafification. These say exactly which sections form a summand and how a map from that presheaf induces a sheaf map. I wrote the adjunction identification: a family H(W,s) -> F(W) is a map H -> e* F, so the fold is the adjunct of the identity. This is an elementary universal-property calculation. It does not assert that every sheaf section is already a global presheaf direct sum, or that the set of lifts on an arbitrary test object is finite.

3. **Actual B-linear maps.** Opened the summandwise sigma clause in lem-sp-et-proet-coefficient-compatibility, the representative-normalization equation in def-pur-etale-scalar-pullback-iso, def-pur-sheaf-tensor-product and module sheafification's universal property. The scalar/pullback isomorphism defined in that node has the opposite orientation to a_e, so the step uses its inverse explicitly. On i_s(x) tensor b both composites give x tensor b. This elementary generator calculation is before localization in B-module sheaves, so equality is not inferred from equality after forgetting the B-action in a derived category. Repeated sheafification universal properties justify checking those generators; degree-zero coefficients introduce no sign.

4. **Derived equality.** Checked def-weil-pbc-derived-categories really defines localization, lem-pur-derived-change-of-rings really computes on the K-flat models and gives resolution independence, and lem-amb-etale-adjoint-locality really supplies the exact whole-derived adjunction. Checked again that the two comparison nodes normalize the actual maps used in step 3. A functor sends equal chain maps to equal morphisms. The quasi-isomorphism from the chosen representative to K and naturality then give the equality at K. No attempt is made to deduce derived equality from stalkwise equality, nor to tensor a non-K-flat model with a nonflat ring.

5. **Mate orientation.** Read the transpose characterization in def-weil-pbc-adjunction-mate. Substituted the six named functors with domains as written and precomposed with sigma inverse. Its transpose is precisely T(v_A) composed with sigma inverse. This checks the inverse in the conclusion; there is no appeal to a vague compatibility principle.

6. **Compact-support normalization.** Read the Noetherianity lemma, the complete statement of lem-asd-etale-compact-support-normalization, and the explicit etale coefficient square in lem-sp-et-proet-coefficient-compatibility. The first supplies the normalization hypothesis, the second identifies the counit including the right-adjoint identification, and the third states C_B beta = sigma T(C_A) for the actual compact-support coefficient map. Step 1 supplies its Dctf input e* K. I wrote the substitution line by line: naturality moves C_B past a_e, the coefficient square replaces C_B beta, and step 4 replaces the sum counit composite. The resulting identity is the requested one with the compact-support counit. It works for the chosen compactification, without assuming its proper leg finite.

I checked B--E of delivery-errors point by point: no new statement-only nodes to misformat or duplicate; the inherited statement introduces its schemes, rings, functors and comparisons; no recorded search was invented; each dependency is used by its statement, with a literal quotation in citations.json; proof_deps is exactly the union of uses. The six steps carry the proof, with no replacement lemma restating a clause. The preliminary K-flat and domain facts are existing smaller tools, not newly hidden lemmas. Each step is below 2000 characters. A read-only traversal of the current DAG found no path from any cited dependency back to this item.

Small cases checked explicitly: e = identity gives the tensor identity and identity counit; U empty makes both sides the unique map from zero; a disjoint union of sheets gives the same finite fold before and after tensoring; zero K gives zero maps; B = 0 and N = 1 give the zero-coefficient case. For nonflat A -> B, such as Z/ell^2 -> Z/ell, the proof uses a K-flat representative of K and its pulled-back/sum-extended models, so the calculation does not replace derived tensor by ordinary tensor on K itself. Direct sums use finite-support elements regardless of how many lifts exist. All these cases agree with the source's summation intent.

## Unfinished work

None in this stage-1 split. No downstream node was changed. Final server preflight and push results are recorded by the delivery tool.
