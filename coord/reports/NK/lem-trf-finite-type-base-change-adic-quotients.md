## Worker report

Files written:

- `dag/nodes/sec-trace-formula/lem-trf-finite-type-base-change-adic-quotients.json`: statement, split using existing Mathlib leaves; no exact Mathlib match for the item.
- `citations.json`: eight verbatim statement quotations, one for each citation in each proof step.
- `report.md`: this report. `searches.jsonl` was produced by the required search command; `prepare.py` is sandbox-only preparation, not a delivery file.

## New nodes

None: zero new nodes and zero new Mathlib leaves. The completion modulo powers, local completion, localization of a quotient, and the relevant definitions already exist. The tensor inverse, the equality Q=qD, and transition compatibility are short calculations in the item's proof, not separate lemmas or clauses relabelled as nodes.

## Attachments

None. Searches in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` and `Comparator/`, both for the exact blueprint tag and for completion/adic quotient/base-change language, and in `dag/lean_names_upstream.json`, found no project declaration stating the item. The completion-related project hits concern derived coefficient completion or curve compactification. Upstream master is not used as finished-proof evidence.

## WANTED

None. All sources required for the proof are present in `literature/stacks-project/algebra.tex`.

## Statement and source clarification

The mathematical statement is true as imported; no hypotheses or conclusions have been added or removed. I put its formulas in TeX, made commutativity and the definition of a local ring explicit, and specified the ordinary tensor ring multiplication and structure maps. The imported reference `def-weil-finite-type-morphism` defines a scheme morphism, whereas the statement needs a finite-type algebra. I replaced it by the existing `def-weil-pbc-finite-type-algebra`, whose statement explicitly gives that notion. I added `def-weil-pbc-module-tensor-product` for its universal property and generation by pure tensors; the retained `def-weil-module-base-change` describes scalar extension.

The imported source field names 00MA(3). This theorem applies to a finite MODULE, and a finite-type algebra C (or C/q^n) need not be finite over R. I did not apply it to either module. I read Tag 05GG, `lemma-hathat-finitely-generated`, including its kernel formula and proof, and Tag 00CT, `proposition-localize-quotient`, including its ring-valued fraction formula. These give exactly the two non-elementary inputs actually used. I also read Tag 05GI, `lemma-radical-completion`, for the local-completion statement, and 00MA, `lemma-completion-tensor`, to check its finite-module restriction. The immutable source field is retained, while the actual source and argument are recorded in every proof step and `proof_origin`.

I read Tag 0GDX, `lemma-relative-map-approximation-pre`, and confirmed that its data already ASSUME the completed-local isomorphism. It is not cited as a proof of the item. The inherited blueprint ancestry is retained. I read `dag/units/sk-i-curve-zero.json`, the chapter record, and the current main-20261015 `lem-trf-local-term-locality.proof.md`: the auxiliary ring calculation belongs to the inherited completed-local branch of the specialization route, not to a literal sentence of the current locality proof. No unit or chapter statement or route is replaced.

## Searches and reuse

The required msearch command was used for LeanFinder (two different phrasings), LeanSearch, Loogle, and grep of RingTheory and then specifically RingTheory/AdicCompletion. All actual invocations are appended to the item's inherited `mathlib_searches`, with their exact query strings and the returned declaration names. The second semantic phrasing found `AdicCompletion.ofTensorProductEquivOfFiniteNoetherian` and related declarations; their signatures assume `Module.Finite R M`. They do not state this assertion for a finite-type local algebra. The more specific grep found the kernel/evaluation formulas in AdicCompletion/Completeness.lean and Algebra.lean, supporting the already existing completion leaf, not a direct match for the item. No unavailable service is called an absence result, and no unrun search is recorded as new work.

Before deciding whether helpers were needed, I searched the whole DAG by 00MA and by completion/quotient/localization/tensor concepts, read the resulting pertinent statements, and ran `tools/blueprint_refs.py search` for completion, completed local, localization quotient, and adic quotients. The first broad keyword search has many irrelevant coefficient-theory results; I narrowed the inspection by node titles and statements rather than treating those as matches. The existing exact helpers are `lem-weil-pbc-adic-completion-mod-power` (05GG) and `lem-weil-pbc-localization-at-prime-of-quotient` (00CT). `lem-weil-pbc-completion-finite-quotient` is instead about R[z]/(z^p-f), and `lem-weil-pbc-localization-quotient-by-prime` is a localization-prime correspondence; I did not duplicate either. The item has no equivalent blueprint statement found by these searches. `blueprint_refs.py ancestor` confirms `lem-trf-local-term-locality` as its inherited blueprint ancestor.

## Not duplicates

No new nodes were created. All needed non-elementary statements are cited under existing ids.

## Review by NK

I checked the split against delivery-errors B through E with the node statements and algebra.tex open. There are no new-node statements to audit. Each proof step is below 2000 characters; none hides a general lemma behind a comparison or a claim of standardness.

Step 1 uses the precise definition in `def-weil-pbc-noetherian-ring` (every ideal is finitely generated), so the hypothesis I.FG of the existing 05GG leaf really holds for m. I read the full statement of `lem-weil-pbc-adic-completion-mod-power`: it supplies the R-algebra projection, its composite with iota, surjectivity, and kernel m^n R-hat, all of which are used later. This agrees with the text and proof of 05GG. I also read `lem-weil-pbc-local-completion-local-ring` and 05GI/05GG: its stated maximal ideal mR-hat explains precisely the maximal ideal mentioned in the hypotheses. These helpers are existing Mathlib leaves, so they require no off-unit route declaration.

Step 2 cites `def-weil-pbc-module-tensor-product`, not a definition of scalar extension as a substitute for a theorem of right exactness. Its statement gives exactly the balanced-map universal property and generation by pure tensors. I checked that m^n acts as zero on C/q^n by taking products, so theta_n is defined, and that the two ring maps agree on R. Multiplicativity is proved on pure tensors and then on finite sums. The image of each generator of q^nD is zero, so the quotient map beta_n exists. The composite beta_n alpha_n is checked on every class of c. No flatness or finite-module assertion is used.

Step 3 cites the same tensor definition and the actual kernel formula in the completion leaf. Choosing r only represents an element of R/m^n, and requires no surjectivity of R to its completion. The error a-iota(r) is a finite ideal-linear combination of elements of m^n, which permits balancing each term into the C factor. Thus the error dies modulo q^nD. Equality on pure tensors extends to equality of maps because the cited definition expressly says that those tensors generate. This constructs the inverse, rather than assuming an unnamed base-change/quotient isomorphism. The argument is a direct calculation from Step 1 and the tensor definition, and is marked elementary.

Step 4 uses the established n=1 isomorphism. I checked the subtle prime identification without assuming Q=qD: for d in Q lift its class modulo qD to c, then contraction forces c into q. This proves the reverse inclusion. Ideal-power extension is written out as equality of the generating products. The prime need not be maximal: q/q^n and Q/Q^n are primes because their quotients are the domains C/q and D/Q. The extra contraction-to-the-completed-base hypothesis is consistent (mR-hat is the maximal ideal and lies in qD); the computation does not require any stronger assumption.

Step 5 cites `def-weil-pbc-localization-at-prime` for fractions, the maximal-ideal description, and locality, and `lem-weil-pbc-localization-at-prime-of-quotient` for its unique isomorphism with the specified fraction formula. I opened that node and checked both uses against its exact hypotheses: I=q^n is contained in q, and I=Q^n is contained in Q, for n>=1; the corresponding primes in the quotients contract to q and Q. Step 4 identifies Q^n with q^nD. Extension commuting with ideal powers is justified by generators in the step. The induced localized isomorphism is explicitly given on fractions with an inverse, and the formula is exactly the map induced by the canonical local map, not merely some abstract ring isomorphism.

Step 6 checks transition compatibility on every fraction class. Both composites have the same formula f(c)/f(s) modulo the lower power, so there is no hidden functoriality assertion or inverse-limit theorem. The item only needs finite-level compatibility; it does not pass to a limit here.

Small cases checked: R a field (m=0, R-hat=R, giving the identity even for nonmaximal q); C=R (the usual 05GG quotient isomorphism); R=Z_(p), C=R[t], q=(p), with residue field F_p(t) after localization (showing that one must not assume q maximal or C/q finite over R); q=(p,t), giving nontrivial nilpotent thickening quotients; n=1, including the prime calculation; and C=0, where no prime q exists and the implication is vacuous. A nonzero nilpotent maximal ideal merely makes the completion eventually constant and causes no exception. All n>=1 are handled uniformly. No new assertion was left unproved, and there is no statement dispute.

Corrections during self-review were the finite-type definition reference, replacement of the inapplicable finite-module shortcut by the explicit inverse, and explicit verification of Q=qD before comparing the powers. The quotations in citations.json were copied from the actual statements and verified as substrings; in particular the localization leaf really contains the fraction formula required by Step 5.

## Unfinished work

None in the split. Server dry-run and delivery results are recorded below when available.
