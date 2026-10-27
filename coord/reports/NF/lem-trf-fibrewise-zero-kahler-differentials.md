# Stage-1 delivery: lem-trf-fibrewise-zero-kahler-differentials

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-fibrewise-zero-kahler-differentials.json`: item, statement, seven-step split. Mathlib ingredients exist, but no exact whole-item match was found.
- `citations.json`: one verbatim statement quotation for every step/node pair.
- `searches.jsonl`: actual search-command records; the pre-existing item search history is preserved in the node, and the searches of this attempt are appended.
- `report.md`: this report. `write_split.py` is sandbox-only preparation material.

New nodes: 0. New Mathlib leaves: 0. Existing Mathlib leaves are reused, not copied.

## Attachments

None. Searched `lean/WeilConjectures/` by the exact blueprint id and by differential, fibre/fiber, residue-field and unramified concepts. No declaration states every clause under these hypotheses. In particular, differential vanishing over a field and base-change results do not themselves give this item.

## WANTED

None. The Stacks sources needed are present locally.

## What was wrong or changed

The item was statement-only. Its statement, hypotheses, source record, statement dependencies, chapter, unit and inherited blueprint ancestry are unchanged. Filled its proof, exact proof dependency union, proof origin, current search records and split report. No statement dispute and no route change. The source label for the final local-to-global step was checked against the tag map and corrected during self-review to `00HN`, `lemma-characterize-zero-local`, part (6).

## Unfinished work

None for this one-level split. No new unsplit nodes were necessary. This stage writes no Lean and runs no compiler.

## Not duplicates

No new nodes. The whole-DAG and blueprint searches for differential finiteness, base change, Nakayama and local vanishing led to the existing nodes used below. In particular, `lem-weil-pbc-kahler-differentials-base-change` already has the required stronger C-linear module statement. `lem-trf-relative-differential-sheaf-base-change` concerns scheme sheaves, so it is not substituted for this algebra-module statement. Finite generation is proved directly from the defining derivation relations rather than turned into a new node restating the first clause.

## Review by NF

I read the item against Stacks algebra.tex Tag 00UV (`lemma-unramified`), especially its proof of (7)--(9), Tag 00RV (`lemma-differentials-base-change`), Tag 00RZ (`lemma-differentials-finitely-generated`), Tag 00DV (`lemma-NAK`, including its empty-generator specialization), and Tag 00HN (`lemma-characterize-zero-local`). I checked each tag against tags/tags. The inherited use in Morphisms 02G8(2) is the ordinary-fibre criterion; no SGA source is used. I also read the trace-formula chapter and `sk-i-curve-zero` unit records and the current blueprint `lem-trf-local-term-locality` proof (1)--(2): this is a commutative-algebra tool inside the inherited normal-cone/alteration chain, not a replacement of the unit's proof route. There are no new nodes requiring separate literature checks.

For step 1 I opened `def-weil-pbc-kahler-differentials`: its statement explicitly supplies the symbol quotient, additivity, Leibniz and vanishing on R. These imply the written monomial derivative formula by induction on exponents and addition of monomials. Thus the finite algebra generators give finite module generators under exactly the item's hypothesis. `def-weil-finitely-generated-module` is used only for that meaning. I did not cite a definition as a finiteness theorem or hide an independent finiteness assertion.

For step 2 I opened `def-weil-pbc-localization-at-prime`, which gives the fractions, local ring and residue field, and `def-weil-pbc-module-tensor-product`, which gives the balancing relations and pure-tensor generation. The contraction is proved prime in the text. For every denominator outside p its image is outside q, hence nonzero in L. The displayed fraction formula therefore makes the k-to-L map valid even if A or R has zero divisors. The map C-to-L is the actual fibre map, not a map from A/pA confused with the ordinary fibre.

For step 3 I read the statement of `lem-weil-pbc-kahler-differentials-base-change`: its last clause literally states the S'-linear isomorphism with S' tensor over S. Substituting S=A, R'=k, S'=C gives exactly the claimed C-linear comparison. No flatness, no Noetherian condition and no finite presentation occurs in that statement or is used here. The harmless factor interchange is explicitly given.

For step 4 I checked the two inverse tensor maps against the universal property in `def-weil-pbc-module-tensor-product`. I wrote both balancing conditions and verified both composites on generating pure tensors. This proves the residue-field fibre vanishing; it does not assume it from the hypothesis on the differential module of C. The proof is one direct tensor calculation, not a hidden comparison lemma left as a black box.

For step 5 I read the fraction equality and zero criterion in `def-weil-pbc-module-localization`. The localized finite generating family is written explicitly, using the meanings in `def-weil-finitely-generated-module`. The two displayed maps comparing N tensor L and M tensor L respect fraction equality because all images of u,s,s' are invertible in L. I verified balancing by a/t, as written, and both composites on pure tensors. The residue-field interpretation is exactly that of `def-weil-pbc-localization-at-prime`; no exactness or preservation theorem is used. These are routine applications of the cited definitions, marked elementary with their calculations supplied.

For step 6 I opened `lem-weil-pbc-nakayama-local-generators`: its statement includes the tensor formulation, equivalently the spanning condition on k tensor M, for every finite module over a local ring. Apply it to B=A_q, N=M_q, and the empty family. B is local and L its residue field by the cited definition, and step 5 proves N finite, so all hypotheses hold. This uses the lemma's statement, not its proof, and is marked non-elementary.

For step 7 I opened `lem-weil-pbc-linear-map-bijective-at-maximal-localizations`. Its statement gives bijectivity of a module map from bijectivity at every maximal localization. The map used here is M-to-zero; localization of a map is explicitly defined in `def-weil-pbc-module-localization`. Its localizations have zero domain and codomain by step 6, hence meet exactly that hypothesis. The result gives M=0. This avoids accidentally citing the existing ring-only primewise injectivity node as a theorem for arbitrary modules. All three non-elementary tools used in steps 3, 6 and 7 are existing Mathlib leaves, so they do not introduce an off-unit proof route.

I checked B--E of delivery-errors.md point by point. No new node, duplicate, restated clause, circular dependency or hidden unsupported literature invocation is introduced. Every uses-entry has a full verbatim statement quote in citations.json, and proof_deps is exactly the uses-union. The four elementary steps have their actual formulas, not words such as 'transport' in place of an argument. No step exceeds 2000 characters (the longest has 768 characters). The statement is self-contained using its original definition citations, and TeX is single-escaped after JSON decoding.

Small cases checked: A=0 (empty prime spectrum and every unital module zero), a quotient A=R/I (no algebra generators are needed and all differentials vanish), A=R (same), A=k[t] (its fibre differential module is nonzero, so the hypothesis correctly fails), and k[e]/(e^2) (nonzero differentials in every characteristic, so the hypothesis correctly fails rather than ignoring nilpotents). A localization such as Z[1/2] has the zero fibre at (2); this causes no denominator argument at a q over (2), because there is no such q. The fraction comparisons therefore do not assume all ordinary fibres are nonzero or that A is flat.

I read both current Mathlib search phrasings and inspected the relevant source: `KaehlerDifferential.finite` at Kaehler/Basic.lean:433 supplies only finite generation (indeed under essentially finite type), `Algebra.formallyUnramified_iff` only reformulates the conclusion, and the locus results do not furnish the complete criterion with both primewise assertions. Existing base change and local-ring generator statements provide the cited ingredients. Only searches actually run through msearch.py are appended as this attempt's records; prior recorded search history is retained unchanged. The server `review_split` check passed before the full delivery dry run.
