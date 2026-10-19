# Q16: lem-per-birational-generic-localization

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-birational-generic-localization.json`: existing statement, now split into seven proof steps; no exact Mathlib match found. Statement and statement dependencies preserved.
- `citations.json`: one entry for every step/node citation, with a verbatim portion of that node's statement.
- `report.md`: this report.

No new nodes; no new Mathlib leaves. The sandbox also contains the search command's `searches.jsonl` and the local construction script `write_split.py`, neither of which is a DAG delivery file.

## Attachments

None. Searched the read-only slopmaster2 `WeilConjectures/` tree for the item id, birational localization, and the generic-localization terminology. The only birational hit was the normalization docstring, which does not state this assertion. The item has no Lean declaration recorded. No source-only sorry declaration was treated as a finished proof.

## WANTED

None. All mathematical sources needed are present locally.

## Audit of the inherited node and sources

The statement is correct as written, including for nonreduced and non-Noetherian rings. No statement dispute or correction is needed. The source is exactly the affine paragraph of Stacks Tag 0BAB (`morphisms.tex`, `lemma-birational-generic-fibres`). The imported item was statement-only; it is now a proof, rather than an application to a newly named restatement. The field-valued surjection, its kernel, maximality, uniqueness of the prime, and the final inverse map are written out.

Read the chapter/unit records and the current main-20261015 ancestor statement/proof location. This is a deeper algebraic tool in the previously split common-dense-open reduction. The current ancestor's Step 1 does not itself state this localization argument; it is inherited through `lem-per-birational-common-dense-opens`. We preserve that ancestry and do not claim the current blueprint proves this ring assertion. Its actual source remains 0BAB. No chapter, unit route, realization record, protected metadata, or ancestor node was changed.

The existing `lem-trf-unique-prime-localization` was considered and rejected as a citation: it assumes a finite ring map and thus cannot be applied here. The existing minimal-prime-localization Mathlib leaf was also read; it concerns localization at the target's own prime and does not itself identify the base localization. Neither fact is silently used to prove the conclusion.

## Mathlib and duplicate searches

Retained all four inherited search entries unchanged. Ran fresh logged searches through the required msearch command: two distinct LeanFinder phrasings, LeanSearch, a grep in `RingTheory/Localization`, and Loogle. Read the hits and the source of `IsLocalization.localizationLocalizationAtPrimeIsoLocalization` (LocalizationLocalization.lean:156), `IsLocalization.subsingleton_primeSpectrum_of_mem_minimalPrimes` (AtPrime/Basic.lean:475), and `Localization.localRingHom_unique` (AtPrime/Basic.lean:273). They provide localization transitivity, a singleton spectrum after localizing at a minimal prime, and uniqueness of the map on local rings respectively. None states this assertion or specializes to it in one line: proving the base localization has only one prime is still the substance. Two Loogle inputs used nonexistent identifiers and are recorded as invalid queries with no absence conclusion; the corrected `Localization.localRingHom_unique` query returned its declaration. Every newly recorded query is copied from this item's actual search log, including failed query diagnostics.

Searched the whole DAG by title/concept and Tags 00E3/0BAB, and used `tools/blueprint_refs.py search` for birational, localization prime, minimal prime, nilradical, and local ring, together with the ancestor command. The relevant general correspondence already exists as `lem-weil-pbc-localization-prime-residue-field-iso`, while minimal-prime existence and maximal-ideal existence are existing Mathlib leaves. The prime/principal-only node `lem-weil-pbc-primes-of-localization` is insufficient for the localization at the image of the base complement. There is no need to create any node.

## Not duplicates

No new node was created, so there are no new/existing node pairs to distinguish.

## Review by Q16

I read Stacks `morphisms.tex`, Tag 0BAB, the entire affine-ring paragraph, including its residue-field surjection and unique-minimal-prime argument. For the reused algebraic facts I read `algebra.tex`, Tag 00E3 (`lemma-spec-localization`, statement and proof), and Tag 00E0 (`lemma-Zariski-topology`, the minimal-prime and maximal-ideal assertions and their proofs). I also read the localization-at-a-prime and residue-field discussion in Section 07BH. There are no new nodes needing a separate source review.

For Step 1 I checked the definition node `def-weil-pbc-localization-at-prime`: its fraction formula/equality criterion supplies the localization language, and its base-localization convention is exactly the item’s convention. The contraction hypothesis makes every denominator avoid the target prime. The displayed formulas prove that the composite is the particular generic-local-ring map from the hypothesis, rather than just some isomorphism between the rings.

For Step 2 I read the full statement of `lem-weil-pbc-localization-prime-residue-field-iso`. Its clause (1), not its residue-field clause or its proof, gives both extension/contraction identities used here. The multiplicative subset is the image of the base complement, is disjoint from the prime, and both applications are actual fraction localizations satisfying (a)-(c). This is the only off-unit statement tool, declared in `split_report.tool_uses`; the unit does not offer a general commutative-ring prime correspondence.

For Step 3 the cited definition explicitly supplies the residue field as the quotient by the extended prime. I checked both directions of the kernel calculation: invert the denominator, contract the maximal ideal using Step 2, and likewise contract J. Surjectivity comes from the actual composite of the assumed isomorphism and the quotient map. Maximality is proved by lifting an inverse in the field; it does not use an unstated theorem about kernels of surjections.

For Step 4 the correspondence node's clause (1) gives Q prime and P=QC. The separate existing `lem-weil-pbc-prime-contains-minimal-prime` explicitly states that every prime contains a minimal prime, so it applies with ideal zero and requires no Noetherian hypothesis. Uniqueness of the given minimal prime identifies that smaller prime with p. Inclusion of extended ideals is the inclusion of their sets of generators. Step 5 then only uses the definition of a maximal ideal and properness of a prime.

For Step 6 I checked that `lem-weil-pbc-proper-ideal-contained-in-maximal` says exactly that every proper ideal lies in a maximal ideal, without finiteness or nonzero-ring hypotheses beyond properness. The principal ideal is proper exactly when its generator is not a unit. The short argument proving the resulting maximal ideal prime is included, so the unique-prime statement applies. In Step 7 the cited localization definition's equality criterion is used explicitly with a witness v outside p; v and both denominators become units by Step 6. This proves well-definedness, and checking the two composites on the displayed fractions proves that the canonical map, not merely the rings, is invertible.

I checked B--E of delivery-errors point by point. There are no new statement-only nodes to contain proof sketches or unsupported notions. Each citation is to its statement, with an exact quote saved in citations.json. Non-elementary steps 2, 4, 6 cite the correspondence, minimal-prime existence, and maximal-ideal existence facts they use. The elementary steps are explicit fraction computations or short ideal arguments. No new clause of the item was renamed as a lemma, and no unspecified standard comparison is used. All steps are below 750 characters, hence none exceeds the 2000-character long-step threshold. The proof follows the 0BAB route and uses no SGA source.

Small-case tests: a field identity gives C=A_p=B_q immediately. For B=k[x] and A=k[x,e]/(e^2,xe), the unique target minimal prime is (e), the source prime is (0), both generic rings are k(x), and localizing by nonzero polynomials kills e; thus the proof does not require reducedness or injectivity of A to A_p. The quotient map in the reverse direction, from k[x,e]/(e^2,xe) to k[x], also satisfies the hypotheses and shows no injectivity of the original ring map is assumed. The zero ring has no prime ideal, so the stated hypotheses exclude it. Minimal-prime existence and the maximal-ideal argument remain valid with infinitely many other primes and without a nilpotence bound. No added finite-generation, domain, flatness, or separatedness condition appears.

## What could not be finished

Nothing remains mathematically unresolved. Required server dry run and delivery follow this report.
