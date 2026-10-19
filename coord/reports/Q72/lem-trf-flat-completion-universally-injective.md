# Q72 stage-1 report

Files written:

- `dag/nodes/sec-trace-formula/lem-trf-flat-completion-universally-injective.json` — split statement, no statement change.
- `dag/nodes/sec-trace-formula/lem-trf-associated-primes-fibre-bound.json` — statement-only auxiliary node, Mathlib no match.
- `dag/nodes/sec-trace-formula/lem-trf-universal-injective-finite-test.json` — statement-only auxiliary node, Mathlib no match.
- `citations.json` — verbatim citations for every proof-step use.

Attachments: none.

WANTED: none.

The source statement and all hypotheses were checked against Stacks Tag 05DM in `literature/stacks-project/flat.tex`; the completion is the inverse limit of the quotients by powers of the extended ideal, and universal injectivity is over the original ring $R$. No Lean declaration with this item tag or an exact proof exists in the read-only slopmaster2 source.

The split follows the source. Step 1 uses the finite tensor-test criterion of Tag 058K; the Noetherian hypothesis makes finite modules the relevant tests. Step 2 checks the canonical map from a tensor product into the completion and observes that its composite with the completion comparison is the map for the finite tensor module. Step 3 checks that $M=Q\\otimes_RP$ is finite over $S$, identifies the completion kernel with the intersection of powers, and invokes the existing associated-prime localization injection. Step 4 applies the new fibre associated-prime node, which is the specialization of Tags 05C2 and 05E0, then verifies that the stated hypothesis makes $IS+\\mathfrak q$ proper and applies the existing prime-over-proper-ideal node. Step 5 applies the existing Krull-intersection localization node to $S$, $IS$, $M$, and the chosen prime; the localization-transitivity sentence is elementary. Step 6 applies the same associated-prime localization injection and then the finite-test criterion.

I searched the whole DAG for Tags 05C2, 05E0, 058K, associated-prime fibre statements, finite tensor tests, and completion universal injectivity. The existing node `lem-weil-pbc-associated-primes-flat-base-change` states the different $N/\\mathfrak pN$ Bourbaki formula, so it is not a duplicate of the fibre statement; the new fibre node is the exact residue-field formulation required by the item. The existing completion and associated-prime localization nodes were cited rather than duplicated. Mathlib searches were run for the item and both new nodes with LeanSearch, LeanFinder, Loogle, and Mathlib grep; no exact theorem was found, and the recorded verdicts distinguish unrelated adic injectivity, flatness, and fibre-spectrum results.

## Not duplicates

`lem-trf-associated-primes-fibre-bound` vs `lem-weil-pbc-associated-primes-flat-base-change`: the existing node gives a Bourbaki union/equality using $N/\\mathfrak pN$, while the new node gives the residue-field fibre $P\\otimes_R\\kappa(\\mathfrak p)$ for the contraction of an associated prime of $Q\\otimes_RP$.

`lem-trf-universal-injective-finite-test` vs `lem-weil-pbc-associated-primes-flat-base-change`: the new node is a tensor-test criterion for arbitrary maps, whereas the existing node concerns associated primes after a flat base change.

## Review by Q72

I read `flat.tex` at Tag 05DM, including the preliminary finite-module reduction, the kernel localization argument, and the final invocation of the Bourbaki fibre result. I also read `algebra.tex` at Tags 05C2, 05E0, and 058K. For Step 1, the finite-test statement explicitly supplies the reduction from universal injectivity to finite tensor factors under the Noetherian hypothesis. For Step 2, the tensor-product definition supplies the induced map and the componentwise completion comparison is the map used in the source. For Step 3, I verified that $Q\\otimes_RP$ is finite over $S$ and that the existing localization node applies to the $S$-module kernel. For Step 4, I checked the contraction $\\mathfrak p=\\mathfrak q\\cap R$, the fibre associated-prime conclusion, and the properness of $IS+\\mathfrak q$ before choosing $\\mathfrak q'$. For Step 5, the existing Krull node has exactly the hypotheses needed after substituting the Noetherian ring $S$, ideal $IS$, finite module $M$, and prime $\\mathfrak q'$; the remaining localization transitivity is an elementary denominator calculation. Step 6 correctly returns from vanishing at all associated-prime localizations to $K=0$ and then upgrades the finite tests to all $R$-modules. I checked small cases $I=0$, $I=R$, $P=0$, $Q=0$, and $R=S$; the $I=R$ case has zero completion and the hypothesis is impossible unless the fibre modules have no associated primes, so the implication remains vacuous as in the source. No statement or hypothesis was changed.
