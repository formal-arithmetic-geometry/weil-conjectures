# Stage-1 report: lem-amb-compact-support-staircase-expansion

## Files written

- `dag/nodes/sec-smooth-purity/lem-amb-compact-support-staircase-expansion.json` — statement, split proof, and Mathlib search record; no new nodes.
- `citations.json` — verbatim citations for every non-elementary proof-step dependency.

## Attachments

None. No finished declaration with this exact statement exists under `WeilConjectures/` in the reference source.

## WANTED:

None.

## Not duplicates

No new node was created, so there are no new-node duplicate pairs. I searched the DAG and blueprint for the staircase statement, Tag 0F7K, and the key comparison formulas; the existing nodes are component lemmas with different statements.

## What was wrong or incomplete

The imported item was unsplit: it had the correct fixed-staircase statement but an empty proof and no split report. I kept its hypotheses and conclusion unchanged. The proof now realizes the Tag 0F7K route in three steps: identify the four raw binary comparisons from the compact-support candidate definition, apply the existing vertical and horizontal proper/open interchange pasting identities, and record that the result consists of the two displayed expansions without asserting `L = R` or compactification independence. No statement error or missing hypothesis was found.

## Review by NU

I read the item statement and its source route in `literature/stacks-project/more-etale.tex`, Tag 0F7K (the proof of `lemma-pseudo-functor`), including the fixed grid of squares A, B, and C and the rectangle pasting formulas from Tags 0F7C and 0F7D. I also read the complete statements of `def-amb-etale-compact-support`, `lem-amb-unbounded-proper-open-interchange`, `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`, and `lem-cbc-extension-zero-composition` in the DAG. Step 1 uses exactly the candidate definition, the existence and normalization of each `Gamma_Q`, and the two structural composition isomorphisms; those statements provide the maps and identifications the step invokes. Step 2 uses the cited interchange statement's vertical and horizontal pasting equations, which directly yield the displayed `B+C` and `A+B` expansions after whiskering. Step 3 is the elementary scope check that these are expansion identities only and make no equality or independence claim. I verified that all four hypotheses (open/proper arrows, commutative equations, cartesian squares, and Noetherian finite-ring setting) are introduced in the item itself and are not silently strengthened. I checked both small degenerate cases conceptually (identity squares and empty/zero objects) against the identity clauses of the interchange and composition statements. The Mathlib searches were rerun with `msearch.py` in both requested phrasings; hits were unrelated topology, sheaf restriction, or generic functor-composition declarations, so the item remains non-Mathlib. The preflight `check_dag` passed before this report was written.

## What could not be finished

Nothing.
