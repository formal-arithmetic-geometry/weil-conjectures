# Worker report

## Files written

- `lem-coef-free-module-orbit-cell-filtration.json`: item split in place; no new nodes and no Mathlib leaf.
- `citations.json`: verbatim citations for every nonempty step dependency.

## Attachments

None. I searched both read-only Lean trees for the item id, blueprint tag, and the relevant free-module/orbit terms; no sorry-free project declaration states this item.

## WANTED

WANTED: Emily Riehl, *Category Theory in Context* / Riehl–Verity material at Proposition 5.3.3 and Lemma 6.1.8 (the online `adjunctions.pdf` source is cited by the item but no archival copy is present in `literature/`). The proof below is written directly from the stated degreewise orbit criterion.

## What was checked and corrected

The repository item was unsplit and carried stale creation metadata from another worker; I changed only that metadata to group NK and retained the statement, chapter, unit, and blueprint ancestry. The statement was checked against the downstream use in `lem-coef-walking-module-weight-cells`; no hypothesis was added or removed. The Mathlib searches were rerun for this item with `msearch.py` (grep, leansearch, Loogle, and LeanFinder). They return only generic simplicial-set cell/factorization declarations, so the item remains non-Mathlib.

No new node was created. The proof uses the existing definitions `def-weil-pbc-simplicial-set` (simplicial operators and simplicial subsets) and `def-coef-coherent-monad-modules` (simplicial-set/action conventions). I read both statements in full. Step 1 constructs the degreewise pushout quotient and checks that its relations are stable under operators and the action. Step 2 verifies surjectivity using the assumed orbit bijection and the fact that non-surjective operators factor through proper faces. Step 3 verifies injectivity, separating old elements from new surjective representatives and using the orbit bijection for uniqueness. Step 4 checks equivariance and the universal property of the pushout degreewise. Step 5 applies the successor pushouts and the given limit union condition to obtain the small transfinite composite and the empty-base cellular-weight clause. Edge cases checked include `n_σ = 0` (empty boundary), an empty `R_α`, and `A = ∅`.

## Review by NK

I read the item statement, the chapter and unit records, the blueprint ancestor `prop-coef-integral-exceptional-adjoint`, and the full statements of both cited definition nodes. The proof has no hidden auxiliary lemma: its only substantive argument is the explicit degreewise quotient calculation. Every step's uses match the cited statement: Step 1 uses the definitions of simplicial operators and the simplicial action; Step 2 uses closure of a simplicial subset under operators; Step 4 uses the action convention. Steps 3 and 5 are direct quotient and transfinite-composite arguments and need no external node. I checked that proper-face images are old, that the stated bijection applies only to surjective operators, that old/new images cannot coincide, and that the $0$-simplex cell has empty boundary. No SGA source is cited, no duplicate node was created, and the proof steps are each below the long-step review threshold.

## What could not be finished

Nothing remains for this split; delivery validation is the remaining required operation.
