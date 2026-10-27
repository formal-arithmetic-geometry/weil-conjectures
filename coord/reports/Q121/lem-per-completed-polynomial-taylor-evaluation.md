## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-completed-polynomial-taylor-evaluation.json`: the item, split into seven proof steps; no new nodes.
- `citations.json`: verbatim statement quotes for every cited dependency.
- `searches.jsonl`: the required Mathlib searches run by Q121. The item also retains its inherited NX search records unchanged.

## Attachments

None. I searched the upstream project for the blueprint tag and for completion, evaluation, Taylor, and partial-derivative declarations; no sorry-free project declaration states this item.

## WANTED

None. The Stacks Project sources used here are present locally.

## What I checked and corrected

The imported item had an empty proof and an inherited formal-algebraization pointer. I kept its statement and all hypotheses, including arbitrary coordinates `y`, no completeness assumption on `A`, the quadratic modulus `I^(2s)`, and `r = 0`. I used the existing completion and polynomial/derivative definition nodes rather than creating duplicates. The proof fills the omitted term-by-term argument in Stacks Tag 0AK3 by working at the quotients `A[x]/I^n A[x]` and passing to inverse limits. This avoids silently replacing the completion by a restricted power-series ring or assuming `A` is complete.

## Review by Q121

I read the item source in `literature/stacks-project/restricted.tex`, Tag 0AK3, and the universal-property discussion in `literature/stacks-project/formal-spaces.tex`, Tag 0AJM. I also read the existing statements of `def-weil-pbc-mv-polynomial-ring`, `def-weil-pbc-adic-completion`, `def-weil-pbc-polynomial-partial-derivative`, and the Mathlib leaf `lem-weil-pbc-module-completion-complete`. Step 1 uses the latter exactly for completeness, separatedness, quotient surjectivity, and the kernel `I^n P`; I checked that its module `M` can be the polynomial ring and its ideal the extended finitely generated ideal. Steps 2 and 3 use the polynomial universal property and the inverse-limit definition to construct evaluation, prove continuity, and prove uniqueness; the arbitrary `y` hypothesis is used only through polynomial evaluation, so no hidden `y ∈ IT` assumption enters. Steps 4 and 5 use the stated polynomial derivative formula and Leibniz rule; I checked that an `A`-linear derivative preserves every power of the extended ideal because it kills coefficients from `A`. Step 6 expands each finite monomial and identifies the one-increment terms with the derivative formula; the remaining terms have at least two increments and therefore lie in `I^(2s)T`, with no division by factorials, so zero divisors and positive characteristic are allowed. Step 7 uses approximation modulo `I^(2s)` for `f` and its derivatives and checks that multiplying an error by `z_i ∈ I^sT` remains in `I^(2s)T`; it also explicitly checks the empty tuple when `r = 0`. I verified every citation quote against the cited node statement and retained only existing DAG dependencies. I also tested the limiting cases `I = 0` (ordinary polynomials, with zero increments), `I = A` (completeness forces `T` and `P` to be zero rings), and the noncomplete coefficient ring `A = ℤ`, `I = (p)`, evaluated in `ℤ_p` at a unit coordinate. All constructions remain valid. No source error or duplicate node was found.

## Not duplicates

No new nodes were created, so there are no duplicate pairs to report.

## Unfinished

Nothing remains for this stage-1 split.
