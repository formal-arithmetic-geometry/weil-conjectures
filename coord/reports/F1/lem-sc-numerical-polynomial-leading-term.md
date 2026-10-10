# Stage 1 report: lem-sc-numerical-polynomial-leading-term

## Files written

- `dag/nodes/sec-abelian-varieties/lem-sc-numerical-polynomial-leading-term.json`: statement node, split, no Mathlib match.
- `dag/nodes/sec-abelian-varieties/lem-sc-generic-stalk-finite-length.json`: statement-only auxiliary node, no Mathlib match.
- `citations.json`: verbatim citations for every non-elementary step use.

## Attachments

None. No sorry-free declaration tagged `(blueprint: lem-sc-numerical-polynomial-leading-term)` or stating Tag 0BEN was found in `WeilConjectures/`.

## WANTED

None. The Stacks sources used are available in the local review checkout and the item source metadata.

## Not duplicates

- `lem-sc-generic-stalk-finite-length` vs `lem-weil-pbc-length-additive-short-exact`: the new node proves finiteness and positivity for a finite module supported at one maximal ideal; the existing node proves additivity of length in a short exact sequence.
- `lem-sc-generic-stalk-finite-length` vs `lem-sc-finite-length-global-submodule`: the new node is the local support-at-a-point criterion used in Tag 0BEN; the existing node is a dimension-one global submodule finite-length theorem for a domain and a principal quotient.

## Review by F1

I read the item statement and its source, Stacks Varieties Tag 0BEN (the local `varieties.tex` copy at the lemma and proof around line 10290), and checked the pushforward reformulation against the projection formula. I also read the existing statements of `lem-pc-euler-additive`, `lem-weil-pbc-length-additive-short-exact`, `lem-weil-pbc-coherent-filtration-integral-subschemes`, `lem-weil-pbc-finite-type-over-noetherian`, `lem-sc-snapper-numerical-polynomial`, and `lem-pc-projection-formula`. Step 1 uses exactly the finite generic-stalk length assertion, Euler additivity, and short-exact length additivity supplied by those statements. Step 2 verifies that proper over a field gives a Noetherian scheme through finite type over `Spec(k)`, then applies the coherent filtration statement and checks each filtration subscheme lies in the support. Step 3 applies the Snapper polynomial bound to lower-dimensional filtration terms and observes that their top-dimensional generic lengths vanish. Step 4 checks the exact ideal sequence, the proper support dimension drop on an integral scheme, and the projection formula identification for the structure sheaf of the integral component; Euler additivity then transfers the result to the ideal. Step 5 performs the finite devissage and records positivity of the nonzero generic lengths. I added `lem-sc-generic-stalk-finite-length` because the source's finite-length-at-a-point input was not stated by any existing DAG node; Mathlib searches found only general length APIs and no matching theorem. I checked the zero-dimensional case separately: every filtration term has support dimension zero and the displayed difference is the zero polynomial of degree below zero by the source convention.

## What was wrong or missing

The imported item had no proof and only one Mathlib search. The missing non-elementary support-point finite-length fact is now an explicit statement-only node, and all item Mathlib searches required by the brief are recorded.

## What could not be finished

No proof in Lean was requested or written at stage 1.

## Second reading by F1

- Item statement: checked against Varieties Tag 0BEN (`lemma-numerical-polynomial-leading-term`) in `varieties.tex` lines 10289--10308, hypothesis by hypothesis; removed the worker-added nonzero hypothesis and zero-polynomial convention.
- Step 1: checked against the finite-support-point statement, Euler additivity, and length additivity; the zero-stalk case is now explicit and the generic-length additivity use is supported by the cited statements.
- Step 2: checked finite type over `Spec(k)` and the coherent filtration statement; the filtration quotients and support-dimension bound match the Tag 0BEN proof.
- Step 3: checked the Snapper polynomial statement and the support inclusion; generic lengths in the degree-`d` sum are explicitly shown to vanish.
- Step 4: checked the exact ideal sequence, proper support dimension drop, projection formula, and closed-immersion cohomology comparison; exact pushforward and cohomology are now cited by their existing nodes.
- Step 5: checked the finite devissage and positivity conclusion against the final paragraph of Tag 0BEN; it is elementary from the preceding steps.
- `lem-sc-generic-stalk-finite-length`: checked against Algebra Tag 00IY (`algebra-lemma-support-point`), with all notions defined and the zero module excluded only where positivity is asserted; small cases include a field and a one-point local scheme.
- Mathlib searches: checked the four recorded item searches and four recorded auxiliary-node searches against `searches.jsonl`; unavailable LeanSearch is recorded as unavailable.
- Changed the item statement to match Tag 0BEN exactly, corrected the new node's `created.item`, repaired step 1's zero-stalk handling, and added exactness/cohomology citations and verbatim citation entries for step 4.
