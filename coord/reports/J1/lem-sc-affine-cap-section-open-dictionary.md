# Stage 1 delivery report

1. Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-affine-cap-section-open-dictionary.json`: repaired item with three proof steps.
- `dag/nodes/sec-curve-estimates/lem-sc-affine-standard-cover-finite-projective.json`: statement-only Stacks 00NX node; no Mathlib match.
- `dag/nodes/sec-curve-estimates/lem-sc-affine-finite-projective-prime-membership.json`: statement-only pure-module prime-membership node; no Mathlib match.

2. Attachments: none.

3. WANTED: none. The Stacks TeX sources were read from `/home/ubuntu/c1-stacks-review/schemes.tex` and `/home/ubuntu/c1-stacks-review/modules.tex`; their labels are the same sources cited by the item.

4. Return repairs: I deleted the two former children because they restated clauses of the item. I restored the item's original citation `[lem-weil-pbc-finite-projective-rank-locally-constant]` and its `stmt_deps` entry. The finite projectivity argument is now in step 2, using the strictly smaller 00NX converse node; the stalk argument is in step 3, using only the strictly smaller pure-module criterion. Both retained nodes have `created` with `by`, `item`, and `date`.

## Review by J1

I read Schemes Lemmas 01IA (`lemma-quasi-coherent-affine`) and 01IB (`lemma-equivalence-quasi-coherent`) in `schemes.tex`, and Modules Lemma 01CY (`lemma-s-open`, line 4360) in `modules.tex`. The item statement agrees with those sources hypothesis by hypothesis: affine `X=Spec(R)`, quasi-coherent invertible `M`, its global module `N`, and the section nonvanishing condition. The original finite-projective-rank citation was restored unchanged.

Step 1 cites the existing affine tilde/Gamma adjunction, whose statement supplies the counit isomorphism for every quasi-coherent module. Step 2 uses the invertible-module definition for local rank-one trivializations, the existing principal-open quasi-compactness node for the finite unit-ideal cover, the existing affine tilde-sections node for `N_f = tilde(N)(D(f))`, and the new 00NX node for the converse from a finite standard-open free cover to finite projectivity. The rank-one conclusion follows by localizing a rank-one trivialization at a prime. Step 3 uses the existing tilde-stalk localization statement to identify `M_p` with `N_p`, then the new pure-module node for the exact equivalence `s/1 in pN_p` iff `s in pN`; the last sentence uses the definition of the nonvanishing locus in the existing 01CY node. Each citation says the fact used, and `citations.json` quotes a verbatim part of every cited statement.

For the new standard-cover node I checked Stacks 00NX (7) => (3), and searched LeanSearch, LeanFinder, and Mathlib source for a single bundled theorem; only separate localization/projectivity components appeared. For the new prime-membership node I checked the localization-and-quotient argument over `R/p` and searched all three Mathlib routes; no exact declaration exists. Small cases include `N=R` (the criterion reduces to ordinary localization membership), `s=0`, and `s=1`. The former relabelling nodes and the inaccurate report claim about absent TeX sources were corrected in this repair.
