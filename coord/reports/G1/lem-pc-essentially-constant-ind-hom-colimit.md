# Stage 1 report

## Files written

- `lem-pc-essentially-constant-ind-hom-colimit.json`: split statement.
- `def-pc-essentially-constant-ind-diagram.json`: new unsplit definition node; Mathlib searches found no exact match.

## Attachments

None. No sorry-free project declaration with the item tag or exact statement exists in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`.

## WANTED

None.

## Not duplicates

`def-pc-essentially-constant-ind-diagram` vs `lem-pc-essentially-constant-pro-hom-colimit`: the new node defines the covariant filtered ind condition (maps `F(j) -> X` and a section `X -> F(j0)`), while the existing item concerns the contravariant cofiltered pro condition and proves a Hom-out colimit formula.

`def-pc-essentially-constant-ind-diagram` vs `lem-pc-essentially-constant-ind-hom-colimit`: the new node is the underlying definition of essential constancy, while the item is the distinct theorem identifying a filtered colimit of Hom sets with Hom into the constant value.

## Review by G1

I read the imported item source at Stacks Derived Tag 0FND, proof line 9515, and the essential-constancy characterization at Categories Tag 05PY. The item statement uses the existing derived-category definition and the new ind-diagram definition. Step 1 uses only the new node's natural maps `p_j` to define the canonical map. Step 2 uses its section `s` and the retraction identity to prove surjectivity. Step 3 uses its eventual factorization clause together with filteredness to prove that equal images agree at a later stage. Step 4 is the direct naturality check. I checked each quoted dependency against the new node statement and recorded the exact quotes in `citations.json`. I searched the DAG and blueprint for Tags 05PY and the ind Hom formula; no duplicate definition or project declaration was found. The new definition is statement-only as required, and its Mathlib searches recorded the nearest `IsEventuallyConstantTo` results as strictly stronger than Stacks' notion.

## What was wrong or corrected

The imported item had no proof and cited `def-weil-abstract-derived-category` for a notion that it does not define. I preserved the item statement but added the missing explicit definition dependency. The first draft of the definition had the transition orientation reversed; it was corrected to the filtered direction `F(j) -> F(k)` and the factorization `F(j) -> X -> F(j0) -> F(k)`.

## What remains

No unresolved mathematical or tooling issue remains in this split.

## Second reading by G1

- Item statement: checked against Derived Tag 0FND, label `lemma-pre-derived-adjoint-functors-general`, first equality, and Categories Tag 05PY; the filtered ind orientation and Hom-colimit direction agree hypothesis by hypothesis.
- Definition node: checked against Categories Tag 05PY; the natural maps, section, retraction, filtered common upper bound, and factorization clause are self-contained and correctly oriented.
- Step 1: checked against the naturality clause of the definition; postcomposition with `p_j` is the canonical colimit map and is elementary.
- Step 2: checked against the section and retraction clauses of the definition; the representative `s` composed with `g` proves surjectivity and is elementary.
- Step 3: checked against filteredness and the eventual factorization clause of the definition; the common-stage argument proves injectivity. This is not elementary and is marked accordingly.
- Step 4: checked against naturality of the `p_j`; the canonical bijection is natural and the verification is elementary.
- New-node form: the definition is statement-only, self-contained, uses the Stacks tag and label, and records three Mathlib searches with no exact match; no duplicate DAG or Lean declaration was found.
- Small cases: the zero object and a one-object constant diagram give the identity Hom bijection; the empty indexing category is excluded by filteredness, as required.

Changes made: removed the unrelated `def-weil-abstract-derived-category` dependency from the generic definition, removed the same stale dependency from the item, and marked the filtered injectivity step non-elementary because it carries the substantive argument.
