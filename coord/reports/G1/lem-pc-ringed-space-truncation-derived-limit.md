Files written:

- `dag/nodes/sec-picard-framework/lem-pc-ringed-space-truncation-derived-limit.json` (statement, split; no Mathlib match).
- `dag/nodes/sec-picard-framework/lem-pc-ringed-space-pointwise-truncation-limit.json` (statement-only child, no Mathlib match).
- `citations.json` (verbatim step citations).

Attachments: none. No `WANTED` entries.

The source statement and proof were checked in `/home/ubuntu/c1-stacks-review/cohomology.tex`: Tag 0D64 states the uniform bound result and proves it by Tag 0D63, while Tag 0D62 supplies the pointwise criterion. The new child is strictly more general: it allows a point-dependent function `p_x(m)` and neighborhood basis. I searched the whole DAG and blueprint for the pointwise criterion and found no existing node; the only related node, `lem-pc-qcoh-truncation-derived-limit`, cites this item and does not state the pointwise result.

## Review by G1

I read Tag 0D62 (the pointwise truncation criterion), Tag 0D63 (the bounded pointwise specialization), and Tag 0D64 (the uniform-dimension statement). The item keeps the scheme specialization and all hypotheses from 0D64, including the basis, integer `d >= 0`, negative cohomology degree condition, standard truncations, and the derived limit in `D(O_X)`. The child states 0D62 with all ringed-space objects introduced and explicitly identifies the canonical truncation map.

The sole item step applies the child with `U_x = {U in B | x in U}` and `p_x(m) = d + max(0,m)`. For `m-p < 0`, the item hypothesis applies because `p > p_x(m) >= d`; for `m-p >= 0`, the inequalities `p <= m <= p_x(m)` contradict `p > p_x(m)`. Thus every child hypothesis is verified, and the child gives exactly the desired canonical map and isomorphism. The standard-truncation and derived-limit terminology was checked against the cited definition nodes. I tested the bound on `d=0`, `m<0` (the nonnegative cohomology branch is impossible), `m=0`, and `m>0`; each case gives the required implication. The Mathlib searches returned only generic complex truncation facts and no derived-limit theorem; LeanSearch was unavailable and recorded as such.

No source or statement error was found. No proof was moved wholesale into a node: the child is a genuine stronger criterion, and the item step performs the specialization explicitly.

## Second reading by G1

- Item statement: checked against Stacks Tag 0D64 (`lemma-is-limit-dimension`) in `cohomology.tex`; the scheme specialization, basis hypothesis, `d >= 0`, negative cohomology-degree condition, standard truncation tower, and derived limit in `D(O_X)` agree hypothesis by hypothesis.
- Item step 1: checked against Tags 0D64, 0D63, and 0D62; the cited pointwise criterion supplies exactly the claimed derived-limit isomorphism, while the standard-truncation and derived-limit definitions supply the notation; the basis-neighborhood and integer inequalities are elementary and written explicitly.
- New node `lem-pc-ringed-space-pointwise-truncation-limit`: checked against Tag 0D62 (`lemma-is-limit-per-point`); it is statement-only, self-contained, and retains the source's arbitrary ringed-space hypotheses and pointwise bound.
- New node search: searched the DAG and blueprint for the pointwise criterion and searched Mathlib with LeanFinder, Loogle, grep, and LeanSearch; no exact Mathlib declaration was found, with LeanSearch recorded unavailable.
- Small cases: checked `d = 0`, `m < 0`, `m = 0`, and `m > 0`; the implication `m-p >= 0` is impossible under `p > d + max(0,m)` and the remaining branch invokes the stated vanishing. The zero complex and a field-valued affine scheme satisfy the expected specialization; the empty scheme is vacuous.
- Changes: removed duplicate `proof`/`proof_deps`/`proof_origin` keys from the item JSON; changed the child from the scheme-only `def-pc-derived-category` citation to `def-weil-sheaf-of-modules-category` plus `def-weil-abstract-derived-category`; defined “fundamental system” inline. These repairs make the child self-contained for arbitrary ringed spaces and eliminate ambiguous JSON parsing.
