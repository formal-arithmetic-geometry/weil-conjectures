# lem-weil-pbc-ml-sets-tower-limit-nonempty

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-ml-sets-tower-limit-nonempty.json`: split the existing statement into three steps; no new nodes. Mathlib verdict remains no single matching declaration, with the earlier five-declaration candidate chain retained.

## Attachments

None. The item has no Lean declaration in either source branch.

## WANTED

None. Stacks Project `algebra.tex`, Definition 0595 (`definition-ML-system`), Example 0596 (`example-ML-surjective-maps`), and Lemma 0597 (`lemma-ML-limit-nonempty`) were read in the local source checkout; the tags were checked in `tags/tags`.

## Corrections and checks

The item was unsplit, with no proof steps. The statement agrees with 0597 specialized to positive integers and with the ML definition 0595. Stacks 0596 asserts surjectivity of transitions on stable images without writing the element argument; Step 2 now chooses an index at least `max(c(i), c(i+1), i+1)` and checks both membership and surjectivity. Step 3 writes the dependent-choice recursion behind Stacks' appeal to the axiom of choice. The existing `def-weil-inverse-system` states the only cited notion. No proof step uses the statement of another node, and no new node duplicates one already in the DAG.

Edge cases checked: `c(i)=i` yields `B_i=E_i` at that level; an empty stable image cannot occur because every `E_k` is nonempty; transitions need not be surjective on the original `E_i`, only on the `B_i`; the proof does not require a monotone choice of `c(i)`. A one-point tower and towers with temporarily larger images both satisfy the argument.

## Unfinished

None for this split. The node remains a non-Mathlib statement for later formalization.

## Review by E1

I read Algebra Definition 0595 (`definition-ML-system`), Example 0596 (`example-ML-surjective-maps`), and Lemma 0597 (`lemma-ML-limit-nonempty`) in `algebra.tex`. The item statement is the positive-integer specialization of 0597, with the inverse-system composite and stabilization hypothesis stated explicitly. No new nodes were added; the current DAG search found only the cited `def-weil-inverse-system`, whose statement defines exactly the sets, transition maps, composites, and compatibility used.

Step 1 defines stable images and uses only the inverse-system composite identity; nonemptiness follows from the nonempty source level. Step 2 uses the same identity and a common index at least `max(c(i), c(i+1), i+1)` to prove both well-definedness and surjectivity, then checks that compatible sequences in the restricted tower and original tower coincide. Step 3 is the positive-integer dependent-choice construction from 0597's final sentence. Every non-elementary source fact is either the item's hypothesis or the cited inverse-system definition; the argument does not treat the Mathlib composite candidate as a leaf. I checked c(i)=i, one-point towers, temporary image growth, and non-surjective original transitions. No A-F issue remains and no worker revision was required.
