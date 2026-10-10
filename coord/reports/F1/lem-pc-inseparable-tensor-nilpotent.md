Files written:

- `dag/nodes/sec-picard-framework/lem-pc-inseparable-tensor-nilpotent.json`: statement, four proof steps, and split report; no new nodes; Mathlib no exact match.
- `citations.json`: verbatim citation for step 2.

Attachments: none.

WANTED: `literature/stacks-project/algebra.tex`, Algebra Tags 030V and 030W, for the field-theory calculation; the source text is not present in this checkout.

## Review by F1

I checked the item against the imported source location, Algebra Tag 030V together with Tag 030W, and against the neighboring parent node `lem-pc-finite-extension-tensor-algebraic-closure-reduced-separable`. No sorry-free declaration in the project source states this item, and no existing DAG or blueprint node states the same tensor-nilpotent conclusion. The existing node `lem-weil-pbc-minimal-polynomial-quotient-field-iso` was read in full; its statement supplies exactly the quotient identification used in Step 2.

Step 1 introduces the minimal polynomial and uses the definition of inseparability to obtain a repeated root in the algebraic closure. Step 2 factors out one repeated-root factor and takes the class of `g=P/(T-beta)`; the class is nonzero by the degree argument and has square zero because `g^2` is divisible by `P`. The cited node says verbatim that the minimal-polynomial quotient is isomorphic to the generated field, which is the only non-elementary cited input. Step 3 verifies the inclusion `k(alpha) -> K` and the injectivity after tensoring over the field `k`; Step 4 is the definition of reducedness. I checked the edge case of a purely inseparable degree-p extension, where `P=T^p-a` and the construction gives the usual nilpotent class, and the characteristic-zero case where the inseparable hypothesis cannot occur.

The Mathlib searches were rerun for the item with LeanFinder, Loogle, grep, and LeanSearch. LeanFinder found only general geometric-reducedness and nilpotence ingredients; Loogle found no usable declaration; grep found nilpotence and geometric-reducedness utilities but no converse; LeanSearch was unavailable. These results are recorded in the item file.

No statement hypotheses were added or dropped. The only source text unavailable locally is recorded above as WANTED.

What could not be finished: no Lean proof was written because this is a stage-1 natural-language DAG split.

## Second reading by F1

- Statement checked against Algebra Lemma Tags 030V and 030W: finite field extension, algebraic closure, inseparable minimal polynomial, and nonzero nilpotent conclusion agree hypothesis by hypothesis.
- Step 1 checked against the repeated-root calculation in Tag 030V and tested on $T^p-a$ in characteristic $p$: valid; the characteristic-zero edge case is vacuous.
- Step 2 checked against the quotient calculation in Tag 030V and the existing quotient-isomorphism node: valid after correcting $g^2=P Q$ (the worker had incorrectly written $P Q^2$); the degree argument gives a nonzero class.
- Step 3 checked against the field-vector-space injection argument in Tag 030V: tensoring the inclusion with the $\bar{k}$-vector space preserves injectivity, so the nilpotent remains nonzero.
- Step 4 checked against the definition of reducedness and the zero-object edge case: valid.
- Existing cited node `lem-weil-pbc-minimal-polynomial-quotient-field-iso` was read; its statement supplies exactly the quotient identification used in Step 2. No new node or Mathlib leaf is needed; duplicate and blueprint searches found no replacement.
- Changed Step 2's divisibility identity from $g^2=P Q^2$ to $g^2=P Q$, and recorded the correction here.
- The source text is available in the local Stacks review checkout (`algebra.tex`); the original WANTED note is retained as historical worker context.
