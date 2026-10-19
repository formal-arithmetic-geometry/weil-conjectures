# Stage-1 report: lem-trf-frobenius-transport-induction

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-frobenius-transport-induction.json`: statement split, no new nodes, no Mathlib leaves.
- `citations.json`: three step-to-node citations.

## Attachments

None. I found no sorry-free declaration tagged `(blueprint: lem-trf-frobenius-transport-induction)` or stating this recurrence exactly in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`.

## WANTED

None.

## What I checked

The imported statement is well-typed and makes explicit the formal induction implicit in the m-th-iterate assertion in `literature/blueprint/main-20261015/blueprint/sec-trace-formula/sk-d-weil/lem-trf-frobenius-operator-compact-description.proof.md`. I searched the DAG and blueprint for an existing induction or coherent-transport lemma; no node states this recurrence. The recorded LeanSearch, Loogle, LeanFinder, and Mathlib grep searches found only general naturality, conjugation, or small-object iteration results, so the item is not a Mathlib leaf.

## Review by Q78

I read the item, its `sk-d-weil` unit and trace-formula chapter records, the parent proof, and the cited `def-nagata-category` statement. Step 1 introduces the repeated composite `E_r` and uses only the category's composition and identity structure, while checking the source and target objects through the canonical associators. Step 2 verifies the r=1 case from `d_1 = id_T`, identity preservation by `H`, and the given `tau_1 = eta`. Step 3 reads the naturality equation for `eta` at `d_r`, uses the explicitly stated coherence `d_{r+1}^{-1} ∘ T(d_r)=b_r`, and applies preservation of composition to obtain exactly the recurrence for `tau_{r+1}`; the induction hypothesis is used at the final substitution. Step 4 applies ordinary induction on positive integers and generalizes over the arbitrary object `M`. I checked $r=1$, $r=2$ (the formula is $H(b_{1,M})∘η_{TM}∘η_M$), the empty source category (vacuous), and identity functors with arbitrary endomorphism components of $η$ (both sides are its powers). In a one-object category the same calculation is a possibly noncommutative product, so the order of the factors matters and is correct. Naturality is used only for $d_{r,M}$, whose source is $P_rM$; the hypothesis does not need naturality of $τ_r$. No isomorphism hypothesis on $η$ was introduced. All four steps are below 2000 characters and the sole substantive step is the displayed single naturality/coherence calculation, with no hidden sub-lemma. No new node was necessary; the item itself is proved rather than passed to a restated child. Every cited quote in `citations.json` is copied verbatim from `def-nagata-category`.

## What could not be finished

Nothing; no Lean files were written or compiled, as required for stage 1.

## Corrections during verification

The first check found the item outside the required `dag/nodes/<chapter>/` layout; it is now in that layout. The initial citation quotation omitted TeX delimiters; each of the three current quotations now reproduces the cited category definition verbatim. The final reading also corrected proof TeX delimiters and a literal newline escape, and refreshed the search summaries from this sandbox’s actual log. No statement or hypotheses changed.
