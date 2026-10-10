# lem-weil-pbc-smooth-fibre-regular-local

## Worker report

Files written:

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-smooth-fibre-regular-local.json`: split the item into two steps, smooth base change and regularity of the local rings of the resulting smooth algebra over a field.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-smooth-over-field-regular-local.json`: new statement node for the final assertion of Stacks Algebra 00TT; all three required Mathlib searches found no match, so it is statement-only and unsplit.

Attachments: none.

WANTED: none.

The item's source cited line 41349 for Stacks 00TT, but the checked `algebra.tex` has `lemma-characterize-smooth-over-field` at line 38609; the source and proof citations now use the checked line. The earlier dependency `lem-weil-pbc-smooth-over-field-dimension-differentials` states only the dimension equality from 00TT and cannot justify regularity, as the existing lead note observes. The new support node records exactly the missing final assertion, strictly smaller than the item because it does not include formation or smoothness of fibres.

Nothing remains unfinished in this one-level split. No Lean was written or compiled.

## Review by E1

I read Stacks `algebra.tex`, Lemma 00T4 (`lemma-base-change-smooth`, line 37133) and Lemma 00TT (`lemma-characterize-smooth-over-field`, line 38609), including the latter's hypotheses and final assertion. The item statement agrees with their composite: 00T4 permits the arbitrary base change $R\to\kappa(\mathfrak p)$, and 00TT applies because a smooth algebra is of finite presentation, hence finite type, and is smooth at every prime.

Step 1 uses `lem-weil-pbc-smooth-ring-map-base-change-composition`, whose clause (1) says exactly that $R'\to R'\otimes_RS$ is smooth for any $R\to R'`; `def-weil-pbc-localization-at-prime` supplies the residue field and fibre ring. The only identification is notation. Step 2 uses the full statement of the new 00TT node: for a smooth algebra over a field, every prime localization is regular local. The substitution $k=\kappa(\mathfrak p)$ and $A=S\otimes_Rk$ is elementary. Neither step is marked elementary because each invokes a substantive lemma.

The new node is self-contained, introduces $k,A,\mathfrak q$, and cites the definitions of smoothness, prime localization, and regular local ring. It contains no proof or proof dependencies while unsplit. Its source is the exact Stacks tag and label. I searched the current DAG by tag, label, title, and the phrases “smooth algebra over a field” and “regular local”; the existing 00TT node gives only the dimension equality and no other node states the final regular-local assertion. LeanSearch, Loogle, and a Mathlib source grep found separate smooth and regular-local APIs but no connecting theorem.

For the hypotheses, Step 1 uses an arbitrary ring map to the residue field, exactly as 00T4 allows. Step 2 uses that a field is the base and that global smoothness entails finite type and smoothness at each prime, exactly the hypotheses of 00TT. The zero ring causes no problem: it has no primes, so the local assertion is vacuous. For a polynomial algebra $k[x_1,\ldots,x_n]$, the conclusion specializes to the familiar regularity of all prime localizations, providing a basic consistency check.

I corrected the source line and required the regular-local clause to be separated from the existing dimension-only node. No further changes were sent back after that correction.
