## Worker report

Files written:

- `dag/nodes/sec-six-functors-basics/lem-sfb-padic-minpoly-root-product.json`: item, statement unchanged, split into four steps (2093 characters total).
- `dag/nodes/sec-six-functors-basics/lem-sfb-algebraic-absolute-value-unique.json`: statement, Mathlib leaf `spectralNorm_unique_field_norm_ext`, SpectralNorm.lean:770–773.
- `citations.json`: every step/node citation with a verbatim statement quote.

Attachments: none. Searches in `lean/WeilConjectures/` for the blueprint tag, minpoly/root/norm and conjugate absolute values found no project declaration stating the item. The Padics/Extension.lean result concerns finding a simple finite subextension, not this identity.

WANTED: none. The source for the item is obtained: Milne, *Abelian Varieties*, Chapter I, proof of Lemma 10.21, printed p.51. The new leaf is read directly in the installed Mathlib source.

The imported item has a correct statement and no proof. The absolute value in Milne is the nonarchimedean one, not the complex absolute value used elsewhere in the blueprint. The proof now exposes the conjugacy and valuation-invariance inputs instead of citing a resultant formula. The nearest-blueprint-ancestor command prints `None`; the item's existing `blueprint.from.node` is null. That inherited value and the complete `via` chain were retained; the new node uses the exact ancestor output. Read the current `literature/blueprint/latest/` unit and direct-image key node; the arithmetic prerequisite serves direct-image clause (3) through the recorded alteration and level-rigidity chain. No unit route was replaced.

Nothing remains unfinished in this one-level split. No Lean files, compilers or builds were used.

## Searches and non-duplication

All Mathlib searches were made through msearch.py and are in searches.jsonl. The item's previous searches were retained; the current searches supply independently logged evidence in this sandbox. The first semantic search found spectralNorm's root norm/product lemmas and algebraic norm identities; a second phrasing about polynomial values at conjugates found the root norm equality, not the whole identity. A product involving an independently given H needs the written double-product argument; it is not a one-line specialization of those hits.

For the new leaf, leanfinder, loogle, leansearch and grep all found `spectralNorm_unique_field_norm_ext`. Read its full signature and section hypotheses at SpectralNorm.lean:683–699 and 767–785. Applying it separately to u and v gives their pointwise equality. The conversion between a nonnegative-real-valued absolute value and Mathlib's real-valued AbsoluteValue is only the codomain inclusion/restriction, with no comparison theorem required.

Searched the entire DAG for uniqueness of absolute values and for the declaration name; opened every candidate that could cover the fact: the finite-extension uniqueness/completeness nodes, normed-coefficient-realization and integral-coefficient-ext-comparison. Searched the blueprint index for `minimal polynomial`, `conjugate`, `absolute value`, and `unique`. No blueprint statement asserts the new leaf. This is a general norm-extension theorem, not a clause of the item's polynomial identity, and it is already a Mathlib leaf; it is not left as a new unsplit lemma.

## Not duplicates

lem-sfb-algebraic-absolute-value-unique vs lem-weil-l-adic-extension-absolute-value: the existing node gives existence, uniqueness and the ultrametric inequality for a finite extension of Q_ell. The new leaf gives uniqueness for arbitrary algebraic extensions of any complete nontrivially nonarchimedean valued field; its application here is directly to the infinite algebraic closure, which the existing node does not cover.

lem-sfb-algebraic-absolute-value-unique vs lem-trf-spectral-norm-algebraic-extension: the existing node constructs the spectral norm and states its norm/vector-space properties, but its statement does not assert uniqueness of an arbitrary given extending absolute value. The new leaf supplies precisely that missing comparison.

lem-sfb-algebraic-absolute-value-unique vs lem-sfb-normed-coefficient-realization: the existing result compares finite coefficient presentations and their derived module categories, and does not state uniqueness on an arbitrary algebraic extension.

lem-sfb-algebraic-absolute-value-unique vs lem-integral-coefficient-ext-comparison: that statement is an equivalence of integral coefficient module categories, not uniqueness of extending absolute values.

## Review by Q22

I read Milne I Lemma 10.21's proof on printed p.51, including the conjugate factorization, permutation of roots, valuation-invariance sentence and both resulting displayed formulas. Its argument applies separately to H, and the item's monicity accounts for the absence of a leading coefficient. I retained its hypotheses exactly and did not assume H is separable. I read the current chapter/unit material and the latest blueprint direct-image statement to check that this auxiliary arithmetic argument does not substitute a new route.

Step 1 cites the actual minimal-polynomial definition, whose statement makes it monic, and the existing algebraically-closed linear-factorization lemma, whose statement gives a polynomial as its leading coefficient times a finite product. Both f and H are nonzero because they are monic. Their degrees count those factors. The roots c_i in the statement can be listed with their given multiplicities, and repeated roots are permitted. I did not take separability or distinctness from this citation.

Step 2 cites the algebraic-closure definition for algebraicity, the same factorization statement for splitting of each nonzero minimal polynomial, and the normal-extension-conjugate-by-automorphism lemma. I opened that node and checked that its statement gives an automorphism carrying alpha to any beta with f(beta)=0, exactly what is needed for each alpha_j. Algebraic closure implies its normality hypothesis by the cited factorization. No finite-degree hypothesis is needed. Its Stacks source is Fields Tag 0BME (lemma-lift-maps), with the root-embedding construction in Tag 09HQ (lemma-characterize-normal); I read both source passages and the tags table. This reuses the node rather than inventing a new conjugacy lemma.

Step 3 uses the l-adic-number definition's completeness, nonarchimedean property and formula for |ell|, and the new leaf's uniqueness statement. Pulling the supplied absolute value back by a field automorphism preserves all the absolute-value axioms and its restriction to K. The explicit verification is in the step. Thus both values meet the leaf's hypotheses on the algebraic extension Omega/K. The coefficient sum explicitly proves H(sigma(alpha))=sigma(H(alpha)); no unproved transport comparison is hidden here. I read the full Mathlib uniqueness theorem and all its ambient hypotheses; it requires completeness of K, not Omega. I avoided citing the existing finite-extension uniqueness statement as if it covered Omega.

Step 4 is the finite commutative product calculation written in full. Reversing c_i-alpha_j contributes (-1)^(rm), which disappears only after taking absolute values. This corrects the possible sign ambiguity in identifying a resultant with evaluation without absolute values. Multiplicativity replaces each conjugate value by the value from step 3. There is no division by H(alpha) or any root difference. I checked r=0 (H=1, both sides 1), alpha in K (m=1), H having repeated roots, and H(alpha)=0 (both sides zero). No extra nonvanishing assumption was introduced.

I checked delivery-errors B–E: the sole new node is self-contained and statement-only, its Mathlib match gives the declaration and lines actually read, all notation is written in TeX, the new fact is neither elementary nor a restated clause, and all non-elementary proof inputs have statement citations. The proof dependency list is exactly the union of uses and citations.json quotes the statements verbatim. Every step is below 2000 characters; the complete assembly is below 3000. No step cites the proof of another node, no SGA reference is used, and no new unsplit subclaim or circular dependency is introduced.
