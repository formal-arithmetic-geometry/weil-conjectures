# Stage-1 report: lem-sfb-continuous-integral-pivot-splitting

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-continuous-integral-pivot-splitting.json`: preserved the imported statement and split its proof into four steps.
- `dag/nodes/sec-six-functors-basics/lem-sfb-continuous-uniformizer-division.json`: new statement-only auxiliary lemma; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-unit-pivot-schur-formula.json`: new statement-only auxiliary lemma; no Mathlib match.
- `citations.json`: three verbatim node citations for the non-elementary uses.
- `report.md`: this report. The actual msearch records are in `searches.jsonl`.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` and `/home/ubuntu/weil-newtargets-master/WeilConjectures/` for the blueprint id, continuous integral pivot terminology, and likely declaration names. There is no sorry-free declaration of this item. The existing `continuousSMul_integralClosure` declarations concern a different Galois action and are not attachments.

## Sources wanted

None. The cited Hemo–Richarz–Scholbach PDF is present locally and was read at pp. 18–19. No SGA source is used.

## Problems found and corrections

The statement is unchanged. The imported node had no proof. Its parent `lem-sfb-continuous-integral-matrix-local-smith` already cites this item for the pivot step, so I did not duplicate or alter that parent. The item does not assume local constancy of a cokernel; the proof uses only entrywise divisibility and a unit pivot at the chosen point.

The source's valuation comparison supplies the scalar division argument but does not state the exact topological matrix lemma. I therefore made the two strict auxiliary statements explicit: division by a fixed uniformizer power on the valuation ring, and the formula for unit-pivot row/column elimination. Neither auxiliary statement restates the full item: the first is scalar, and the second leaves the pivot as an arbitrary unit and records the actual matrices and Schur complement formula.

## Not duplicates

- `lem-sfb-continuous-uniformizer-division` vs `lem-sfb-continuous-integral-matrix-local-smith`: the former is a scalar homeomorphism and quotient-continuity fact; the latter is a full local Smith form under locally constant cokernel type.
- `lem-sfb-continuous-uniformizer-division` vs `lem-weil-pbc-integral-matrix-entry-properties`: the latter concerns endomorphisms of sheaf modules on schemes and a dominating coefficient; it does not state scalar division on a valuation ring or a topological quotient map.
- `lem-sfb-unit-pivot-schur-formula` vs `lem-weil-pbc-continuous-field-matrix-elimination`: the existing node works over a field with a constant-rank minor and gives a geometric rank factorization; this node is an explicit integral rectangular unit-pivot formula with continuous elementary factors.
- `lem-sfb-unit-pivot-schur-formula` vs Mathlib `Matrix.fromBlocks_eq_of_invertible₁₁`: Mathlib gives an algebraic block identity for fixed matrices with an invertible block, while this statement supplies continuous families, explicit row and column maps, rectangular dimensions and continuous inverses.

Whole-blueprint searches for “continuous integral pivot”, “pivot division”, “unit pivot”, and “Schur complement” found no blueprint node stating either auxiliary lemma; `blueprint.same_as` is therefore empty for both.

## Repair of returned E2/C3/C4

The returned review correctly found that the old auxiliary statement was false: with
$L_0=\operatorname{diag}(a^{-1},1,\ldots)$ and
$(L_1)_{i1}=-a^{-1}K_{i1}$, the order $L_1L_0$ leaves a nonzero entry below the
pivot. For example, over $\mathbb Z_5$ with
$K=\begin{pmatrix}2&4\\6&5\end{pmatrix}$, the old formula gives
$\begin{pmatrix}1&0\\3&-7\end{pmatrix}$ rather than
$\operatorname{diag}(1,-7)$. I repaired the statement to use
$L=L_0L_1$. Direct multiplication gives first row
$(1,a^{-1}K_{1j})$, which $R_0$ clears, and lower rows
$K_{ij}-a^{-1}K_{i1}K_{1j}$ with zero first column. The second reported test,
$K=\begin{pmatrix}2&0\\2&0\end{pmatrix}$ over $\mathbb Z_5$, likewise now gives
$\begin{pmatrix}1&0\\0&0\end{pmatrix}$. I also repaired the item's step 2 to name the
combined factor $L_{\mathrm{pivot}}=L_0L_1$, and step 3 to set
$L=L_{\mathrm{pivot}}$; its citation quote now matches the corrected node verbatim.

## Review by Q147

I read the target node, the chapter `sec-six-functors-basics`, the unit `sk-def-sfb-dc-restricted-functors`, the ancestor proof `lem-sfb-dc-hom-preserves.proof.md`, the parent `lem-sfb-continuous-integral-matrix-local-smith`, and the statements of every node used by the split. I also read Hemo–Richarz–Scholbach, *Constructible sheaves*, Theorem 6.12 and its finite-extension valuation argument on pp. 18–19. The source identifies the valuation ring and compares valuations to keep quotients integral; the explicit matrix formulas below are the agent-written refinement recorded in the node sources.

Step 1 uses the coefficient-extension definition for the valuation ring and uniformizer, and `lem-sfb-continuous-uniformizer-division` for the only non-elementary operation. I checked its hypotheses exactly: the given entries are continuous and lie in `\pi^eA`, so each quotient is a continuous `A`-valued function; the pivot hypothesis says the quotient at `t_0` is a unit; the unit locus is open, so the required open `U` exists and inversion is continuous there. The division lemma itself states the homeomorphism onto `\pi^eA`, uniqueness of the quotient, and the local unit conclusion.

Step 2 uses exactly the statement of `lem-sfb-unit-pivot-schur-formula`. Its hypotheses hold for `q|_U`: `A` is a commutative topological ring, all matrix entries are continuous, the upper-left entry is unit-valued, and its inverse is continuous. The cited statement gives the explicit diagonal factor `L_0`, the first-row factor `R_0`, the first-column factor `L_1`, the combined order `L_{\mathrm{pivot}}=L_0L_1`, the residual formula, their continuous inverses, and the block identity. No proof detail from that node is used beyond its statement.

Step 3 is elementary scalar multiplication and block-matrix rewriting. Multiplying `diag(1,H_0)` by `\pi^e` gives `diag(\pi^e,\pi^eH_0)`; pointwise scalar multiplication preserves continuity. The factor `L=L_{\mathrm{pivot}}` and `R=R_0` are exactly those supplied by Step 2, so their invertibility and inverse continuity are already accounted for.

Step 4 is the rectangular edge-case check. The item assumes `m,n\ge1`; when one is one, the reduced matrix has zero rows or zero columns, and the displayed formulas have no entries in the corresponding empty index set. I also checked `e=0`, a one-point `T`, an empty `T`, and the scalar matrix `G=(\pi^e u)`: the construction gives the expected unit normalization and an empty residual block. No local constancy of a cokernel is introduced.

The new statements were tested on `e=0`, `e=1`, scalar `1\times1`, one-row and one-column rectangular matrices, zero residual blocks, constant and varying unit pivots, and the case where all entries equal `\pi^e` times continuous functions. The division statement fails without the divisibility hypothesis, and the pivot formula fails without a unit pivot, so both hypotheses are necessary. Every proof step is below 2000 characters and contains its concrete algebraic operation; no hidden sublemma is left in a long step. `proof_deps` is exactly the union of the cited nodes, the dependency graph has no cycle, and no SGA citation occurs.

## Unfinished work

No mathematical part of this one-level split remains. The two auxiliary nodes are intentionally statement-only stage-1 leaves for later workers.
