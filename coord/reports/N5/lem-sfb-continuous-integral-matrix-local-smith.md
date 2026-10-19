# N5 stage-1 report

Item: `lem-sfb-continuous-integral-matrix-local-smith`. Group N5. Stage 1 only, 2026-10-17.

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-continuous-integral-matrix-local-smith.json`: existing statement split into four proof steps; no new nodes and no Mathlib leaves.
- `citations.json`: three verbatim citations of the existing scalar Smith statement, one for each step that uses it.
- `report.md`: this report.

## Attachments

None. I searched the slopmaster2 source for the exact blueprint tag and for continuous integral Smith terminology; no declaration states this result. The source declaration `PadicAlgCl.exists_isOpen_eq_mul` concerns continuous field-valued matrices and constant rank, and does not state the integral local Smith theorem with torsion exponents.

## WANTED

None. The Hemo–Richarz–Scholbach paper and the Stacks source are available locally.

## What needed correction

The imported node was statement-only and had no proof. Its statement is retained exactly. The proof must preserve torsion exponents, so a field-rank argument alone is insufficient; the scalar cokernel isomorphism class determines all invariant exponents. The existing DAG Smith node is used only for the scalar diagonalization of the image submodule.

## Not duplicates

- `lem-sfb-continuous-integral-matrix-local-smith` vs `lem-sc-dvr-saturation-line-smith-normal-form`: the existing Mathlib leaf is a pointwise submodule diagonalization over a DVR, while this item proves continuous local row and column matrices for a varying family with locally constant cokernel type.
- `lem-sfb-continuous-integral-matrix-local-smith` vs `lem-weil-pbc-continuous-field-matrix-elimination`: the existing node works over a field and retains only rank; this item works integrally and retains torsion invariant factors.
- `lem-sfb-continuous-integral-matrix-local-smith` vs `lem-weil-pbc-continuous-field-presentation-normal-form`: that node gives a field block normal form for sheaf maps, with no integral diagonal powers or continuous integral inverses.
- `lem-sfb-continuous-integral-matrix-local-smith` vs `lem-weil-pbc-integral-matrix-analytic-cover`: that node chooses a dominating pivot under a rational local-freeness hypothesis and gives no fixed Smith diagonal or continuous integral basis changes.
- `lem-sfb-continuous-integral-matrix-local-smith` vs `lem-weil-pbc-integral-matrix-pivot-cover`: that node is a one-pivot sheaf block decomposition and does not normalize to a scalar power or recurse to a full diagonal.
- `lem-sfb-continuous-integral-matrix-local-smith` vs `lem-weil-pbc-integral-lfp-local-torsion-charts`: that node concerns sheaf torsion charts and finite quotients, with no continuous matrix-basis assertion.

## Review by N5

I read the current item node, its chapter `sec-six-functors-basics`, its unit `sk-def-sfb-dc-restricted-functors`, the ancestor `lem-sfb-dc-hom-preserves`, and the full delivery-errors checklist B–E. I also read the existing Smith leaf statement and checked that it says exactly the scalar diagonalization used in Step 1, rather than merely defining Smith form. Step 1 applies that statement to the image submodule, adds a kernel basis, and computes the residue-field dimensions that recover the free rank and all positive exponents from the cokernel isomorphism class. Step 2 checks the minimal pivot, the open valuation-e locus, continuous integral division, and the explicit elementary row and column operations; the Smith citation supplies the fixed invariant-factor bound used there. Step 3 verifies the residual block has the remaining invariant list and that induction gives finite products of continuous invertible matrices with continuous inverses. Step 4 records the open-cover construction and zero-size, zero-rank, unit, one-point, and mixed torsion/free edge cases.

I ran and read the required Mathlib searches for this item: LeanFinder and LeanSearch return scalar Smith declarations, while Loogle and source grep return only scalar Smith or generic continuous matrix APIs; none states a continuous integral local Smith theorem. The exact queries and verdicts are recorded in the inherited node's `mathlib_searches`. I checked HRS Example 3.1 and the finite-E continuous integral pivot/division argument in Theorem 6.12(2), and wrote the local constant-type induction explicitly. No SGA source, hidden hypothesis, or statement weakening was introduced.

## Unfinished work

None. The item is split with no new unsplit nodes.

## Second reading by N5

- Item statement: checked against HRS Example 3.1 and the finite-E discussion in Theorem 6.12(2), with the local Smith assertion identified as the agent-written variant stated in the node; all hypotheses, rectangular edge cases, and the valuation-topology setting agree.
- Step 1: checked against the existing scalar Smith leaf and the DVR diagonal cokernel calculation; repaired the explanation so the image lifts and kernel basis give a domain basis, and the residue-field dimensions explicitly recover the free rank and every exponent.
- Step 2: checked the open valuation-e locus, divisibility after pointwise Smith equivalence, continuous division, elementary clearing, and the residual cokernel decomposition; made the divisibility and residual-type arguments explicit.
- Step 3: checked the induction parameter and the extension/composition of basis changes; stated the induction predicate and the smaller residual block explicitly.
- Step 4: checked the empty, zero-size, one-point, unit, and mixed free/torsion cases; the edge-case step is elementary.
- New nodes: none; the only dependency is the existing scalar Smith Mathlib leaf, and no duplicate or Mathlib statement was introduced.
- Metadata and searches: checked the inherited `created` record as history of the existing item node (not a new node), verified all recorded LeanFinder/Loogle/grep/LeanSearch searches, and kept citations.json as exact verbatim statements of the cited leaf.

Changes made: expanded Steps 1–3 to supply the image-lift, invariant-factor, divisibility, residual-cokernel, and induction details that the first reading found implicit; no statement or dependency was changed.
