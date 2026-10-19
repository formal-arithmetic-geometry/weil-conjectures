# Q53: lem-rp-even-tensor-positivity

## Files written

- `dag/nodes/sec-purity-real-sheaves/lem-rp-even-tensor-positivity.json`: statement, split into four steps; Mathlib searches found no declaration stating both clauses for all tensor powers on the stated schemes.
- `citations.json`: six verbatim statement excerpts, one for every proof citation.
- No new nodes and no new Mathlib leaves. The imported item is the only DAG file changed.

## Attachments

None. I searched the project source by the blueprint id and by even-tensor/positivity notions. `AlgebraicGeometry.WeilGroup.IsReal.hasNonnegCoeffs_eulerFactor_tprod_self`, `WeilConjectures/EtaleCohomology/Purity/RealSheaves/Rankin.lean:259`, proves positivity for a tensor square in the curve representation setting, with substitution by the degree of the point. Its docstring explicitly distinguishes that result from all even powers. `IsReal.tprod` at line 133 supplies tensor reality in the same setting. Neither states this item's two clauses on arbitrary separated finite-type schemes. I therefore make no attachment claim. The upstream master's sorry declarations were not treated as completed proofs.

## WANTED

None. The current blueprint statement and separate proof are available, as are Milne's lectures for the formal trace–determinant identity.

## Corrections and decisions

The imported statement is correct; it has not been weakened or otherwise changed. I added `def-wf-iota-real` to `stmt_deps`, since the hypothesis already uses that notion. I replaced the single long imported proof paragraph with four short steps. The non-elementary formal trace–determinant identity is already stated by `lem-weil-exp-trace-determinant`, so it is now cited rather than called elementary. The last coefficient argument follows directly from the existing explicit coefficient formula in `def-weil-power-series-exponential`, and does not merit a new positivity node.

I searched the whole DAG and blueprint for tensor positivity, determinant/exponential identities, and spectra. The only blueprint node matching even tensor positivity is this item. The existing linear algebra spectrum and triangularization nodes and the existing trace–determinant node suffice. No new-node duplicate or Stacks-tag comparison is needed; this proof is finite-dimensional linear algebra and formal power series, not a Stacks or SGA route.

The Mathlib queries in the node are copied from `searches.jsonl`: two semantic phrasings, Loogle, grep, and LeanSearch. I read all returned hits. `FDRep.char_tensor` concerns a tensor character, `Even.zpow_nonneg` concerns even powers in ordered fields, and the remaining hits concern unrelated norms, characters, or elliptic curves. None states the item or gives it by a one-line specialization. The project-specific coefficient-positivity theorem mentioned in Rankin.lean is outside Mathlib and does not finish this item.

## Unfinished work

None for the one-level split. The pre-existing unsplit inputs remain their own DAG items.

## Review by Q53

I read `coord/brief-stage1.md`, `stages/1-dag.md`, the three-level rule in `SETUP.md`, `coord/delivery-errors.md` B–E in full, `GOAL.md`, and `coord/dag-sync.md`. I read the chapter and Rankin–Selberg unit records and the main-20261015 statement, its separate proof, and the unit's proof. The argument stays exactly on that unit's local-factor route. The item is not the unit's key statement, so its already realized unit record needs no change. No Lean was written or compiled and no shared file or launcher was modified.

For step 1 I opened the statements of `def-real-weil-representation-operations`, `def-wf-iota-real`, and `p-linear-spectra`. The first gives the action on a pure tensor; the second explicitly identifies reality with conjugation stability of the local eigenvalue multiset and gives the determinant product; the third gives the eigenvalue multiset of a tensor product with multiplicity. Iteration is stated with its base and step. Conjugating the resulting finite product fixes every coefficient, which proves the real-polynomial clause. The argument works on the stalk at an arbitrary fixed closed point. I did not invoke the curve-only global sheaf–representation equivalence or `p-real-operations`, whose curve hypothesis would be unjustified here.

For step 2 I opened `p-linear-triangular`: it supplies an invariant full flag with one-dimensional quotients. I use it only over the algebraically closed field C and only in finite dimension. The determinant, trace, and power calculations in an adapted upper triangular basis are written out. Applying iota entrywise to the matrix is legitimate without any topology: determinants and tensor entries are finite sums and products. Finite distributivity gives the power-sum identity; the same conjugation permutation from step 1 makes the sum real, and an even power is a square. No diagonalizability or semisimplicity is assumed.

For step 3 I opened `lem-weil-exp-trace-determinant` and read Milne, Lectures on Etale Cohomology, Lemma 27.5, pp. 155–156, including its triangular-matrix proof. The node's statement gives exactly the inverse determinant/formal exponential identity used here. Its hypotheses hold for the complex finite-dimensional endomorphism constructed in step 2. Constant term one makes the inverse unique. Applying iota to the inverse identity identifies the original local factor after iota with that inverse; this avoids any unproved analytic continuity or exchange of infinite sums. This node is declared as a generic off-unit tool in `split_report.tool_uses`; it supplies the very identity the unit already uses, with no change to its route.

For step 4 I opened the complete statement of `def-weil-power-series-exponential`. It gives both the displayed coefficient formula and the constant coefficient one. Since all indices in that formula are positive, there are finitely many compositions of each fixed N, and all their terms are nonnegative. This is a direct elementary specialization of the definition, not a separate hidden lemma.

I checked zero-rank stalks (empty determinant product, inverse 1), k=1 (only reality is claimed), k=2 (squares of real power sums), and nonsemisimple matrices (upper triangular powers suffice). Rank-one eigenvalue -1 gives `(1-t)^(-1)` for even k and `(1+t)^(-1)` for k odd, confirming that positivity needs the even condition. Conjugate nonreal pairs have real power sums and their even powers remain nonnegative; no individual eigenvalue is required to be real or positive. Empty schemes have no closed point and the assertion is vacuous. All four steps are below 2000 characters. I checked B1–B10 and D1–D5: no new node, no restated clause, no circular citation, no unsupported attachment or invented search. For C1/C4 I checked the full cited statements above and generated exact excerpts directly from them; C3 uses no cited proof internals. For E1–E7 I checked field characteristic, finite dimension, parity, local objects, and the explicit determinant/trace computations. There is no statement dispute or changed coefficient category.

The first dry run flagged the TeX row separator in the step-4 subscript as doubled backslashes. I rewrote the index conditions on one line and corrected the two Lean source line references after checking them.
