# Worker report: field injective matrix nonzero maximal minor

Files written:
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-field-injective-matrix-nonzero-maximal-minor.json`: item split, four proof steps; no direct Mathlib match found.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-injective-coordinate-linear-map-retraction.json`: statement, Mathlib leaf specializing `LinearMap.exists_leftInverse_of_injective` to coordinate spaces.

Attachments: none.

WANTED: none. Sources used are available: Stacks source at `/tmp/stacks-project/algebra.tex`, tags/tags; pinned Mathlib source read remotely without saving or building.

Corrections and provenance:
- The original statement had doubled TeX backslashes; corrected escaping and added the coordinate definition of $K^r$ and matrix-vector multiplication. Mathematical assertion unchanged.
- Original source Stacks 00MY (`lemma-exact-depth-zero-local`) and 00MW (`lemma-trivial-case-exact`) implies the assertion by splitting a two-term complex over a field. It is not used as a proof dependency because the depth-zero parent already uses this field lemma. The proof is explicitly agent-written: linear retraction, coordinate calculation of its matrix, Cauchy–Binet, nonzero summand. This is below the unit level and retains the field-minor step.
- Read Stacks 0F0K (`item-cauchy-binet`, algebra.tex lines 282–288). Its hypothesis is only a ring and conformable rectangular matrices; it applies even when n > p. Read existing `lem-weil-pbc-cauchy-binet` statement; step 3 uses its conclusion, including the increasing-order row subsets, rather than its proof.
- Mathlib source provenance: `/home/ubuntu/weil-src-slopmaster2/lake-manifest.json` pins mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`. Advertised local .lake checkout is absent; `/tmp/mathlib-f1` is sparse and lacks LinearAlgebra. Read official raw source at that revision, streamed to `rg`. `Basis/VectorSpace.lean` lines 40–42 have DivisionRing/module hypotheses; lines 240–241 state the linear left inverse theorem. LeanSearch and Loogle calls independently returned the same type. This is honestly recorded in searches, without claiming a local grep ran on an absent checkout. Item searches were also rerun with LeanSearch, LeanFinder, and streamed pinned Matrix/Rank.lean grep; prior broad source searches retained.
- Whole-blueprint search (`tools/blueprint_refs.py search 'left inverse'` and `'maximal minor'`) and DAG grep found no existing coordinate-linear retraction node. The existing split-extension-free-presentation node mentions the same declaration only in search discussion and has a different statement. New leaf metadata inherits the ancestor `thm-weil-pbc-finite-etale-lifting`, with this item prepended to via.

Edge checks:
- n = 0, arbitrary p: empty minor determinant 1; coordinate retraction and Cauchy–Binet include the zero space.
- n > p: Cauchy–Binet sum is empty, contradicting 1 != 0, so the hypothesis cannot hold.
- n = p = 1: retraction gives c*b = 1, so b is nonzero.
- No restriction on characteristic, and no claim that injectivity survives tensoring is used.

Checks: `tools/review_split.py` PASS, one new node; flags statement changed because escaping/inline coordinate definitions were repaired. `tools/check_dag.py`: zero cycles, zero self-loops; seven pre-existing unrelated unreachable warnings (constructible finite-pushforward approximation/noetherian, constructible approximation, finite cover killing, finite stage killing, prime torsion devissage, pushout monicity). No own-file issue.

Unfinished: none in the assigned split. Lead review is pending.

## Review by M1

I read Algebra 00MY/00MW for the original field-complex assertion and 0F0K for the rectangular Cauchy-Binet formula. I compared the item statement with those assertions and read the existing Cauchy-Binet, matrix, submatrix, determinant and field node statements used by the proof. The new retraction node states a strictly smaller vector-space fact, with all objects introduced; its pinned Mathlib declaration `LinearMap.exists_leftInverse_of_injective` was checked at `Basis/VectorSpace.lean:240-241` at the recorded revision. The whole-blueprint and DAG searches found no node with this statement. Its three search kinds, source, `created.item`, and blueprint ancestry are present; the one-line specialization to `Fin n -> K` and `Fin p -> K` is valid.

Step 1 applies only that retraction statement to the injective matrix map. Step 2 computes the coordinate matrix of the retraction and every entry of `CB`; no rank assertion is hidden. Step 3 uses the exact Cauchy-Binet statement on `n x p` and `p x n` matrices and the determinant definition for `det I_n=1`. Step 4 uses `1 != 0` in the field and the finite-sum formula to select a nonzero summand, then the subset cardinality to infer `n <= p`. The elementary labels attach only to coordinate and finite-sum calculations. I tested `n=0`, `n>p` (empty sum contradiction), and `n=p=1`. The worker corrected TeX escaping and made coordinates explicit; no mathematical hypothesis or conclusion changed. No further correction was requested. I checked delivery-errors A-F, including the cited statements, duplicate search, Mathlib line, and zero cycles.

## Follow-up source Lean audit (2026-10-10)

Read-only audit of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`: exact-id searches for both `lem-weil-pbc-field-injective-matrix-nonzero-maximal-minor` and `lem-weil-pbc-injective-coordinate-linear-map-retraction`, including the literal `(blueprint: lem-weil-pbc-field-injective-matrix-nonzero-maximal-minor)`, returned no match. Concept searches for nonzero/nonvanishing/maximal minors, injectivity, and retractions found the following nearby declarations, whose source statements were read:

- `Matrix.exists_submatrix_det_ne_zero_of_le_rank`, `WeilConjectures/Mathlib/LinearAlgebra/Matrix/Rank.lean:54–62`: hypothesis `r ≤ A.rank`, conclusion arbitrary maps `e₁ : Fin r → m`, `e₂ : Fin r → n` with nonzero submatrix determinant. The compressed committed sorry map has `s=false`, `ts=false`; its recorded dependency `Matrix.exists_linearIndependent_col_of_le_rank` also has `s=false`, `ts=false`. It is closed, but does not state the item exactly: the item's hypothesis is injectivity; its conclusion uses all columns, an increasing-order row subset, and includes n ≤ p. Applying this theorem requires the rank implication and extracting/reordering the chosen row/column indices. It was already honestly recorded as a source-repository candidate in the item's original search list.
- `linearIndependent_iff_exists_det_ne_zero`, `WeilConjectures/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean:70–89`, and `LinearIndependent.exists_det_ne_zero`, lines 91–97: linearly independent families of functions have a nonzero square evaluation matrix, with arbitrary coordinate map. Both are closed (`s=false`, `ts=false`); the private auxiliary `exists_det_ne_zero_fin`, lines 35–68, is likewise closed. These are closer candidates but still omit the increasing-order row subset and inequality and take linear independence rather than the item's injectivity. No exact declaration was found.
- `LinearMap.exists_leftInverse_of_injective` occurs as a Mathlib theorem used in source files `EtaleCohomology/Purity/RealSheaves/LocalSystems.lean:207`, `AlgebraicGeometry/Cohomology/DualityPairing.lean:86`, and `RingTheory/GenericIrreducibility.lean:623`; none declares the retraction node's own coordinate-specialized statement. No source-repository wrapper or blueprint annotation for that node was found. The existing new node is a Mathlib specialization, not an unrecognized source-repository Lean declaration. The project sorry map contains no `LinearMap.exists_leftInverse_of_injective` entry because it maps project declarations, so it cannot be used to claim a transitive audit of this imported Mathlib theorem; its verified pinned Mathlib match remains the appropriate evidence.

Outcome: no exact source-project attachment found for either node, so no node changes were made in this follow-up. Only this worker report was amended. The isolated `/home/ubuntu/m1-matrix-minor` delivery worktree and source checkout were not changed; nothing was compiled.
