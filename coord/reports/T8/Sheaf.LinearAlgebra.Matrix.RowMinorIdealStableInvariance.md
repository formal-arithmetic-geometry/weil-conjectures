## What changed

Proved Matrix.rowMinorIdeal_stable_invariance in
Sheaf.LinearAlgebra.Matrix.RowMinorIdealStableInvariance. The public statement,
rowMinorIdeal definition, and DAG route are unchanged. Added proved private
helpers for minor generators, the finite-matrix supremum, the two stabilization
inclusions, the cutoff case, and coordinate-change inclusion.

The proof selects rows for the finite-matrix supremum. For stabilization it
appends zero columns and standard basis rows, identifies a selected minor with
an old minor and identity block through finSumFinEquiv, and applies
Matrix.det_fromBlocks_zero₁₂. Projection gives the converse via
Matrix.minorIdeal_inclusions clause (2). When n ≤ k < n+d, increasing standard
rows in the last coordinates produce a unit minor. For automorphisms, write
the inverse-image row matrix as B and the coordinate matrix as C, verify
A = B*C using pi_eq_sum_univ', apply clause (3), and repeat with the inverse.

Removed the unused public import Mathlib.LinearAlgebra.FreeModule.Basic;
record: coord/changes/T8-row-minor-unused-import.md. The existing private proof
import MinorIdealInclusions is used. No other module is edited.

Validation: lcompile.py compiled all three clauses together without errors or
warnings. Empty ranks, d=0, n≤k, the crossing n≤k<n+d, arbitrary submodules,
and the zero ring are included; no extra hypotheses or nonempty assumptions.
The sources read were Stacks more-algebra.tex, lemma-fitting-ideal (07Z8),
including its use of lemma-ideals-generated-by-minors (07Z7), and the existing
DAG dependencies and their Lean signatures. Mathlib and library searches found
no direct replacement theorem. The unit route is retained.

## Proved and sorry left

Closed 1 of 1 original holes: Matrix.rowMinorIdeal_stable_invariance
(node lem-trf-row-minor-ideal-stable-invariance).
Added 0 holes; split off 0 statements. No sorry remains in this module, and
all new private helpers are proved. The proof uses the existing theorem
Matrix.minorIdeal_inclusions (node lem-trf-fitting-ideal-minor-inclusions),
whose existing sorry is unchanged and not part of this delivery.

## No longer needed

Removed import Mathlib.LinearAlgebra.FreeModule.Basic; no free-module basis
or finite-generation instance is used. All original DAG proof dependencies
remain used: the minor-ideal and determinant definitions, the block triangular
determinant formula, and minor-ideal inclusions. No DAG node or project module
is pruned or withdrawn. No new dependency import is needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy. The stage-2 review already identified
FreeModule.Basic as redundant. The apparent finite-index bookkeeping in
stabilization is handled with Fin.append and finSumFinEquiv, without changing
any definition or statement. No new nodes or forced adaptations.

## Second reading by T8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
