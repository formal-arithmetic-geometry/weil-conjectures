## What changed

Retired `Sheaf.AlgebraicGeometry.Modules.ExteriorSheafRankWedgeZero` by listing
its path in `deleted.txt`; the adopted upstream twin
`WeilConjectures.AlgebraicGeometry.Modules.ExteriorSheafRankWedgeZero` supplies
the fully proved rank-vanishing theorem. Adapted the three direct consumers while
preserving every public signature. `DeterminantSplitLinearMaps` and
`DeterminantWedgeQuotientFactor` now import the proved
`ExteriorSheafPowerComparison` API and use private helpers transporting the
upstream wedge result to `exteriorSheafSection`. `DeterminantSplitLinearBijective`
drops its unused rank-module import without replacement. Updated the three
copied DAG nodes to record the retirement route and upstream attachment.

Repair of return C-a64b1 (head a64b195c89): corrected the rank node
`lean.statement` to quote the upstream `wedge` conclusion verbatim; removed the
unused upstream rank import from `DeterminantSplitLinearBijective`; removed the
duplicate comparison import from `DeterminantWedgeQuotientFactor`. Rebased the
retained packet onto the current chart-comparison and tensor-quotient migrations,
preserving their imports, calls, proof rewrites, and node dependency updates.

Validation: `lcompile.py --all` compiled all three repaired consumer modules
without errors or warnings. Static checks confirm the rank node quotes the
upstream declaration verbatim, all delivered Lean files have zero holes,
imports have no duplicate entries, and Lean lines stay within 100 characters.

Change record: `coord/changes/retire-exterior-sheaf-rank-wedge-zero-v2.md`.

## Forced adaptations

The three consumer adaptations are forced by deletion of the imported Sheaf module.
Against the changed dependency set, the original `DeterminantSplitLinearMaps` and
`DeterminantWedgeQuotientFactor` fail at their rank-vanishing calls because
`exteriorSheaf_rank_wedge_eq_zero` is unavailable from the removed Sheaf import;
the changed lines replace that import with the upstream theorem plus
`ExteriorSheafPowerComparison`, and add a private transport helper. The original
`DeterminantSplitLinearBijective` fails to resolve the removed Sheaf import; its
changed import line is removed without replacement, as requested by reviewer
C-a64b1. Public signatures and all unrelated proof lines are unchanged.

## Proved and sorry left

This is a zero-hole retirement repair. Closed: 0 of 0 sorries in the retired
module (it already had a complete proof). Added: none. Split off: none. No
`sorry` remains in any delivered module; the two compatibility helpers and all
three adapted consumer proofs are complete.

## No longer needed

Removed the Sheaf rank-wedge module and all three imports of that module. The
upstream rank theorem and the existing comparison module replace the old import
closure in the two consumers that use rank vanishing. The unused upstream rank
import in `DeterminantSplitLinearBijective` and the duplicate
`ExteriorSheafPowerComparison` import in `DeterminantWedgeQuotientFactor` are removed. No mathematical unit step or dependency is pruned: the rank-vanishing
node remains reached and is attached to the upstream theorem, while the two
consumer proof routes still use it through the compatibility helper.

## Where the brief, the DAG or earlier work was wrong

The current assignment is the explicit retirement row in `coord/retire-items.tsv`,
not a request to reprove the already completed Sheaf theorem. The upstream twin
is API-different (`wedge` over `exteriorPower`), so direct import replacement
would not typecheck against the existing consumer statements. The private
transport helpers are required and are proved from `exteriorSheafPowerIso`; no
statement, upstream source file, or target is changed.

## New nodes

None.

## Second reading by V2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
