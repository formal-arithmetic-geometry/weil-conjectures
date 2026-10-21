## What changed

Restored the quarantined module `lean/Sheaf/CategoryTheory/CartanEilenbergHorizontalCutComparison.lean` with its complete Cartan–Eilenberg horizontal-cut comparison proof. The proof constructs the truncated-total inclusion, obtains the mapped-total isomorphism, applies the existing good-cut identification, and verifies the degree-zero component formula including the total-flip sign. The module is byte-for-byte identical to its quarantined source and compiles in the J1 sandbox.

## Proved and sorry left

Closed the sole target declaration hole: `CategoryTheory.cartanEilenberg_horizontal_cut_comparison`.
No `sorry`s remain in the delivered module, and no new holes were added. The theorem depends on existing declarations whose own modules may still contain their independent proof obligations.

## No longer needed

None. The two proof dependencies named by the DAG, `lem-sp-cartan-eilenberg-mapped-total` and `lem-sp-ce-good-cut-identification`, are both used. All imports in the restored module are retained because they provide the public signature or proof constructions.

## Where the brief, the DAG or earlier work was wrong

The module had been quarantined by the merge queue after a cluster restore, while its source and complete proof remained available under `quarantine/`. No mathematical or statement correction was needed; restoring that source closes the assigned item.

## New nodes

None.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
