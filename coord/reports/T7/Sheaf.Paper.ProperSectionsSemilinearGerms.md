## What changed

Proved `WeilConjectures.ProperSemilinearGerms.movingPoint_properties` and the
private naturality lemmas `integralCounit_natural`, `integralUnit_inv_natural`, and
`integralGerm_natural` in `lean/Sheaf/Paper/ProperSectionsSemilinearGerms.lean`.
The proof uses the existing category-theoretic whiskering and naturality APIs; it
adds only the proof import `Mathlib.CategoryTheory.Whiskering`, with fully
qualified helper references. Public signatures, definitions, and
file-level commands are unchanged. The file compiles.

## Proved and sorry left

The original module had three `sorry`s. One is closed:

- `WeilConjectures.ProperSemilinearGerms.movingPoint_properties`.

Two original theorem holes remain, with no new holes or split-off declarations:

- `WeilConjectures.properSectionsSemilinearGermsRational`
  (`lem-a1-proper-sections-semilinear-germs`).
- `WeilConjectures.properSectionsSemilinearGerms`
  (`lem-a1-proper-sections-semilinear-germs`).

The three private helper lemmas listed above contain complete proofs and no
`sorry`.

## No longer needed

None. No imports, nodes, or modules were pruned.

## Where the brief, the DAG or earlier work was wrong

Earlier attempts were interrupted by temporary compile-server/provider failures.
The current local compile succeeds. Source inspection also found that the germ
construction uses the selected `integralPullbackComposition` family, while some
coherence theorems use the normalized comparison family; no bridge theorem was
found, so no unsupported equality between those families was assumed.

## Second reading by T7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
