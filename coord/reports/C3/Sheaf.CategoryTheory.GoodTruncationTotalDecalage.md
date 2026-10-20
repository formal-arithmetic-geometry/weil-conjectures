## What changed

Restored the quarantined module `lean/Sheaf/CategoryTheory/GoodTruncationTotalDecalage.lean` with its existing complete proof of `HomologicalComplex₂.good_truncation_total_decalage`. The proof uses the existing total-mono argument, the degreewise good-truncation image theorem, and the canonical decalage subobject construction. No declaration signature or definition was changed.

## Proved and sorry left

Closed zero original `sorry`s: this rework item was quarantined for an import/build collision and its restored module is already sorry-free. Added zero `sorry`s. The theorem `HomologicalComplex₂.good_truncation_total_decalage` compiles unchanged and has no `sorry`.

## No longer needed

No imports or declared DAG dependencies were removed. The proof uses `Sheaf.CategoryTheory.FilteredComplexDecalageComplex`, `Sheaf.CategoryTheory.DoubleComplexTotal`, and `Sheaf.CategoryTheory.GoodTruncationTotalImage`; all are retained.

## Where the brief, the DAG or earlier work was wrong

The prior rework quarantine recorded an import collision involving `Sheaf.CategoryTheory.Filtration` and the adopted `WeilConjectures.CategoryTheory.CanonicalFiltration`. The module itself has a complete proof and compiles against the current artifacts when restored in isolation. This delivery restores that source module without changing its statement or proof route.

## New nodes

None. The existing node `lem-sp-good-truncation-total-decalage` is copied unchanged for the rework delivery.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
