## What changed

Restored the complete proof of `AlgebraicGeometry.Scheme.exists_properFlatDirectImagePerfectChart` in `lean/Sheaf/AlgebraicGeometry/ProperFlatDirectImagePerfectChart.lean`. The proof is the existing affine Cech perfect-model argument, including bounded tensor-cohomology vanishing and the derived-pullback base-change comparison. The public `DerivedPullback` import points to `WeilConjectures.AlgebraicGeometry.DerivedPullback`, which owns the current implementation.

## Proved and sorry left

- Proved `AlgebraicGeometry.Scheme.exists_properFlatDirectImagePerfectChart` (the module had one target theorem and now has zero `sorry`s).
- No `sorry`s left and no new holes added.

## No longer needed

None. The proof uses all imports retained in the module and the declared proof dependencies: the affine Cech perfect model, relative flatness of finite locally free modules, bounded-above flat K-flatness, tensor-closed structure, module pullback adjunction, and derived pullback.

## Where the brief, the DAG or earlier work was wrong

The quarantine restore had recorded this item as failing because of the withdrawn `Sheaf.AlgebraicGeometry.DerivedPullback` public import. The proof compiles after redirecting that import to the adopted upstream module `WeilConjectures.AlgebraicGeometry.DerivedPullback`; no statement or proof change is required.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
