## What changed

Replaced the single sorry in
`AlgebraicGeometry.Etale.isCompactObject_lowerStar_openImmersionLowerShriek_of_isFiniteLocallyConstantSheaf`
with the current DAG's adjunction proof. The existing private helpers transport compactness
along additive adjunctions and isomorphisms. Finite type makes the strata Noetherian;
the rank-one/constant-sheaf adjunction makes the tensor unit compact; lisse dualizability
makes L[0] compact; the open and closed adjunctions then give the required compact object.
The exact-functor single comparisons identify it with (g_* j_! L)[0].

The derived braiding is installed locally using the proved existence theorem
`DerivedCategory.nonempty_braidedCategory`. Existing signatures, public imports, docstrings,
definitions and visibility are unchanged. No other module is adapted.

Validation: the complete main module compiled through `lcompile.py` in 14.2 seconds,
with no errors or warnings. The existing closed-right-adjoint and lisse-dualizability
modules were compiled unchanged into the sandbox build cache, because the published build
lacked the former artifact. These unchanged support sources are not part of the delivery.
No existing signature, public import or declaration was changed.

Current resumed-session validation: `deliver3.py --no-push` passed compilation and
all preflight checks (dry-run commit `31086b777b`, review class AUTO). The earlier
compile-service response failures recorded in the sandbox logs are resolved.

## Proved and sorry left

Original holes: 1, in
`AlgebraicGeometry.Etale.isCompactObject_lowerStar_openImmersionLowerShriek_of_isFiniteLocallyConstantSheaf`
(node `lem-pur-etale-lisse-stratum-compact`). This hole is closed by the compiled proof.
Holes closed: 1 of 1.

Sorries in the sandbox Lean source: 0. Holes added: 0. New declarations: 0.

## No longer needed

Removed the proof-only import
`WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided`:
the proof uses the already available, proved existence theorem
`DerivedCategory.nonempty_braidedCategory`, so no named braiding is needed. Also removed the redundant proof-only import
`WeilConjectures.SixFunctors.Etale.Derived.Kunneth.CohomologicalDimension`:
its finite cohomological dimension API is already available through the retained
`WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Coproducts` import.
The implementation follows all five steps of the current DAG plan and retains its
existing dependencies. No blueprint unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

`coord/changes/upsync-e9ba49ac4.md` explains that the upstream sync replaced the former
proof with sorry because the unprimed derived braiding disappeared. The proof now uses the
proved existence of a derived braiding. The mathematical statement and the current DAG route
remain unchanged. The published compiler build lacked one of the existing declared
proof dependencies, so both existing support modules were compiled unchanged through the
prescribed `lcompile.py --all` sandbox mechanism. No dependency was restated or changed.

## Second reading by X3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
