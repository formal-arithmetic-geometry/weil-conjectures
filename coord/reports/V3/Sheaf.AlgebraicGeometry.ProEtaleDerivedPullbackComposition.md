## What changed

Filled `AlgebraicGeometry.Scheme.proEtaleRingDerivedPullbackComposition` without changing
its signature or any existing definition. Three proved private helpers establish the canonical adjunction's sectionwise
normalization, cancellation of inverse restriction maps, and the derived factorization
formula for an arbitrary exact-functor comparison.

Reuse the proved `proEtale_tensor_composition_unit` for the ordinary direct-image
comparison. Invert that comparison and use `conjugateIsoEquiv` to define its canonical
pullback mate. Apply it termwise and descend it using the proved exact-functor APIs
`Functor.mapDerivedCategoryNatIso` and `Functor.mapDerivedCategoryCompIso`.
Their factorization formulas give the required equation on every complex. Apply the general
`SheafOfModules.isKFlat_ringedToposPullback` through the existing algebraic presentation
to obtain K-flatness and flatness of terms.

Updated the original theorem node's proof and dependencies to this argument. The
already proved tensor-composition and algebraic-presentation results are used as tools;
finite-limit preservation is supplied by `det-pe-topos-functoriality-inverse-image`.
The proper-base-change unit's realized statements and proof steps are preserved.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.proEtaleRingDerivedPullbackComposition`
(`lem-weil-pbc-proetale-derived-pullback-composition`).

Holes closed: 1. Holes added: 0. Split off: 0. No sorry remains in the item module.
All three added private helpers are proved. The full module passed `lcompile.py`
without diagnostics in 36.0 seconds. The theorem signature was compared verbatim
with the original. Existing dependency theorems retain their published statements
and proofs.

## No longer needed

Removed the proof import
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
The composition proof does not use `lem-pc-kflat-resolution` or its resolution-existence
module: exact termwise pullback and localization give the comparison on every complex.
Removed that node from proof dependencies and removed its obsolete top-level tool-use
approval. Its existing statement-dependency entry is preserved: no statement metadata
is changed. Other consumers may still require the resolution theorem.

All original public imports remain. All remaining planned proof dependencies are used.
No Lean module is withdrawn, and no whole-library pruning claim is made.

## Where the brief, the DAG or earlier work was wrong

The resolution choice in the old third proof step is unnecessary for the exact
identified-coefficient pullbacks in this statement. The preservation theorem applies
directly to the given complex, and the descended comparison has its factorization
formula on all complexes. This removes the resolution proof dependency without
weakening the K-flat normalization.

The theorem's historical node is currently attached to a downstream alias in
`Sheaf.Paper.IntegralFinitePullbackComposition`; the source theorem proved in this
item and that alias are unchanged. No new node, axiom, statement repair, definition
repair, consumer adaptation or source-library edit is needed.

## Second reading by V3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
