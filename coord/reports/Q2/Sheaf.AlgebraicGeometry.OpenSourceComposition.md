## What changed

Proved `AlgebraicGeometry.Etale.unboundedEtaleLowerShriekCompIso_open_source` without changing its statement. The proof reuses the existing unbounded formalism and its proved comparison identifications through a private `import all`. It computes composition on the triangle with compactifications `(w,id_X)`, `c`, and `c.precomp w`; the exchange square has identity horizontal arrows. The exchange identity law and the proper-composition left unit law compute its compositor. The every-triangle equation, the open-composition identification, the proper identity identification, naturality, and inverse cancellation give the specified equality.

Updated the item's DAG proof and proof origin to describe this shorter calculation. No definitions or public interfaces changed.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.Etale.unboundedEtaleLowerShriekCompIso_open_source` (node `lem-amb-compact-support-open-source-composition`). Added zero holes; zero holes remain in the delivered module. No split-off statements.

## No longer needed

Removed redundant direct proof imports `Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence` and `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`; both remain available through the existing public imports.

The pullback-unit identification of `e.restrict` with `(w,id_X)` and its refinement-comparison normalization are unnecessary: the existing every-triangle theorem applies directly to the identity-proper triangle. All three declared proof dependencies remain needed through the unbounded formalism and its open-adjunction/composition identifications. No modules or DAG nodes are withdrawn.

## Where the brief, the DAG or earlier work was wrong

The earlier proof plan used only the restricted-tower presentation of the general comparison theorem. Its already-proved underlying formalism accepts an arbitrary triangle, so the source-open case avoids constructing and normalizing a pullback compactification. The theorem is unchanged and includes identity and empty opens without extra assumptions. The unit route is preserved.

## Second reading by Q2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
