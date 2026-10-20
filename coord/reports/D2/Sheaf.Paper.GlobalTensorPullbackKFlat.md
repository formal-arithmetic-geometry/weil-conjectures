## What changed

Restored `lean/Sheaf/Paper/GlobalTensorPullbackKFlat.lean` from the quarantine
archive named in `coord/rework.tsv`. Replaced its public import of the retired
`Sheaf.Algebra.Homology.KFlatPullback` by
`WeilConjectures.Algebra.Homology.KFlatPullback`. The latter supplies the same
concrete tensor pullback construction; its `IsKFlatTensor` predicate is
definitionally equal to the `IsAcyclicTensorKFlat` used by the archived proof.
Wrapped the existing overlong local `inverse_isKFlat` signature.

The theorem `AlgebraicGeometry.Scheme.Modules.globalTensorPullback_kflat`, its
signature, complete proof and docstring are preserved. The DAG attachment and
three-step route remain accurate, so no node fields change. No definitions or
source-library files change.

Change record: `coord/changes/D2-global-tensor-pullback-kflat-import.md`.

## Proved and sorry left

The assigned module has zero holes before and after this import repair. Its
existing complete proof of
`AlgebraicGeometry.Scheme.Modules.globalTensorPullback_kflat` is restored and
compiles against the current upstream pullback API. Holes closed: none (0).
Holes added: none (0). Sorries left in this packet: none (0). No split-off
statements are introduced.

The final single-file compile passed in 25.3 seconds with no warnings or errors.
The import-direction check also passes. Required delivery checks run separately.

## No longer needed

Removed the public import of the retired duplicate
`Sheaf.Algebra.Homology.KFlatPullback`, replacing it with its official upstream
counterpart. This delivery withdraws no modules or DAG nodes. All declared
proof dependencies remain needed, including point inverse evaluation, concrete
K-flat pullback preservation, inverse-image exactness and comparison, and
change-of-rings preservation of quasi-isomorphisms.

The required library searches found supporting derived-functor infrastructure
rather than a replacement for the combined statement. The current proof already
uses the existing declared results without new lemmas.

## Where the brief, the DAG or earlier work was wrong

This is the quarantined import-collision repair listed in `coord/rework.tsv`,
not an unfinished mathematical proof: the archive already contains zero sorries.
The earlier public import selected a duplicate declaration provider; the
upstream inverse-image comparison also imports the official provider. The
Sheaf duplicate has since been retired. Selecting the official module explicitly
restores the archived proof without changing its meaning or bypassing any unit.

`tools/downstream.py --allow-missing --uses globalTensorPullback_kflat` reports
zero current live consumers. Searching the quarantine too finds the retained
parent `Sheaf.Paper.GlobalTensorPullbackDerivedData`, which applies the unchanged
theorem at line 153. Its attachment and dependencies are preserved; its own
quarantine restoration is separate work. No consumer adaptation is forced by
this signature-preserving repair.

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
