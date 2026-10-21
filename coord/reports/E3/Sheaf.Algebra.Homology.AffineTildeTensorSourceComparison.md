## What changed

Simplified the public interface of
`Sheaf.Algebra.Homology.AffineTildeTensorSourceComparison`: import
`Sheaf.Algebra.Homology.AffineTildePushforwardCohomologyNormalization` directly
instead of the declaration-free Sheaf core-final wrapper. The adopted comparison
already publicly supplies the core theorem and derived-unit compatibility.
The normalization import preserves the legacy `affineTildeFunctor` abbreviation
and its instance. All public declarations and their types remain available.

The changed interface compiles in 1.8 seconds. A scratch consumer importing this
interface repeats the complete archived theorem statement and proof, including
the old tilde spelling, and compiles in 31.7 seconds. It verifies the archived
core API and universal equation. Its theorem, the source comparison theorem and
the core-final theorem all use only `propext`, `Classical.choice`, `Quot.sound`.
The replacement import passes the import-direction check. Recursive public
import comparison removes only the declaration-free wrapper. Scratch work is
outside `lean/` and is excluded from delivery.

Change record: `coord/changes/E3-affine-tilde-source-direct-interface.md`.

## Proved and sorry left

The current item has zero `sorry`s before and after this change. Holes closed:
none (0 of 0). Holes added: none (0). Split off: none (0). No named declaration
is left with `sorry` in this packet.

`AlgebraicGeometry.exists_affineTildeTensorSourceComparison` already has a
complete adopted proof, as does
`AlgebraicGeometry.exists_affineTildeTensorSourceComparisonCore`. This delivery
preserves those proofs and verifies their axioms; it claims no new mathematical
proof, definition repair or quarantine restoration.

## No longer needed

Removed the direct public import of
`Sheaf.Algebra.Homology.AffineTildeTensorSourceComparisonCoreFinal` from this item.
The module has no declarations, and all its public dependencies remain supplied
by the two retained imports. This prunes an interface dependency only. The wrapper
itself is neither deleted nor withdrawn, and no whole-library module pruning is
claimed. No mathematical node or proof dependency becomes unnecessary: the
K-flat source comparison, affine pushforward-unit invertibility and derived
base-change transport argument are retained in the adopted implementation.

## Where the brief, the DAG or earlier work was wrong

The route note predates the adopted implementation and W6's successful interface
restoration, recorded in the ledger on 2026-10-21 at 18:26 UTC. The live module
is already present and compiling, and its theorem has no dependence on `sorryAx`.
The stale quarantine row is not evidence of an unresolved mathematical hole.
This session therefore performs a concrete redundant-import cleanup and reports
the actual zero-hole count. No root bypass, new split or affine-core relocation
is needed.

The quarantined source and the four quarantined direct consumers were inspected.
Their declarations are preserved; no missing module is treated as withdrawn.
The original node attachment and mathematical dependencies remain accurate and
unchanged, as does the unit route. The complete archived statement and its proof
were recompiled through the simplified interface. No other group's module was
adapted.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
