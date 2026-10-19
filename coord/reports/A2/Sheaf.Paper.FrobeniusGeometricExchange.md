## What changed

Filled the three proof holes in `Sheaf.Paper.FrobeniusGeometricExchange` without changing
any declaration's signature, definition, visibility, or imports.

`geometricCompactification_properties` applies Mathlib's
`MorphismProperty.overPullbackMap` to the open and proper maps of the given
compactification. The factorization follows by mapping the equality of arrows in the
over category through `Over.pullback`, then taking underlying maps. The open-immersion
proof uses `c₀.isOpenImmersion` directly, rather than the postponed duplicate wrapper
`zlCompactificationOpen_isOpenImmersion`.

`fiber_finiteType` applies `MorphismProperty.baseChange_obj` separately to locally finite
type and quasi-compactness. `fiberMap_properties` applies `overPullbackMap` to
separatedness, locally finite type, and quasi-compactness.

Two declaration-local `linter.unusedSectionVars` settings retain the original finite-type
parameters in the public signatures while allowing the more general base-change proofs.
No file-level elaboration option or instance was added.

## Proved and sorry left

Closed 3 of 3 original holes (all under node `def-weil-frobenius-square-exchange`):

- `WeilConjectures.FrobeniusExchange.geometricCompactification_properties`.
- `WeilConjectures.FrobeniusExchange.fiber_finiteType`.
- `WeilConjectures.FrobeniusExchange.fiberMap_properties`.

No holes remain in the item module. No holes, declarations, or split-offs were added.
Existing postponed theorems in imported modules remain outside this delivery.
The module compiles through `lcompile.py`; the delivery preflight checks all its declarations.

## No longer needed

No imports or modules were removed. The sole public import
`Sheaf.Paper.FrobeniusSquareExchange` is required by the existing definitions and their
signatures. The node has no numbered proof steps or `proof_deps` to prune; its existing
statement dependencies supply the definitions used throughout the file.

The new proof does not use `zlCompactificationOpen_isOpenImmersion`: the compactification
already supplies this property. Its containing module remains necessary for its definitions.
No coefficient-passage or unit-level route was changed, and no new imports are needed.

## Where the brief, the DAG or earlier work was wrong

The three holes are geometric stability facts already covered by Mathlib; they do not
require new sheaf-theoretic exchange arguments. The existing assumptions on the model
schemes are stronger than these geometric proofs require, but their signatures are preserved.
No mathematical statement or definition repair was necessary. The attached definition node
has an empty proof plan, so there are no numbered steps to implement or replace.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
