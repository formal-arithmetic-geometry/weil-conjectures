## What changed

Replaced the sole `sorry` of
`WeilConjectures.sfPackageLocalizationCommonStages` by a Lean proof assembling the
base rational boundary, a finite coefficient-field family, and its common-stage
boundary. For each finite field the proof constructs an operation datum with the
recorded finite normalization at level one, reuses
`sfPackageLocalizationIntegralTower`, and applies rational transport. It then
applies the supplied-family descent theorem and assembles the field-system witness.
The finite-image, integral-tower, and final projection-realization proofs stay intact.

Moved the thirteen public localization data declarations into
`Sheaf.Paper.SfPackageLocalizationBoundaryData` and publicly reexported that module.
This permits the two new proof modules to use the boundary predicates without an
import cycle. All existing declaration signatures and definition bodies are preserved;
no target or definition meaning changes. The boundary type is now an ordinary
definition rather than an abbreviation, so the new proof can keep its large category
expression folded locally while passing boundary witnesses. The other predicates are
opened only when constructing their witnesses. The item's old public projection imports
remain present. Two private proof imports provide the new intermediate theorems. The five already
proved private coefficient-square helpers are retained in the rational transport
module for its remaining proof. Its generic helper section respects transparency.
All four modules passed the remote compilation check after the boundary definition
repair; profiling options have been removed for the delivery checks.

## Proved and sorry left

Original item: one hole, in `WeilConjectures.sfPackageLocalizationCommonStages`.
Its proof is now complete from the named dependencies; no `sorry` remains in the item.
This delivery is a decomposition, not a net hole reduction: it closes that upper hole
and adds two strictly smaller obligations, each in its own module:

- `WeilConjectures.sfPackageLocalizationRationalTransport`, node
  `lem-sf-package-localization-rational-transport`: rationalization of a supplied
  integral tower boundary, with its prescribed coefficient equation and distinguished
  triangle. It asserts neither finite-field family existence nor common-stage descent.
- `WeilConjectures.sfPackageLocalizationBoundaryDescent`, node
  `lem-sf-package-localization-boundary-descent`: scalar compatibility and common-stage
  descent of an already supplied tower-pinned finite-field family. It does not construct
  that family or the base rational boundary.

Each new hole has source, complete proof in words, and an attached DAG node.
The extracted data module has zero holes. Empty strata and zero inputs are included
in the intermediate arguments. Server compilation is recorded by the delivery checks.

## No longer needed

The item no longer needs `lem-sf-package-compactified-tower-comparisons`: its existing
exact-image proof uses the operation datum's composition, open identification and
proper identity comparisons directly. Removed this node from the relevant proof step
and proof dependencies. No module is withdrawn; other users may still need it.

The direct public import of `Sheaf.Paper.SixFunctorOperationDatum` is replaced by the
public boundary-data import, which itself publicly imports the operation datum.
All public names and availability are preserved. No other original import is removed.
The new intermediate modules import only their statement data; no unused scalar
localization proof import is retained. The private coefficient-square helpers
`sfPackageCoefficientOpen`, `sfPackageCoefficientClosed`, `sfPackageCoefficientOuter`,
`sfPackageCoefficientFirst`, and `sfPackageCoefficientSecond` move to the rational
transport module. They are not pruned: they are already proved inputs to its remaining
transport argument and should not have to be reconstructed by the next worker.

## Where the brief, the DAG or earlier work was wrong

The coefficient-passage step bundled three distinct tasks: rational transport,
construction of the finite-stage family, and descent with all transition squares.
The middle task follows by applying the existing integral-tower theorem to each
recorded coefficient normalization. The two remaining tasks are isolated as explicit
intermediate statements, rather than replacing the original theorem by an alias.
The DAG now records this assembly. The original statement and the unit route remain
unchanged. The boundary data extraction is required to avoid an import cycle, not
to evade a compile-time limit; the original module compiled in 50 seconds.

## New nodes

`def-sf-package-localization-boundary-data` records the unchanged public data moved
to `Sheaf.Paper.SfPackageLocalizationBoundaryData`. Its thirteen declaration names,
signatures and bodies are preserved. The boundary type changes from an abbreviation
to an ordinary definition to permit local irreducibility; its body is identical. Change record:
`coord/changes/C5-localization-boundary-data-extraction.md`.

`lem-sf-package-localization-rational-transport` records the rationalization step
in `Sheaf.Paper.SfPackageLocalizationRationalTransport`. Its proof uses scalar
localization's unique natural-transformation extension and exact transport of the
integral triangle; the coefficient comparison fixes the boundary.

`lem-sf-package-localization-boundary-descent` records the compatibility and descent
step in `Sheaf.Paper.SfPackageLocalizationBoundaryDescent`. Its proof uses the
source recollement boundary, exact scalar extension, and common-stage descent of
the supplied family. The family-existence proof is already in the item.

## Second reading by C5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
