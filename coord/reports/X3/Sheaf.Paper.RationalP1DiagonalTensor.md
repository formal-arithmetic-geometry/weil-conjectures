## What changed

Proved `AlgebraicGeometry.ProEtale.RationalP1.diagonalTensorIso_naturality` in
`Sheaf.Paper.RationalP1DiagonalTensor`. Private, proved helpers derive naturality
from the native adjunction projection map, the two braiding identities, the
section comparison and the right unitor, then cancel the invertible comparisons.

Factored the existing explicit diagonal composite into the new irreducible
`AlgebraicGeometry.ProEtale.RationalP1.sectionTensorMap`, parameterized by arbitrary
schemes, the two morphisms, and specified section and unit comparisons. The
existing `diagonalTensorMap` now applies that constructor to precisely its former
canonical data. This avoids unfolding concrete projective-line site instances
when proving naturality. All existing public signatures, attributes and imports
are unchanged; the construction, its orientation and mathematical meaning are
unchanged. No other Lean module changes.

The repaired module, including the naturality proof, compiled in 30.0 seconds
with profiling enabled. Diagnostic options and commands have now been removed;
the final delivery checks compile the cleaned file again.

Change record: `coord/changes/X3-diagonal-tensor-parametric-construction.md`.
The consumer check lists all 239 transitive importers. The only external textual
use of the inverse is `diagonalClassMap` in `RationalP1AmbientComposites`; it uses
the unchanged isomorphism interface and needs no adaptation. No target changes.

## Proved and sorry left

Original holes: 2. Closed: 1. Added: 0. Split off: 0. Remaining: 1.

Closed:

- `AlgebraicGeometry.ProEtale.RationalP1.diagonalTensorIso_naturality`.

Remaining, unchanged:

- `AlgebraicGeometry.ProEtale.RationalP1.diagonalTensorMap_isIso`, node
  `def-sfb-internal-diagonal-tensor-comparison`.

The naturality proof uses the existing `diagonalTensorMap_isIso` theorem to
invert and cancel the forward comparisons. Its closed-support argument remains
the original named obligation; no replacement obligation is introduced.
All added helpers are proved and the added definition has explicit data.

## No longer needed

None. No existing import, declaration, node or module is withdrawn.
The unit's prescribed diagonal-comparison route is retained.

## Where the brief, the DAG or earlier work was wrong

The original concrete definition caused its naturality proof's type conversion
to exceed 120 seconds. The parametric constructor fixes that elaboration problem
without changing its mathematics. The native projection is already a natural
transformation in the existing adjunction API, so naturality needs no new
mathematical dependency. The separate closed-support invertibility proof remains
open.

The new constructor makes no invertibility claim and requires only the explicit
section and unit isomorphisms that the diagonal construction already supplies.
Its composition is meaningful for empty schemes and zero modules as well.

## New nodes

`def-sfb-section-tensor-comparison` records the explicit parametric constructor
`sectionTensorMap` in the item module. It has no proof obligation and no `sorry`.
Its definition dependencies are the existing derived module operations, fixed
native tensor interface and canonical projection family. Mathlib and blueprint
searches found no duplicate. The existing diagonal node cites this constructor
and records the same-data implementation change with its five citers all marked
holds. The change record is
`coord/changes/X3-diagonal-tensor-parametric-construction.md`.

## Second reading by X3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
