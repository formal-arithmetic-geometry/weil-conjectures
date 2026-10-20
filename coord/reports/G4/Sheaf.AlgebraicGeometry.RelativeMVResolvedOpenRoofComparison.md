## What changed

Restored `lean/Sheaf/AlgebraicGeometry/RelativeMVResolvedOpenRoofComparison.lean`
from the quarantine archive named in `coord/rework.tsv`. Removed only
`derivedPullback` from its `attribute [local irreducible]` command. The current
`WeilConjectures.AlgebraicGeometry.DerivedPullback` declares this functor with
`irreducible_def`, so Lean rejects setting the same local reducibility attribute.
The other three local irreducibility attributes remain in place.

The archived file reproduced the recorded error at line 69. The repaired full
file compiled through `lcompile.py` in 33.7 seconds. All existing declarations,
proofs, docstrings and imports are preserved. This is an elaboration repair;
it changes no definition, statement, public import or proof route.

Change record:
`coord/changes/G4-relative-mv-resolved-open-roof-reducibility.md`. The delivery
checker treats edits to local attribute commands as interface changes; the record
documents the old and new commands and the archived consumers for independent
review. No consumer source requires adaptation.

## Proved and sorry left

The quarantined module contained zero `sorry`s and the restored module contains
zero. Holes closed: none. Holes added: none. Split off: none.
`AlgebraicGeometry.relativeMV_resolved_open_roof_comparison` and its seven private
helpers retain their complete proofs.

The repaired proof still combines open-image localization naturality, the
intersection image-resolution comparison specialized to W,W, the normalized
coefficient-roof theorem, `derivedBaseChange_open_transpose`, and
`relativeMVInverseOpenIso_mate`. The change does not impose a new hypothesis or
exclude an empty or full open, zero coefficient object, or zero morphism.

## No longer needed

None: no imports, declarations, dependencies, nodes or modules are pruned.
The redundant local attribute for `derivedPullback` is the only removed text.
The archived parent modules
`Sheaf.AlgebraicGeometry.RelativeMVResolvedRoofOpenMateComparisons` and
`Sheaf.AlgebraicGeometry.RelativeMVResolvedRoofMiddleMateComparison` continue to
use exactly the restored theorem's unchanged signature.

## Where the brief, the DAG or earlier work was wrong

This assignment is the listed zero-hole compile repair, rather than an unproved
theorem. The current upstream functor is already irreducible, unlike the version
against which the archived local attribute was written. Reapplying that attribute
is rejected before it can provide any additional abstraction boundary.

The archive's docstring names
`lem-pc-relative-mv-resolved-open-roof-comparison`, but the shared current
`dag/nodes/` contains neither that node nor a Lean attachment for this module.
No existing node is edited or removed, and the archived blueprint tag and all
Lean dependencies are preserved. The original proof route is unchanged, so this
repair introduces no replacement node or route. There is no current return
specific to this item in `coord/returns/G4.md`; the operative failure is its
`coord/rework.tsv` row.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
