## What changed

Proved the original `AlgebraicGeometry.AlgebraicSpace.exists_linePresentation`
from effective realization and descent of module morphisms. The proof lifts the
small-etale equality isomorphism and its inverse, uses uniqueness of morphism lifts
to prove the two inverse identities, constructs the componentwise cartesian
isomorphism, handles the dependent section transport explicitly, and proves its
uniqueness. Its signature and all existing definition bodies are unchanged.

Moved the ten presentation declarations preceding that theorem verbatim from
`SpaceLineModuleProjInput` to `SpaceLinePresentationDefs`, publicly reexported by
the item. This prevents an import cycle between the presentation definitions and
their existence theorem. Added `TestLineHom` with proved identity, composition,
extensionality, etale compatibility and conversion from cartesian isomorphisms.
The new definitions have explicit data; no definition contains a hole or chooses
arbitrary data from an unproved existence theorem. `linePresentation` still uses
the original existence-and-unique-isomorphism universal property.

`SpaceLinePresentationHomDescent.existsUnique_testLineHom` has a complete proof
from the separate fullness result. Its faithfulness argument is proved here:
all opens of small-etale tests determine the chart sheaf morphisms, every test
has a surjective etale atlas pullback, and the proved upstream fpqc descent
faithfulness determines its morphism. The tensor/ordinary-pullback comparison
is inserted explicitly. The atlas etaleness and surjectivity witnesses are
reconciled by the unique isomorphism between their representing pullbacks;
no common witness is assumed from two unrelated existentials.

All five sandbox modules compile cleanly through `lcompile.py --all`.
Each compiled separately within the server's per-file limit. The unchanged direct
consumer `SpaceSectionAlgebraEtaleBaseChange` also compiles against the sandbox
modules. The unchanged `SpaceLineModuleProjMap` consumer compiles as well.

## Proved and sorry left

Closed original hole:
`AlgebraicGeometry.AlgebraicSpace.exists_linePresentation` (1 of 1 original holes).

Added two holes, each the entire proof of a public theorem in its own module:

- `AlgebraicGeometry.AlgebraicSpace.exists_etaleLinePresentation`, in
  `SpaceLinePresentationExistence`, node
  `lem-trf-cartesian-line-presentation-existence`.
- `AlgebraicGeometry.AlgebraicSpace.exists_testLineHom`, in
  `SpaceLinePresentationHomExistence`, node
  `lem-trf-cartesian-line-presentation-hom-existence`.

This is a decomposition, not a net hole reduction: 1 original hole closed,
2 holes added, net -1 before the ledger accounts for newly reached imports.
The item has zero remaining sorries. The shared definitions module and the
morphism-uniqueness module have zero sorries. The original isomorphism
existence/uniqueness assertion is not merely renamed: object existence supplies
only objects; fullness supplies arbitrary module maps; the proof combines
morphisms and their inverses and proves uniqueness using the separately proved
faithfulness argument.

The two remaining constructions follow the existing atlas/descent argument.
The supplied node originally had no proof steps or proof dependencies. I read
the canonical scheme comparison and module-descent APIs, searched the source
library and Mathlib, and proved the faithful part using the existing fpqc
morphism theorem. The unresolved object construction must connect the custom
small-etale localized site to the scheme comparison, build its atlas descent
datum, and retain its tensor and section identifications. The unresolved
morphism construction must build the chart map in those coordinates and check
its overlap equality before invoking the existing fpqc fullness theorem.
These are separate source results, documented completely in their theorem
docstrings and nodes. Neither assumes the original universal property.

## No longer needed

No mathematical dependency node or entire existing module is pruned.
No part of the unit's route is bypassed.

Removed the item's direct public imports of
`SquareZeroTensorBoundaryComparisons` and `TensorPullbackCompositionIso`:
they remain public imports of `SpaceLinePresentationDefs`, so their public
availability is preserved and they remain needed by the definition bodies.
Replaced the direct public import of `AlgebraicSpace` by the shared presentation
definitions module, which publicly imports it. This is factoring, not removal
of those mathematical dependencies. Removed the exploratory private import of
`AlgebraicSpaceRepresentableEtaleSchemeTests`: the proved atlas lemma uses
only the atlas data already present in `AlgebraicSpace`, so that extra theorem
is unnecessary for the written proof.

## Where the brief, the DAG or earlier work was wrong

The original definition node includes a nontrivial existence/unique-isomorphism
theorem but its proof and proof_deps were empty. The node now records the actual
assembly and its dependencies. No statement is disputed or weakened. The
existing source-library declarations and their public imports are untouched.
The custom site requires an explicit comparison with a scheme's small-etale
site; the available scheme equivalence cannot be applied to it by definitional
equality. This is recorded as work in the remaining construction lemmas rather
than assumed silently.

Edge cases checked in the mathematical statements: empty scheme tests,
zero module maps, identity maps, non-separated or non-quasi-compact atlases,
and repeated overlap indices. No quasicoherence assumption on arbitrary
small-etale modules is inferred: the test modules used for faithful descent
are invertible by the presentation's existing field, hence quasi-coherent.
Surjective etale covers are used through the fppf-to-fpqc topology inclusion,
so no quasi-compactness of the atlas projection is imposed.

A raw dependency traversal also encounters a pre-existing cycle below the unchanged
relative-Proj dependency: `prop-nagata-relative-proj-functoriality` and
`lem-nagata-affine-proj-scalar-extension` point back to one another. This delivery
does not edit either node or introduce that cycle; maintainer reconciliation is
needed if the project's DAG checker does not already exclude those records.

## New nodes

`def-trf-cartesian-line-presentation` records the moved definitions and the
componentwise morphism API, in `SpaceLinePresentationDefs`. Existing signatures,
data and attributes are retained; the item publicly reexports the module.

`lem-trf-cartesian-line-presentation-existence` states only effective object
realization, in `SpaceLinePresentationExistence`, with its atlas descent proof.
It does not assert uniqueness or introduce selected definitions.

`lem-trf-cartesian-line-presentation-hom-existence` states fullness for all maps
between two fixed presentations, in `SpaceLinePresentationHomExistence`. It
contains no existence of presentations and no assertion that the lifted map
is invertible or unique.

`lem-trf-cartesian-line-presentation-hom-descent` records the proved
existence-and-uniqueness assembly in `SpaceLinePresentationHomDescent`, including
the full proof of faithfulness on arbitrary scheme tests.

All new nodes retain the original chapter, unit, and blueprint ancestry.
LeanSearch, LeanFinder/Loogle and Mathlib grep searches are logged in
`searches.jsonl` and copied into the node search records. Blueprint searches
for cartesian line, line module, 03M3 and the descent tag found no duplicate
blueprint node. Related scheme-only comparison and fpqc descent nodes are
cited as tools. Their modules and theorem signatures were read.

Change record: `coord/changes/T4-cartesian-line-presentation-factoring.md`.

## Second reading by T4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
