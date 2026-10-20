## What changed

Restored the quarantined item module as a public compatibility import of
`WeilConjectures.AlgebraicGeometry.HigherDirectImageDerivedModel`. That adopted
module already proves exactly
`AlgebraicGeometry.Scheme.Modules.exists_derived_model_higherDirectImage`.
Reusing it removes the obsolete Sheaf derived-pullback import and avoids both
same-name derived-pullback and higher-direct-image theorem declarations.
The quarantine archive and every source-library file are unchanged.

Reattached `lem-pc-higher-direct-image-derived-model` to the existing adopted
source declaration, with its exact signature. The only spelling difference
from the archived statement is the explicit `AlgebraicGeometry.derivedPullback`
qualification needed in the current namespace. All hypotheses, quantifiers,
cohomology comparisons and arbitrary cartesian-base-change conclusions agree.
No definition or target statement changes.

The source proof follows the existing two-step DAG plan: construct Rf_*(F[0]);
use right-derived-functor connectivity and homology comparisons; apply canonical
relatively flat module base change; identify tensor pullback with ordinary
pullback by adjunction uniqueness; and apply homology. All mathematical edges,
parent dependencies and unit steps are retained. No arbitrary existence witness
is used to define the derived model.

The restored module compiles cleanly. A sandbox signature probe applies the
source theorem at arbitrary universe parameters and arbitrary input schemes,
with no extra assumptions; its axiom output is exactly `propext`,
`Classical.choice`, `Quot.sound`. A consumer probe checks coexistence with the
unchanged source `Cohomology.DirectImage.PerfectLocusOfRank`.
The consumer query reports zero importers of the absent Sheaf path. The live
perfect-locus proof already calls the canonical source declaration, and its
DAG parent still cites this node. Therefore this is a restoration and ownership
repair, not a withdrawal based on zero importers.

Change record: `coord/changes/A9-higher-direct-image-derived-model-source-proof.md`.

## Proved and sorry left

Original assigned module: 0 sorry; final restored module: 0 sorry.
Holes closed: none. Holes added: none. Split off: none.
This is a completed zero-hole quarantine/import repair, not a new proof count.

The existing proved theorem
`AlgebraicGeometry.Scheme.Modules.exists_derived_model_higherDirectImage`
(node `lem-pc-higher-direct-image-derived-model`) is preserved by re-export.
Its entire axiom closure contains only the three allowed axioms. No unfinished
lemmas, new declarations, hollow definitions or new nodes are introduced.

## No longer needed

The duplicate local declaration/proof is superseded by the identical adopted
source proof, re-exported publicly. Its obsolete direct public import of
`Sheaf.AlgebraicGeometry.DerivedPullback` is removed. That path was retired in
the source-construction repair; the canonical source DerivedPullback supplies
the actual functor used by this theorem.

The explicit public imports of `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
`Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`, and
`WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic` are supplied
transitively by the new public source import. The old private imports of
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility`
and `WeilConjectures.AlgebraicGeometry.RelativelyFlatCanonicalModuleBaseChange`
are internal to the preserved source proof and no longer repeated in the
compatibility module. They remain needed by the mathematical argument.

No mathematical node, dependency, unit route, or source module is pruned.
No path is listed in deleted.txt and the quarantined archive is not removed.

## Where the brief, the DAG or earlier work was wrong

The item is an assigned zero-hole repair, as permitted by the brief. Its
archived proof was already complete; the 2026-10-20 source sync made the
parallel Sheaf and adopted constructions conflict. The adopted source also
contains the complete higher-direct-image model proof, so a new proof or a
new split-off statement would duplicate existing mathematics. Restoring only
the archived file would retain stale ownership. The repaired compatibility
import and source attachment resolve ownership while preserving the node,
its parent and all mathematical dependencies.

Read the current main-20261015 unit and its relatively flat base-change node.
The more general theorem remains applicable to the unit's invertible-sheaf
case; its proof route is not bypassed. There is no open A9 return entry for
this item and no forced consumer adaptation.

## Second reading by A9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
