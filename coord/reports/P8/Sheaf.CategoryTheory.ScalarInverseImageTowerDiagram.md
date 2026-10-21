## What changed

Proved `SheafOfModules.RingedTensor.scalar_inverseImage_tower_diagram` in
`Sheaf.CategoryTheory.ScalarInverseImageTowerDiagram`, preserving its signature and
all three existing definitions verbatim. All added declarations are private and
proved. No other Lean module changes.

Scalar reassociation comes from uniqueness of left adjoints, with its two quotient
formulas proved from the scalar units, linearity and balancing. The normalized
inverse-image comparison comes from the geometric module direct image and natural
semilinear Hom bijections. Its unit equation gives the generalized pure-tensor
formula via the transported scalar action. The composite comparison is defined
by pasting the two successive comparisons with reassociation; its normalization
is proved explicitly, and the square follows by cancellation. Evaluation gives
the equality in every degree of a cochain complex.

Private proof imports reuse geometric module transport/construction and their
proved Hom-equivalence APIs. The elementary operation maps, graph calculation and
ring-operation transport proof are private helpers here, adapted from the proved
helpers in `RingedToposKFlatPullback` and
`RingedTopoiInverseImageTensorPairingIsIso`. Their full proofs are included, so this
item does not load the tensor-comparison or K-flat pullback constructions. A general private adjunction comparison lemma and local cached
instances avoid unfolding sheafification choices during elaboration. Addition and
scalar action are marked locally irreducible after their graph formulas have been proved, to
avoid repeated reduction of categorical limit choices. The caches
are scoped to private proof helpers and do not enter existing public definitions.
Updated the item's DAG proof, proof dependencies and proof origin to this route.
The public-import narrowing and scoped proof commands are documented in
`coord/changes/P8-scalar-inverse-image-tower-imports.md`; there are no downstream
Lean consumers to adapt.

## Proved and sorry left

Closed the sole original hole:
`SheafOfModules.RingedTensor.scalar_inverseImage_tower_diagram`
(node `lem-sfb-scalar-inverse-image-tower-diagram`).

Holes closed: 1. Holes added: 0. Holes remaining: 0. No split-off statements.
The complete file compiles through `lcompile.py`; `#print axioms` for the theorem
reports exactly `propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

Removed the proof import `Sheaf.Paper.RingedTopoiInverseImageTensorComparison` and
its node `lem-weil-pbc-algebraic-inverse-image-tensor-comparison` from this item's
proof dependencies and obsolete `tool_uses`. The general tensor comparison is
replaced here by the scalar-specific adjunction construction, using the already
proved `Sheaf.CategoryTheory.GeometricModuleTransport`.

Also removed the unused public imports of
`Sheaf.CategoryTheory.RingedToposMorphism` and
`Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`. Narrowed
`Sheaf.CategoryTheory.AlgebraicInverseImageOfUniverses` to the specialized
`Sheaf.CategoryTheory.AlgebraicInverseImage` used by the statement, and
`Mathlib.Algebra.Homology.DerivedCategory.Basic` to
`Mathlib.Algebra.Homology.HomologicalComplex`. The conclusion only evaluates a
cochain complex at each degree; it needs no tensor on complexes or derived category.
The original algebraic-inverse-image and tensor-product nodes remain needed through
the specialized presentations and scalar tensor constructions.

The proof also avoids imports of
`Sheaf.Paper.RingedTopoiInverseImageTensorPairingIsIso` and
`Sheaf.CategoryTheory.RingedToposKFlatPullback`: only their elementary graph
calculations were needed, and these are now proved locally. This removes their
unrelated general tensor and derived pullback import closure from this item.

The old plan's separate injectivity argument for maps from the double extension
is unnecessary: the conclusion existentially quantifies the comparisons, so the
composite comparison can be defined by pasting and then normalized explicitly.
All other original mathematical dependencies remain used through scalar tensor
construction, algebraic inverse-image presentations, or the termwise conclusion.
No modules are withdrawn and no source-library declarations are removed.

## Where the brief, the DAG or earlier work was wrong

No false statement or incorrect definition was found. The existing plan is valid
but longer than needed for this existentially stated theorem. The replacement
route preserves both reassociation formulas, every generalized-section
normalization, the natural-transformation square and its termwise consequence.
It uses no assumption of points, global pure-tensor generation, nonzero rings,
nonzero modules, or flatness; the argument also applies to identity maps, zero
modules/rings, empty sites, and nonflat scalar towers.

## Second reading by P8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
