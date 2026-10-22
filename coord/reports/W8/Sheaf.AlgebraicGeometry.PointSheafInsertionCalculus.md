## What changed

Filled `AlgebraicGeometry.Scheme.pointSheafInsertionCalculus` in
`Sheaf.AlgebraicGeometry.PointSheafInsertionCalculus`, with the exact existing theorem
statement and all existing public definitions. The private helpers construct the module
restriction adjunction for the specified coefficient comparison, prove its graph
normalization by a triangle identity, compute the exact chosen compositor on nested
unit generators, and deduce linear natural section insertions and their cocycle. The
cochain maps and isomorphisms use Mathlib’s degreewise extension of natural
transformations and natural isomorphisms, so their differential compatibility is
provided by those constructions; the remaining naturality and cocycle equations
are checked componentwise. The generic private linear restriction map uses successive
scalar restrictions in the same order as the existing sections functor. This avoids
expensive definitional conversion with restriction along a composed ring homomorphism.
The insertion transformation is constructed directly and has a proved section formula.
A private proposition names graph normalization, avoiding repeated elaboration of its
sectionwise expression in the helper signatures.
The item's DAG proof and proof dependencies describe this route.
No source-library module is changed and no new module or node is introduced.
The compile-time attributes and proof-local instance registration are documented in
`coord/changes/point-sheaf-insertion-proof-elaboration.md`. The one direct importer,
`Sheaf.Paper.PointSystemPowerRoosCoherence` (unclaimed), needs no adaptation.

The proof uses `lem-pur-proetale-module-pullback-composition` as the API for the
compositor already used in the existing public definition. This is a tool from
`sk-def-sf-operations`: its direct-image formula and conjugation equation determine
that exact compositor, while the unit has no separate computation of ordinary module
pullback composition. No maintainer approval is added by this delivery.

## Proved and sorry left

Closed the one original hole, `AlgebraicGeometry.Scheme.pointSheafInsertionCalculus`
(node `lem-trf-point-sheaf-insertion-calculus`). Added zero holes and split off zero
statements. Every private helper is proved; there is no `sorry` in the delivery.
The complete file passed `lcompile.py` in 56.4 seconds after localizing the helper instances.

## No longer needed

The direct unit computation avoids the three former proof imports:
`Sheaf.AlgebraicGeometry.ProEtaleConstantRingComposition`,
`Sheaf.CategoryTheory.SiteInverseImageCompositionGenerators`, and
`Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIso`.
The proof no longer needs nodes `lem-trf-constant-coefficient-composition`,
`lem-trf-site-inverse-image-composition-generators`,
`lem-weil-sheaf-scalar-extension-ring-iso`,
`prop-weil-pbc-proetale-constant-ring-map`, or the theorem
`lem-sf-proetale-tensor-composition-unit`. The module
`Sheaf.AlgebraicGeometry.ProEtaleTensorCompositionUnit` stays publicly imported:
its actual generator definition occurs in the existing public graph-insertion definition.
The old top-level tool approvals for the scalar-extension isomorphism, finite
constant-ring map, tensor-composition theorem, and site-composition generators are
withdrawn from this node; the object-restriction approval is retained. This is pruning
of this proof's dependencies; no claim is made that other consumers cease needing them.

## Where the brief, the DAG or earlier work was wrong

The generic object-restriction theorem exposes existence and naturality of its module
isomorphisms, but omits their graph normalization. Its private adjunction construction
can be repeated with the specified public coefficient comparison and normalized by
Mathlib's uniqueness-of-left-adjoints unit equation. This supplies the missing equation
without changing that dependency or introducing a new unproved result. The existing
compositor theorem already gives its exact direct-image mate, so nested scalar units
can be computed directly from its conjugation equation, without separately comparing
coefficient compositors or importing the full generic tensor-composition theorem.

## Second reading by W8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
