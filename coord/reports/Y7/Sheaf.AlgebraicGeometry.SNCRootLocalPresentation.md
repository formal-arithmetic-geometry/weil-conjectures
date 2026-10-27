## What changed

Completed `AlgebraicGeometry.snc_root_local_presentation` in
`Sheaf.AlgebraicGeometry.SNCRootLocalPresentation`, preserving its full signature.
Private proved helpers identify the supplied branches with the SNC family,
compute intersection stalks as local quotients, construct the root-quotient
localization, prove its uniqueness, and identify further prime localizations.
Proof imports provide the existing affine ideal-sheaf, stalk-kernel and Mathlib
localization APIs. The node proof now records these constructions.

## Proved and sorry left

Closed the one original hole: `AlgebraicGeometry.snc_root_local_presentation`
(node `lem-sfb-snc-root-local-presentation`). Added zero holes; zero remain in
the item. All seven private helpers are proved. No statements or definitions
were changed and no intermediate theorem was split off.

## No longer needed

No existing public imports, nodes or modules were withdrawn. The function-field
clause of `lem-weil-pbc-spec-domain-stalks-function-field` is unnecessary; only
the affine stalk identification is used. An exploratory proof import of
`Mathlib.AlgebraicGeometry.FunctionField` was removed. Redundant exploratory
imports of `Mathlib.AlgebraicGeometry.Noetherian`,
`Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
`Mathlib.AlgebraicGeometry.StructureSheaf`, and
`Mathlib.RingTheory.Spectrum.Prime.RingHom` were also removed; their needed APIs
are already provided by the retained imports. The fraction-by-fraction
constructions in the original plan are handled by the existing polynomial,
quotient and iterated-localization universal properties. The quotient
localization dependency remains needed for the root quotient, while the
intersection quotient is obtained directly from the surjective stalk map and
its kernel.

## Where the brief, the DAG or earlier work was wrong

The SNC definition supplies its own finite branch family rather than the
chosen enumeration in the theorem. The proof must first embed the enumerated
irreducible components into that family and identify their reduced ideal
sheaves. This necessary reindexing was implicit in the original plan and is
now explicit in both the Lean proof and node. Empty intersections, empty branch
sets, zero rings, and n=1 require no additional assumptions. No other issue.

## Second reading by Y7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
