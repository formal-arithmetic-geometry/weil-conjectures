## What changed

Replaced three of the four theorem holes in
`Sheaf.AlgebraicGeometry.ClosedRestrictionTotalPullback`, preserving every signature.

`finiteClosedAugmentedRows_exists` now uses the existing
`closedRestriction_signed_refinements` theorem. It extracts the row for the given family,
sets restrictions outside subset inclusions to zero, proves that this leaves every
signed face differential unchanged, and transfers the augmentation and total data.
The augmentation-unit equation follows from the existing component and support-unit
identities. This is a proof from a stated dependency, not a new construction chosen
inside a definition.

`closedRestrictionComparison_unique` obtains epimorphic units from ringed open-closed
localization. Adjunction uniqueness transfers epimorphy to the specified normalized
unit; the inverse-image left adjoint preserves the epimorphism. Componentwise
cancellation proves equality of the comparisons.

`closedTotalComparison_naturality` precomposes with the canonical total comparison
isomorphism, tests equality on all diagonal inclusions, and applies the supplied
component formulas and bicomplex compatibility square.

Added proof imports of signed refinements and adjunction uniqueness. No shared
interface, definition, instance, attribute, public import, or consumer was changed.

Validation: the item compiled cleanly through `lcompile.py` in 36.8 seconds.
A source comparison confirms that all four theorem signatures are verbatim unchanged;
the direct hole count is four before and one after, and every Lean line is at most
100 characters. The delivery tool additionally checks declaration axioms.

## Proved and sorry left

Closed three existing holes:

- `AlgebraicGeometry.finiteClosedAugmentedRows_exists`.
- `AlgebraicGeometry.closedRestrictionComparison_unique`.
- `AlgebraicGeometry.closedTotalComparison_naturality`.

One existing hole remains, unchanged:
`AlgebraicGeometry.closed_restriction_total_pullback`, attached to
`lem-sfb-closed-restriction-total-pullback`. Its complete source and six-step proof
remain in its docstring and DAG node. The row and total isomorphism assembly, their
uniqueness, augmentation equation, and derived normalization remain to be formalized.

No holes were added or split off. The row-existence proof uses the already stated,
still unproved `AlgebraicGeometry.closedRestriction_signed_refinements` dependency;
it does not claim that dependency is closed.

## No longer needed

Removed unused proof imports:

- `Sheaf.AlgebraicGeometry.ClosedImmersionProducts`.
- `Sheaf.CategoryTheory.Sites.GeometricInverseImageExact`.
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`.

The delivered three proofs do not need the intersection-geometry or exact-homology
arguments. Their results remain part of the pending main theorem's existing plan;
no DAG node or whole module is claimed globally pruned. The original DAG plan is
retained because its main comparison theorem is unchanged and still open. In particular the unit route
and the unfinished main comparison are retained.

## Where the brief, the DAG or earlier work was wrong

No false statement or signature change was needed. The existing signed-row interface
lacks the `restriction_zero` field required by `FiniteClosedAugmentedRows`; zeroing
non-subset restrictions repairs this interface mismatch inside the proof. Every
actual deleted-position face is a subset inclusion, so the differential stays equal.
The unit equation required for the augmentation is obtained by composing its
projection formula with the given support unit, without an additional geometric lemma.

Searches used LeanFinder (additive totalization and diagonal inclusions), Loogle
(`"total", "hom_ext"`), the project grep service, and local searches of both library
roots and Mathlib. They identified `HomologicalComplex₂.total.hom_ext`,
`mapTotalXIso`, `ι_mapTotalXIso_hom_assoc`, `ιTotal_map`, and
`Adjunction.unit_rightAdjointUniq_hom_app`; none supplies the entire main theorem.
Read the current blueprint unit and Stacks `proetale.tex`,
`lemma-ses-associated-to-open` (09AH), as well as `homology.tex`,
`lemma-double-complex-gives-resolution` (0133). No new mathematical statement or
new node is introduced. Edge cases remain included: empty intersections, empty
support, one family member, and total diagonals with zero summands.

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
