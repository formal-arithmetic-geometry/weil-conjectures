## What changed

Proved `AlgebraicGeometry.ProEtale.coefficientComparison_representable_preservesColimit`
from the existing essential-image characterization
`Scheme.proEtaleClassicalSheavesImage`. The private, fully proved construction
`pullbackEtaleRepresentableIso` identifies the inverse image of a lifted etale
representable with the corresponding lifted pro-etale representable, using the
comparison adjunction and the sheaf-valued Yoneda lemma.

The characterization makes this representable classical. For the given
presentation, its bijective continuity map makes its restriction cocone
colimiting. Joint surjectivity and eventual equality then transfer explicitly
between the ULift hom sets and the coefficient-model opposite hom sets. The
original cone is a limit by reflection through the fully faithful forgetful
functor and preservation by the AsSmall equivalence; its opposite gives the
colimit needed for the claimed preservation instance.

Added only private proof imports of
`Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesImage` and
`Mathlib.CategoryTheory.Limits.Types.Filtered`. Updated the item's node proof,
proof dependencies and proof origin. Its statement, universes, public imports,
all definitions, and the unit route are unchanged. No other module is adapted.
The new dependency has no import or DAG dependency path back to this item.
The delivered module compiled successfully through lcompile.py in 5.5 seconds,
with no warnings or errors.

## Proved and sorry left

Closed one of one original holes:
`AlgebraicGeometry.ProEtale.coefficientComparison_representable_preservesColimit`
(node `lem-pe-coefficient-comparison-representables`).

Zero holes remain in the item's module. Zero holes are added elsewhere; zero
statements are split off. The private isomorphism is fully constructed and
proved. The proof uses the existing, still-unproved theorem
`AlgebraicGeometry.Scheme.proEtaleClassicalSheavesImage`
(node `det-pe-classical-sheaves-image`), without changing it or its dependencies.
This is a proof from an existing declared dependency, not an axiom-free proof
of that dependency or of the whole target closure.

Edge cases need no extra hypothesis: the same argument includes empty affine
schemes, non-separated etale targets, and arbitrary small cofiltered categories
in universe u+1. The index is never shrunk, and the independent coefficient
universe v is retained by explicit lifts.

## No longer needed

The item's former proof dependencies
`lem-weil-pbc-finite-presentation-map-limit-factorization` (Mathlib leaf) and
`lem-weil-pbc-finite-type-hom-colimit-qc-equality`
(`Sheaf.AlgebraicGeometry.FiniteTypeHomColimitQcEquality`) are not used directly
by this proof. Their edges are removed from this node. The latter is a module
sheaf theorem and is not needed to show equality of scheme morphisms.

No original Lean import is removed. No existing module is withdrawn, and no
source-library declaration is changed. Other consumers may still need the old
dependencies; this delivery claims only their removal from this item's plan.

## Where the brief, the DAG or earlier work was wrong

The original DAG cited a module-sheaf eventual-equality theorem for an equality
of scheme morphisms; its signature does not supply that step. The cited Mathlib
scheme factorization theorem also has an index in Type u for Scheme.{u}, while
this item's index is in Type (u+1).

The existing classical-sheaf essential-image characterization already states
continuity for the original larger index universe. Applying it to a representable
avoids both mismatches and requires no new geometric factorization lemma. The
categorical comparison of representables is proved in the delivered file.

## Second reading by C5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
