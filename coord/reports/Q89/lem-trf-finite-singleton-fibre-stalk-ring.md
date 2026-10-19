## Worker report

The module `Sheaf.TraceFormula.FiniteSingletonFibreStalkRing` states the two clauses of
Stacks Tag 05B8, parts (2) and (3), for a finite scheme morphism with singleton fibre.
The finite clause is rendered by `RingHom.Finite (p.stalkMap t).hom`. The additional
locally-finite-presentation hypothesis is rendered by `LocallyOfFinitePresentation p`,
and its conclusion is an explicit finite polynomial algebra presentation using
`Algebra.FinitePresentation`'s quotient form, expressed as a nonempty `AlgEquiv`.
The singleton-fibre hypothesis is the equality of inverse image sets shown in the
statement. All scheme, point, and morphism objects are explicit and universes are bound.

Dependencies used: `AlgebraicGeometry.IsFinite` from
`Mathlib.AlgebraicGeometry.Morphisms.Finite`; `PresheafOfModules.moduleStalkFunctor`
is not needed in the final statement because scheme stalks are directly
`U.presheaf.stalk` and `T.presheaf.stalk`; `AlgebraicGeometry.LocallyOfFinitePresentation`
from `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`; and
`AlgebraicGeometry.LocallyRingedSpace.Hom`/`Scheme.Hom.stalkMap` from
`Mathlib.AlgebraicGeometry.Stalk` and the Mathlib scheme definitions.

Edge cases checked: the finite presentation indices are natural numbers and may be zero;
the formulation permits empty fibres only when the displayed singleton equality permits it,
and permits zero stalk rings and zero-variable/zero-relation presentations. The stalk map
is the actual canonical scheme stalk map.

Searches made: `msearch.py` LeanFinder/LeanSearch/Loogle queries for singleton-fibre stalk
finiteness and finite presentation returned no exact theorem; grep over Mathlib and
`WeilConjectures` found only general stalk-map and localization infrastructure, with no
statement of this lemma. Existing DAG dependency records were read and their declarations
checked in the recorded Mathlib/source files.

## Second reading by Q89

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
