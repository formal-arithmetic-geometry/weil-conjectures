## What changed

Proved both original theorem holes in `Sheaf.Paper.RestrictionDirectImage`.
`finiteCoefficientBoundedConstructible_isTriangulated` specializes the existing
closure theorem from `Sheaf.AlgebraicGeometry.PullbackBoundedConstructible`.
`restrictionDirectImage` now proves preservation of the recorded full essential
image, triangulatedness of the lifted functor, and the sharp interval `[a,b+c]`.

All new helper theorems are private and fully proved in the item module. They
identify the essential-image condition with bounded constructible etale-origin
cohomology and prove the constructible-only amplitude induction. Constructibility
uses the existing source-library etale comparison theorem. Exact comparison and
`DerivedCategory.prop_of_bounded` avoid the separate intrinsic-ring encoding.
The ordinary derived-functor compatibility theorem supplies negative vanishing.
The node proof and dependencies now describe this implementation.

Validation: the item compiles via `lcompile.py` in approximately four seconds,
with no warnings. The proof treats empty cohomological intervals by zero objects;
the induction also includes width zero. No nonzero-ring or nonempty-scheme
assumption is introduced. Existing signatures, definitions, public imports and
the unit route are preserved. No change record or consumer adaptation is needed.

## Proved and sorry left

Closed 2 of 2 original holes, both on node
`prop-weil-pbc-restriction-direct-image`:

- `AlgebraicGeometry.ProEtale.finiteCoefficientBoundedConstructible_isTriangulated`.
- `AlgebraicGeometry.ProEtale.restrictionDirectImage`.

Zero holes remain in the item. Zero new holes or split-off nodes were added.
These are proofs from existing declared dependencies, including the still-open
triangulated-closure theorem in `PullbackBoundedConstructible`; they do not claim
that the transitive axiom closure is already free of the dependencies' sorries.

## No longer needed

Removed proof imports:

- `Sheaf.CategoryTheory.RingedSiteGrothendieckAbelian`.
- `Mathlib.Algebra.Category.Grp.AB`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits`.
- `Mathlib.Algebra.Category.Ring.Limits`.
- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic`.
- `Sheaf.CategoryTheory.ExtensionByZeroPresheaf`.
- `Sheaf.Paper.FiniteRingConstructibleSheafOrigin`.
- `Mathlib.CategoryTheory.ObjectProperty.FullSubcategory`.
- `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`.
- `Mathlib.Algebra.Homology.Embedding.CochainComplex`.
- `Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT`.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`.
- `Sheaf.CategoryTheory.RingedSiteModules`.
- `Sheaf.Paper.FiniteRingConstructibleDerivedOrigin`.
- `Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated`.
- `WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian`.

Removed direct proof dependencies (other modules may still use them):

- `prop-weil-pbc-proetale-constant-ring-map`.
- `lem-pur-ringed-site-grothendieck-abelian`.
- `def-weil-sheaf-of-modules-category`.
- `lem-weil-pbc-derived-functor-negative-vanishing`.
- `lem-weil-pbc-finite-ring-constructible-derived-origin`.
- `lem-weil-pbc-finite-ring-constructible-sheaf-origin`.
- `lem-weil-pbc-truncation-cohomology`.
- `lem-weil-proetale-dbc-triangulated`.

The intrinsic finite-ring sheaf and derived-origin bridges, constant-ring-map
comparison, and intrinsic bounded-constructible triangulation are unnecessary:
the proof stays in the recorded finite coefficient module category. Enough
injectives are transported along its existing realization equivalence, so the
ringed-site generator construction is unnecessary here. Derived truncation API
replaces the separate cochain truncation-cohomology statement. The concrete
unbounded negative-vanishing corollary replaces the bounded-below wrapper.

The existing three `tool_uses` entries are retained: ordinary derived-functor
compatibility, derived truncation triangles and long exact cohomology are used.
No unit statement or unit proof step is bypassed, and no library module is deleted.

## Where the brief, the DAG or earlier work was wrong

The retained report described only one closed hole; it has been superseded by a
complete proof of both. The earlier retained route correctly suggested finite
canonical truncation, but its intrinsic coefficient bridges are avoidable. The
current blueprint's finite-filtration constructibility and amplitude argument
is implemented by canonical truncation induction, including its zero-object edge
case. FIN is applied only to constructible sheaves, never to arbitrary sheaves.

## Second reading by Y5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
