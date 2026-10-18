## What changed

Proved `AlgebraicGeometry.Etale.properOpenSectionGeometry` in
`Sheaf.AlgebraicGeometry.ProperOpenComparison`, with its signature unchanged.
The projection identities give the open immersion by `IsOpenImmersion.of_comp`.
Proper base change makes the second projection separated; its section is a closed
immersion by `IsClosedImmersion.of_comp`, hence has closed image. The Cartesian
square follows from `IsPullback.of_horiz_isIso_mono`.

The three existing definition bodies and all declaration signatures are unchanged.
Updated `def-weil-pbc-proper-open-comparison`'s proof route and proof dependencies.
Added the proof-only import `Mathlib.AlgebraicGeometry.Morphisms.Separated`.
Change record: `coord/changes/F1-proper-open-comparison-import-pruning.md`.

Validation: the module compiles without warnings; `#print axioms` for the completed
geometry theorem reports exactly `propext`, `Classical.choice`, and `Quot.sound`.
All six direct importers compile unchanged against the modified module:
`ProperOpenSection`, `ProperOpenComparisonComposition`, `CompactSupportFiniteTorsion`,
`ProperOpenInterchangeCoherence`, `ProperOpenComparisonIso`, and
`EtaleCompactSupportComparisons` (all in `Sheaf.AlgebraicGeometry`).
Their temporary, unchanged consumer copies were removed from the delivery.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.properOpenSectionGeometry`
(node `def-weil-pbc-proper-open-comparison`).
Added 0 holes. Split off 0 statements. Remaining holes in the delivered module: 0.
This is a proof, not a decomposition; the completed theorem uses no sorry axiom.
The unchanged derived constructions still depend on their previously stated lemmas.

## No longer needed

Removed these imports from the assigned module:

- `Sheaf.AlgebraicGeometry.OpenSectionClopen` (formerly public): the needed closed
  image follows directly from Mathlib's separated-composite lemma. The stronger
  complementary coproduct statement is unused.
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`: no declaration or instance
  from this import is needed by the existing constructions or the completed proof.
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`: the descended derived
  adjunction is already supplied by the retained derived open-immersion module.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`: the retained
  APIs already supply all derived functor and bounded-below constructions used here.

Accordingly, this module does not directly need nodes
`lem-weil-pbc-open-section-clopen`, `def-cbc-open-immersion-square`,
`prop-weil-pbc-inverse-image-modules-exact`,
`lem-weil-pbc-termwise-adjunction-homotopy`,
`lem-weil-pbc-localization-universal-property`,
`lem-weil-pbc-extension-by-zero-exact`, and
`lem-weil-pbc-exact-functor-bounded-below` as separate proof steps.
The derived API may still depend on the exactness/localization infrastructure.
These are local dependency prunings, not claims that all these modules leave the
whole target closure: in particular `ProperOpenSection` still imports
`OpenSectionClopen` directly. No existing module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The geometry docstring used the stronger clopen-section
lemma; its closed-image clause is already proved by Mathlib's
`IsClosedImmersion.of_comp`. The definition node had an empty proof plan despite
containing the geometry proof obligation; the delivered route records the proof
and retains the prescribed canonical comparison construction. The unit record has
no realized steps, so no fixed unit step is bypassed. No statement or definition is
weakened, and no new nodes or forced adaptations are needed.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
