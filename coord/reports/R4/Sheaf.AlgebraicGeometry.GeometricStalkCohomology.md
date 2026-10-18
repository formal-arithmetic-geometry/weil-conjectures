## What changed

Proved `AlgebraicGeometry.Etale.nonempty_geometricStalk_cohomology_iso` in
`Sheaf.AlgebraicGeometry.GeometricStalkCohomology`, preserving its signature and public imports.
Compose the inverse component of `upperStarCompUliftSheafFiberIso` at the cohomology sheaf
with the identity-point fibre applied to `mapDerivedCategoryHomologyFunctorIso` for pullback.
The latter is a proved upstream comparison for exact functors on unbounded derived categories.
Added its module as a direct proof import and updated the existing node's proof route.

The final module compiled through `lcompile.py` in 2.5 seconds without diagnostics.
An additional compile with `#print axioms` reported exactly `propext`, `Classical.choice`,
and `Quot.sound`. The temporary print command was removed. No new definitions or statements.
The comparisons are natural, work for every integer degree and every unbounded object,
and require no vanishing, boundedness, or nonzero hypothesis; zero objects are included.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.nonempty_geometricStalk_cohomology_iso`
(node `lem-kun-stalks-of-cohomology`).

Zero holes remain in the item; zero holes added; zero split-offs.
The axiom audit also confirms the proof has no transitive sorry dependency.

## No longer needed

Removed proof imports:
- `Sheaf.AlgebraicGeometry.GeometricStalkAsPullback`.
- `Mathlib.CategoryTheory.Sites.Point.Skyscraper`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories` (already re-exported by the retained
  public import `Sheaf.AlgebraicGeometry.DerivedCategories`).

Removed proof dependencies `lem-kun-stalk-as-pullback` and
`prop-weil-pbc-geometric-stalks-exact`. The argument uses exactness of inverse image and
its homology comparison, followed by the underived stalk comparison, so it needs neither
the derived global-sections comparison of `GeometricStalkAsPullback` nor exactness of stalks.
Consequently the proof does not need the dependency branches
`Sheaf.AlgebraicGeometry.GeometricPointPullbackStalk` and
`Sheaf.AlgebraicGeometry.GeometricPointCanonicalGerm` brought in by that removed import.
These are pruned from this argument; other parents may still need them.
The declared dependency `def-weil-pbc-derived-categories` remains used.
The unit record has empty realized statement/steps, so no mandated unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No incorrect statement was found. The DAG plan is longer than necessary for the actual
Lean statement: exactness of pullback already supplies the cohomology comparison before
applying the fibre functor. The complete proof is a composite of two existing isomorphisms,
so no new localization or cycle/boundary lemmas are required. The updated proof dependencies
record the inverse-image interface and the existing underived stalk comparison instead.

## Second reading by R4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
