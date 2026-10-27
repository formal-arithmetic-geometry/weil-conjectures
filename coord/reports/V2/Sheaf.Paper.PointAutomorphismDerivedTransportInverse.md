## What changed

Filled the four original theorem bodies of
`Sheaf.Paper.PointAutomorphismDerivedTransportInverse` without changing any existing
signature, definition, public import, or docstring. Exact sections use the existing
independent-universe ring-retraction argument from PointAutomorphismRestrictionNatural.
The sections isomorphism inverts the actual restriction map, identifies its inverse
with restriction along the inverse site arrow, and descends through the exact-functor
localization comparisons, with uniqueness checked on all representatives.

Finite transport is reduced to the new, strictly smaller chain-comparison
invertibility theorem in `Sheaf.AlgebraicGeometry.ProEtale.FiniteComparisonIsomorphism`.
The parent supplies the comparison's naturality, inverse scalar formula, localization,
and composition with derived sections. Integral transport uses the existing comparison
naturality/normalization package and actual reconstruction-unit invertibility, then
constructs both inverse transports and proves their naturality by cancellation.

Updated the item's DAG proof and dependencies to this implementation.
The assigned module compiled cleanly in 43.7 seconds. The general derived-functor
compatibility is proved with abstract functors before specialization, avoiding expensive
unfolding of concrete sheaf functors.

## Proved and sorry left

Original holes: 4. Closed original holes: 4. Added holes: 1. Net reduction: 3.

- `AlgebraicGeometry.ProEtale.pointRestrictionSections_exact`: proved.
- `AlgebraicGeometry.ProEtale.point_automorphism_sections_inverse`: proved.
- `AlgebraicGeometry.ProEtale.point_automorphism_finite_transport_inverse`: decomposition
  through the finite chain-comparison invertibility lemma; the combining proof is complete.
- `AlgebraicGeometry.ProEtale.point_automorphism_integral_transport_inverse`: proved from
  existing declared dependencies, including the sections theorem in this file.

The only new sorry is
`AlgebraicGeometry.ProEtale.inverseImageFiniteComparisonComplex_isIso`, node
`lem-weil-finite-comparison-complex-isomorphism`. It asserts invertibility of the
specified finite comparison on complexes; it does not assert the inverse scalar
formula, naturality, derived comparison, or sections transport proved by the parent.
There are no sorries left in the assigned module and no holes in definitions.

## No longer needed

Removed the private proof import
`Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIso` from the assigned module:
its finite scalar-extension identification is confined to the new sublemma's proof plan.
The new node still cites the scalar-extension lemma, so it remains a mathematical
dependency of the remaining proof; no global pruning is claimed.
Removed the obsolete parent tool approvals
`lem-weil-sheaf-scalar-extension-ring-iso` and
`lem-weil-isomorphism-derived-pullback-comparison-normalization`: the former is now
a dependency of the new finite sublemma, and the latter is used through the existing
comparison-naturality package.

The parent no longer invokes
`lem-weil-isomorphism-derived-pullback-comparison-normalization` directly; the existing
`lem-weil-isomorphism-comparison-natural` packages precisely this normalization on all
ambient objects, and actual reconstruction maps handle complete inputs. Its public
import is retained because existing interfaces are unchanged. No module is withdrawn
and no unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original public import PointProEtaleSectionsExact specializes the coefficient
universe to the point universe. The existing private exactness proof in
PointAutomorphismRestrictionNatural already handles the independent universes required
here; its argument was reused rather than adding a hypothesis or a new exactness hole.
The current node attachment has since moved to PointProEtaleSectionsExactOfUniverses,
which independently formalizes the same argument; no defect in that new statement is claimed.

The finite comparison's existing characterization and the general scalar-extension
isomorphism do not by themselves provide a Lean identification with the chosen
constant-coefficient pullback adjunction. The new sublemma isolates precisely that
identification, with the original step 3 argument written out in its docstring and node.

## New nodes

`lem-weil-finite-comparison-complex-isomorphism`:
`Sheaf.AlgebraicGeometry.ProEtale.FiniteComparisonIsomorphism`, declaring
`AlgebraicGeometry.ProEtale.inverseImageFiniteComparisonComplex_isIso`.
Source: original node step 3, Stacks 03D2/03D6/00WX. The proof plan uses the site
equivalence, scalar-extension multiplication and its tensor-unit inverse, uniqueness
of left adjoints preserving the actual unit, and the recorded sectionwise uniqueness
of the comparison. Searches via LeanSearch, LeanFinder, Loogle, Mathlib/library grep,
and the blueprint found no declaration of this specified comparison's invertibility.
Edge checks: zero objects and arbitrary unbounded complexes are covered degreewise;
no flatness, constructibility or equality of coefficient/site universes is needed.

## Second reading by V2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
