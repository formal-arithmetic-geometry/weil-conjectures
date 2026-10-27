## What changed

Replaced the proof hole of `CategoryTheory.CondensedBar.nonempty_injectiveRows` by
an injective-extension argument. For each profinite parameter the recorded exact
homogeneous tensor bar is sent to an exact Hom row using Mathlib's
`ShortComplex.Exact.descToInjective` and its composition identity. The normalized
coordinate equivalences transport the resulting preimages back to the existing
bar sections. Epimorphic augmentation gives sectionwise injectivity; sectionwise
exactness is promoted through abelian presheaves, exact sheafification, and the
exact faithful internal-module forgetful functor. The degree-zero formula is
proved separately from the two recorded bar face formulas.

Added `Sheaf.CategoryTheory.CondensedBarHomCoordinates` for the strictly smaller
coordinate construction, independently of injectivity. It asserts no exactness.
The existing definitions `parameterGenerator` and `parameterPullback` stay
verbatim in the item. The new coordinate specification uses their formulas
explicitly and is imported privately for the proof. All existing declarations and
public imports retain their signatures and visibility. No existing module besides
the item is changed.

## Proved and sorry left

Closed the original hole in
`CategoryTheory.CondensedBar.nonempty_injectiveRows`
(`lem-sfb-condensed-injective-bar-rows`). Added one hole:
`CategoryTheory.CondensedBar.nonempty_homCoordinates`
(`lem-sfb-condensed-bar-hom-coordinates`). This is a decomposition: one original
hole closed and one strictly smaller coordinate-construction hole added, for a
net change of zero holes. The item has zero remaining holes; the added module has
one. The injective extension, augmented monicity, sectionwise and internal
exactness, and degree-zero face calculation have complete Lean proofs. The injective Hom argument is factored into a
private generic lemma for an exact short complex in any abelian category.

Final server validation: `lcompile.py --all` passed without warnings for
`Sheaf.CategoryTheory.CondensedBarHomCoordinates` (7.9 seconds), the item (16.9
seconds), and its unchanged direct importer
`Sheaf.CategoryTheory.CondensedProductBarResolutionModel` (49.7 seconds). The
unchanged importer copy was removed from the sandbox after this check; it is not
part of the delivery. Every delivered file and the checked consumer is under the
60-second file limit.

The remaining theorem has its source and a complete generator-level argument in
its docstring and node. Its invariant-section equivalence and augmentation square
are the degree-minus-one part of the coordinate construction. No data definition
contains a hole or is selected from a mere existence theorem.

## No longer needed

No modules or nodes are pruned. All original mathematical dependencies remain
needed, directly or through the coordinate-construction node. Free linearization
and the invariants/free adjunction are used by that node rather than directly by
the completed exactness argument. No source-library declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The planned exactness argument has an existing Mathlib implementation:
`ShortComplex.Exact.descToInjective`. Thus there is no need to rebuild the
image/coimage factorization and injective extension. The homogeneous coordinate
construction is not supplied by the existing free-tensor comparison declaration;
it is separated as the genuine coordinate-only part of the argument.

Searches found ordinary `groupCohomology.inhomogeneousCochainsIso` but no internal
condensed analogue. The existing `InternalHomogeneousCochainCoordinates` supplies
coordinates on a specified homogeneous subcomplex for a whole family of profinite
groups, not the free-parametrized-Hom comparison with the given resolution, and
cannot replace the missing bridge. The unit's route is preserved.

Edge cases checked in the remaining construction: degree zero, the trivial group,
the zero coefficient ring, and the empty profinite parameter. The construction
uses natural generalized generators and local tensor extension; it never assumes
global sections form a free module or evaluation is exact on arbitrary sheaves.
All noncommutative group ratios keep their specified order.

## New nodes

`lem-sfb-condensed-bar-hom-coordinates` records the normalized additive Hom
identifications, naturality, differential compatibility, and invariant augmentation
square for arbitrary equivariant coefficients. It omits all injectivity and
exactness assertions, which the original module proves. One new module, one new
statement node, no shared definition or statement correction, and no forced
adaptations or change records.

## Second reading by V4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
