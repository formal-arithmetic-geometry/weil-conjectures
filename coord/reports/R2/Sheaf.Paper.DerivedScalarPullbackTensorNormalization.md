## What changed

The original statement of `scalarPullback_tensor_normalization` is unchanged.
Its proof now cancels the one-sided scalar tensor coordinates on a flat-term
K-flat representative, compares two routes to ordinary total tensor, and
transports the equality to every derived object by naturality.

`Sheaf.Paper.ScalarTensorOrdinaryPullback` constructs the scalar counit
coordinates, the coefficient complex pullback, and the ordinary total route.
`Sheaf.Paper.ScalarTensorOneSidedPullback` then proves
`tensorScalar_oneSided_pullback`, the geometric tensor half,
from the specified representative square and `IsDerivedTensor`. The proof
resolves the coefficient complex, uses both representative normalization
identities, and cancels the localized quasi-isomorphism. The new definitions
are actual composites; none chooses data from an existence theorem. Their
implementations are marked irreducible to keep elaboration from expanding
the underlying total-complex constructions; the proofs unfold them explicitly
where their formulas are needed.

`Sheaf.Paper.ScalarMateOrdinaryTensorRoute` states the remaining scalar-counit
normalization on a K-flat complex. The new obligation has no derived tensor
model, no canonical geometric derived tensor comparison, and no arbitrary
derived input. The original theorem combines this equation with the proved
tensor equation by real cancellation and naturality arguments.

Proof imports of the original item now include both route modules,
independent-coefficient K-flat resolution and its flatness comparison.
No other existing Lean module or definition is changed. Remote compilation
passed for all four modules, without development options or warnings. The
last check of the assigned module completed in 15.3 seconds.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.DerivedScalarMate.scalarPullback_tensor_normalization`
(node `lem-sfb-derived-scalar-pullback-tensor-normalization`) by decomposition.

Proved
`AlgebraicGeometry.Scheme.DerivedScalarMate.tensorScalar_oneSided_pullback`
(node `lem-sfb-scalar-tensor-one-sided-pullback`) and its private
representative-normalization helper. Also proved
`AlgebraicGeometry.Scheme.DerivedScalarMate.tensorScalarOrdinaryPullback_naturality`
(node `lem-sfb-scalar-tensor-ordinary-pullback`).

Added one hole:
`AlgebraicGeometry.Scheme.DerivedScalarMate.scalarMate_ordinary_tensor_route`
(node `lem-sfb-scalar-mate-ordinary-tensor-route`). This is the scalar-adjunction
and ordinary balanced tensor portion of the argument, not the original
statement under another name. Its source and full proof in words are in the
new module. The assigned module has zero holes; the delivery has one hole.
One original hole closed, one new hole added: net zero, a decomposition.
Existing imported holes are not claimed as proved by this delivery.

## No longer needed

No original import was removed: `DerivedScalarMateData` remains public.
No module is withdrawn and no globally unused module is claimed.

The original item's direct proof dependencies
`lem-weil-pbc-ring-sheaf-change-adjunction` and
`lem-sfb-kflat-scalar-comparison-normalization` move to the scalar ordinary
route node; they remain needed there. They are not globally pruned.
`lem-weil-pbc-site-derived-tensor-descent` is not used directly: the proved
canonical tensor pullback and its descent-data naturality supply the exact
representative square needed. The dependency remains transitively in that
existing construction, so no global pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was found false. The planned one-sided computation
needed an explicit interface: `IsDerivedTensor` is normalized using a
resolution of the coefficient complex, whereas the requested equality has
that coefficient fixed in degree zero. The tensor helper supplies that
interface and carries out the resolution cancellation, including nonflat B.

The tensor/scalar route equality was not already a consequence of the
abstract mate API alone. The generic K-flat scalar comparison theorem uses
equal site object, morphism and coefficient universe levels; applying it to
these fixed pro-etale models requires transport and identification of their
universal scalar counits, followed by the ordinary tensor calculation. The remaining scalar ordinary route records its
precise scalar-counit and localization equation, separated from the tensor
representative normalization that is now proved. Empty schemes and zero
ring sheaves require no extra assumptions; the equations are composites of
canonical morphisms and the balanced-generator argument also covers them.
No unit route or target statement is bypassed.

## New nodes

`lem-sfb-scalar-tensor-ordinary-pullback` supplies explicit scalar coordinate
maps and proves naturality of the ordinary total comparison in
`Sheaf.Paper.ScalarTensorOrdinaryPullback`. Separating this self-contained
calculation keeps each compilation within the required per-file limit after
adding explicit endpoint types and controlling unfolding of the new maps.

`lem-sfb-scalar-tensor-one-sided-pullback` is the proved tensor representative
calculation in `Sheaf.Paper.ScalarTensorOneSidedPullback`. It uses the explicit scalar coordinates and ordinary coefficient map of
`ScalarTensorOrdinaryPullback`.

`lem-sfb-scalar-mate-ordinary-tensor-route` is the remaining scalar-adjunction
calculation in `Sheaf.Paper.ScalarMateOrdinaryTensorRoute`. It is strictly the
scalar/ordinary part on a K-flat complex, without derived tensor models.
No change record is needed because no existing definition or statement changes.

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
