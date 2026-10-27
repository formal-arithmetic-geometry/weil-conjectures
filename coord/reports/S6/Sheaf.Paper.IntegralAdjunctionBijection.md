## What changed

Replaced the hole in `integral_adjunction_bijection` by explicit categorical assembly.
Mathlib `Adjunction.restrictFullyFaithful` supplies the adjunction and its exact Hom
chain, mapped unit, and mapped counit. Naturality of finite evaluation comparisons
and cancellation of the reconstruction comparison isomorphisms yield the finite
unit/counit equations. The recorded reconstruction identities give the derived-limit
equations. The actual completeness unit and tower purity map are isomorphisms,
so functoriality proves the specified purity realization for every source comparison.

Two interface steps remain separate: the reconstruction package for the specified
NX/NY presentations, and the ordered Tate tensor/shift comparison. The existing
`twistedPullbackReductionTower` is used directly for coherent reduction and source
constructibility. No existing statement, definition, or public import was changed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.SpIntegralAdjunction.integral_adjunction_bijection`
(node `det-sp-integral-adjunction-bijection`) by decomposition, not a complete
sorry-free proof of its mathematical inputs.

Added two holes, each the entire proof of one public theorem:

- `AlgebraicGeometry.ProEtale.SpIntegralAdjunction.integralAdjunctionReconstruction`
  (`lem-sp-integral-adjunction-reconstruction-package`).
- `AlgebraicGeometry.ProEtale.SpIntegralAdjunction.integralAdjunctionSourceComparison`
  (`lem-sp-integral-adjunction-ordered-source`).

The assigned module has zero direct holes after the change; the delivery has two.
Original holes closed: 1. New holes: 2. Net: -1. All three Lean modules compiled
through lcompile.py; the main module completed in 19.2 seconds without warnings.

## No longer needed

Removed the direct proof import `Sheaf.Paper.IntegralReconstructionComparisons` from
the assigned module: its interface conversion is isolated in
`IntegralAdjunctionReconstruction`, which imports that existing module. Thus the
existing reconstruction node and its dependencies remain needed transitively;
no existing module is withdrawn or claimed globally pruned. The two original
approved tools for integral constructibility/twisting remain available via the
existing coherent reduction theorem. No public import was removed.

## Where the brief, the DAG or earlier work was wrong

The declared reconstruction theorem returns `IntegralReconstructionComparisons.Comparisons`
with existential limit presentations, whereas the assigned theorem extends
`SpIntegralAdjunction.Reconstruction` for the specified normalized equivalences NX,NY.
An interface assembly is necessary; the former cannot simply be supplied as the latter.
The coherent twisted pullback theorem ends in `finiteSource`, while the purity theorem
uses the ordered product of shifted degree-one Tate lines. The new second lemma states
only that presentation comparison, with explicit invertibility of ell on X,Y,
supplied by the coherent reduction theorem,
and no smoothness or purity assumption.

Edge checks: d=0 uses the coefficient unitor; d=1 identifies the single shifted line;
d=2 uses associativity and two even shifts, so no odd permutation sign appears.
The zero object and identity morphism cases retain all comparisons. Reconstruction
uses actual NX/NY units and counits and therefore accommodates a different adjunction
normalization on the same two functors. No equality is inferred from finite evaluations.

## New nodes

`lem-sp-integral-adjunction-reconstruction-package` isolates Normalization and the
canonical reconstruction comparisons of Bijections, using the existing reconstruction
and compactification-limit results. It asserts no integral adjunction or purity.

`lem-sp-integral-adjunction-ordered-source` isolates the tensor/shift reassociation of
the Purity paragraph. It compares `finiteSource` to the ordered-line source and does
not assert source constructibility, gamma invertibility, or integral realization.

Searches used LeanFinder, Loogle, LeanSearch, and rg over Mathlib and both library roots.
The categorical assembly is in Mathlib; neither interface statement was found as an
existing Lean declaration. No change record is needed for the unchanged existing API.

## Second reading by S6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
