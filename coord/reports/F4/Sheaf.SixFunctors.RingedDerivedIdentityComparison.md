## What changed

Proved `CategoryTheory.RingedDerivedComparisons.identityComparison_exists` in
`Sheaf.SixFunctors.RingedDerivedIdentityComparison`, with the original theorem
signature and every field of `IdentityCore` unchanged. All supporting declarations
added to the module are private and proved or are explicit constructions.

The ordinary comparison comes from the morphism's module-linear Hom equivalence:
transport underlying sections across the geometric identity, prove linearity using
the structural-ring-map hypothesis, and take the adjunction mate. Its scalar
insertion equation is proved through the geometric Hom bijection.

Right-derived uniqueness applied to the componentwise ordinary right mate gives
the right comparison with its eta formula on every complex. Its left adjunction
mate has the required flat-term K-flat model formula: the supplied canonical
transpose equation extends from K-injective targets to arbitrary complexes by a
K-injective resolution and naturality.

For tensor compatibility, first prove the ordinary equation on pure sections,
then check every bidegree inclusion of the direct-sum total. Combine that chain
identity with the canonical derived tensor representative equation. The total of
the two flat-term K-flat representatives is flat-term K-flat by the existing
total-tensor theorem, using the existing flatness comparison. Naturality and
K-flat resolutions extend the result to all derived objects. The monoidal
left-unit identity and cancellation then imply unit compatibility.

Added private proof imports for Cartesian monoidal sheaves, right-derived
uniqueness, pure tensor sections, K-flat total tensor models, the comparison of
site and categorical flatness, and independent-coefficient K-flat resolutions.
The public import is unchanged. Updated the node's proof, proof dependencies and
proof origin to record this argument; no statement, definition interface, target,
source-library module, consumer, or unit route changes.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.RingedDerivedComparisons.identityComparison_exists`
(node `lem-sfb-ringed-derived-identity-comparison`).

Original holes: 1. Closed: 1. Added: 0. Split off: 0. Remaining in the item: 0.
No other Lean module is changed or added. Existing stated dependencies retain
their proofs; this delivery does not introduce an admitted intermediate result.

## No longer needed

Removed the private imports `Sheaf.CategoryTheory.GeometricModuleTransport`,
`WeilConjectures.Algebra.Homology.KFlatResolution`, and
`Mathlib.Algebra.Homology.DerivedCategory.Fractions`.

Removed these dependencies from this node's proof route:

- `lem-weil-pbc-geometric-module-transport`: the supplied module-linear Hom
  equivalence constructs the ordinary comparison directly.
- `lem-weil-pbc-ringed-topoi-derived-pullback`: the left comparison is obtained
  as the mate of right-derived uniqueness for the already supplied derived
  functors, rather than constructing derived pullback anew.
- `lem-pc-right-fraction-representation`: K-injective naturality and the right
  derived universal property provide the normalization on every complex, and
  K-flat resolution isomorphisms suffice for tensor naturality.

The K-flat resolution node remains needed through its current
independent-coefficient attachment. No module is withdrawn: the removed direct
proof dependencies can still be needed by other nodes, or transitively by the
canonical tensor comparison. No claim of global pruning is made.

## Where the brief, the DAG or earlier work was wrong

No false or unusable statement was found. The previous proof plan unnecessarily
introduced fractions and localized the left comparison first. Starting with the
universal right-derived comparison fixes its eta formula on all complexes before
taking the left mate, so fractions are unnecessary. The unit equation also
follows formally from tensor compatibility of the invertible comparison; it
does not need a separate coefficient-unit representative calculation.

The existing proof in `RingedDerivedCompositionComparison` provided useful
patterns for module-linear transport, K-injective naturality, and the formal
unit argument. That module imports this item and is not imported here; the
private helpers needed for the identity case are proved in this module.

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
