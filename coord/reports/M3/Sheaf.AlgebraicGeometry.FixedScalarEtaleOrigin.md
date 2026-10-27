## What changed

Proved `AlgebraicGeometry.Scheme.fixedScalar_etaleOrigin` with its original statement.
Added four supporting modules: `FixedScalarEtaleModel` constructs the explicit exact
scalar equivalences and their localization factors; `FixedScalarOrdinaryComparison`
reuses the existing general-ring ordinary comparison square; `FixedScalarEtaleConstructibleSheaf`
identifies constructibility in the two scalar presentations; `CoefficientFieldTorBounds`
proves the same Tor interval from bounded cohomology over a constant field.
All new imports of the existing item are private proof imports. Existing definitions,
targets, public imports and declaration signatures are unchanged. No source-library
module is edited.

The constructibility proof reuses general-ring private helpers through `import all`.
It identifies finite constant module models with finitely generated geometric stalks,
without assuming that the coefficient ring is finite as a set. Nonempty trivializing
members give the reverse implication; removing empty members preserves joint surjectivity,
including the empty scheme. The Tor proof uses the standard derived t-structure bounded
representative, constant-field flatness, and the coefficient bounded-flat-model criterion.

## Proved and sorry left

Closed the one original hole: `AlgebraicGeometry.Scheme.fixedScalar_etaleOrigin`
(`lem-sfb-fixed-scalar-etale-origin`). Added zero holes and split off zero obligations.
The new theorems `fixedScalarEtale_constructible_sheaf`, `fixedScalar_ordinary_comparison`
and `CategoryTheory.coefficientFieldTorBounds` have complete proofs. The new scalar
presentation functors, equivalences, additive instances and localization factors are
explicit constructions with complete proofs. There is no `sorry` in the delivery.
Existing imported proof obligations are unchanged.

## No longer needed

The item had no private proof-dependency imports to remove. Removed the unused
`ConstructibleProEtaleComparisonData` import from the new model module; the required
small-site definitions already come through `FixedScalarComplexModel`. The proposed direct dependency
`lem-sfb-constant-module-ordinary-realization` / `Sheaf.CategoryTheory.ConstantModuleOrdinaryRealization`
is replaced by the existing general-ring comparison square and equivalence cancellation.
`lem-sfb-noetherian-global-constructibility` is no longer a direct dependency of the item:
the constructibility bridge reuses the existing coefficient global-stratification helper,
which still imports and uses `NoetherianGlobalConstructibility`. Thus that module is retained
as a transitive dependency, not pruned.
`lem-sfb-constant-scalar-restriction-tensor` is no longer a direct dependency of the origin
proof or its Tor argument; its scalar restriction equivalence remains needed by the
explicit model module and is already publicly imported by `FixedScalarComplexModel`.
`def-sfb-fixed-scalar-complex-model` remains a statement dependency, as before.
No module is withdrawn and no unit realization is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original proof plan is valid, but the large ordinary geometric realization interface
is unnecessary. Despite its name, `finiteComparisonModelPullbackSquare` assumes only
`CommRing`, so it already gives the required ordinary comparison. The finite-comparison
presentation proof also contains general-ring site and stratification helpers; only its
final conversion to finite underlying sets needs finite coefficients. The new bridge
retains module finite generation instead, which is the actual `IsFiniteSheaf` predicate.
The unit's residue-field argument and fixed-scalar model are preserved. The existing
`constant_field_tor_bounds` has the pro-etale model topology fixed in its signature, so
it does not apply to the etale antecedent. The new generic small-site lemma supplies that
missing specialization using the same constant-field flatness input.

## New nodes

`def-sfb-fixed-scalar-etale-model`: explicit etale and pro-etale scalar equivalences,
termwise functor, derived functor and canonical localization factors, all constructed.

`lem-sfb-fixed-scalar-ordinary-comparison`: the ordinary sheaf comparison square obtained
from the existing square and equivalence units, proved over an arbitrary commutative ring.

`lem-sfb-fixed-scalar-etale-constructible-sheaf`: constructibility equivalence over a
Noetherian commutative ring on a Noetherian scheme, with a complete finite-model/stalk proof.

`lem-sfb-coefficient-field-tor-bounds`: bounded constant-field derived objects have the
same coefficient-model Tor interval, proved using a bounded flat representative.

Change record: `coord/changes/M3-fixed-scalar-etale-proof-helpers.md`.

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
