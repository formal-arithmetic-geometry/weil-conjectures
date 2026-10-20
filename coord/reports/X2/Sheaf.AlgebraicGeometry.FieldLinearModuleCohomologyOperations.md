## What changed

Retired Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations in favor of
WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations. This is the
kind=retire item recorded in coord/retire-items.tsv. Changed the import in all seven
remaining direct consumers and moved all three attached DAG lean records to the twin.
No upstream file, public signature or mathematical construction changed.
Wrapped two pre-existing long local-instance declarations without changing their terms.
CanonicalCoherentEtaleComparison also uses local irreducibility for existing coefficient
and cohomology definitions during normalization, restoring transparency for its proof
and later Ext conversions. Its private component-equality calculation now infers the
mapped equality directly and explicitly unfolds CoherentEtale.Coeff when applying it.
This fixes a 60-second timeout; the actual delivered module compiled in 33.1 seconds.
Public data terms and global attributes remain unchanged.

Change record: coord/changes/X2-retire-field-linear-module-cohomology-operations.md.
Validation: lcompile.py --all compiled all seven consumers (2.3 to 47.8 seconds
each). The two existing long-line warnings were fixed by the wrapping noted above;
the delivery checks compile the final sources again with the axiom probe.
The complete pairwise diff contains only copyright/spacing and local instance names.
The upstream implementation supplies the mathematical declarations unchanged.
The five differing local-instance labels have no references outside the retired file.

## Proved and sorry left

The assigned module has zero original holes: proved 0 of 0, added 0, split off 0.
Its duplicate declarations are removed; their complete proofs remain in the upstream twin.
The adapted consumers retain these existing holes without modification:

- AlgebraicGeometry.genus_well_defined
  (GenusWellDefined; blueprint: lem-pc-genus-well-defined).
- AlgebraicGeometry.Scheme.Modules.scalarCup_positive_resolution_class_compatibility
  (ScalarCupPositiveResolutionClassCompatibility; blueprint:
  new-sc-scalar-cup-positive-resolution-class-compatibility).

No other adapted consumer contains a sorry. This delivery claims module pruning, not
new mathematical proof progress.

## No longer needed

The module Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations and its duplicate
implementation are no longer needed. Its import is removed from:

- Sheaf.AlgebraicGeometry.CanonicalCoherentEtaleComparison
- Sheaf.AlgebraicGeometry.ExternalCupScalarBalance
- Sheaf.AlgebraicGeometry.GenusWellDefined
- Sheaf.AlgebraicGeometry.ScalarCupPositiveResolutionClassCompatibility
- Sheaf.AlgebraicGeometry.ScalarExtCupInverseImageSecond
- Sheaf.AlgebraicGeometry.ScalarModuleCohomologyPullbackComparison
- Sheaf.AlgebraicGeometry.ScalarTensorUnitCoefficient

Every such import is replaced by the official twin. No mathematical dependency node
is pruned: def-sc-field-linear-module-cohomology-operations,
lem-sc-field-linear-ext-map-injective and lem-sc-field-linear-ext-map-surjective
remain, attached to the same declarations in the twin. The module-resolution and
field-scalar-restriction dependencies remain necessary to those retained proofs.
All seven substituted source import closures contain zero Sheaf/WeilConjectures twin
pairs, and a full Lean-source reference scan identified exactly these seven consumers.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes an item with sorry or a definition repair, but the
current queue marks this item retire. It already has zero sorry and its upstream twin
retains all proofs and definitions. The retirement manifest's 50-consumer snapshot is
stale: only seven direct imports remain in the current sources. The three old DAG
lean attachments still pointed at the duplicate and are corrected in this packet.

The three required msearch.py searches were run. LeanFinder returned general sheaf
cohomology and injective-resolution Ext APIs, Loogle did not know scalarCohomologyCup,
and Mathlib grep found no matches. Local source comparison found the exact official
twin, which is the relevant shorter route. No new statements, nodes or proof holes are
added. One existing proof is adjusted only to avoid repeated coefficient-type unfolding.

## Second reading by X2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
