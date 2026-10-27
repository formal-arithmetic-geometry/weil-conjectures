## What changed

Reduced SheafOfModules.systemSingletonGeometricPullback to two separate mathematical
results: the ordinary comparison on strict semilinear systems, and the normalized lift
of a specified ordinary comparison to unbounded derived categories. Both new statements
have their own modules, source, proof in words and DAG nodes. Their ordinary data
interface is concrete; none of its definitions contains a sorry or chooses arbitrary
data from existence. The original module's public declarations and signatures are
unchanged.

The parent contains the complete flat-model argument: ringed-topos K-flat pullback,
followed by the normalized identity scalar unit, preserves flat-term K-flat complexes
under level inverse image. The identity coefficient-map case of singletonScalarExtension
then supplies the source and target singleton models on the ringed sequence sites.
The parent transfers the exact ordinary system functor and assembles all nine clauses.

## Proved and sorry left

One original hole is closed by decomposition:
SheafOfModules.systemSingletonGeometricPullback
(lem-pur-system-singleton-geometric-pullback).
The parent has zero remaining sorry placeholders.

Two holes are added, each exactly the body of a named public theorem:

- SheafOfModules.geometricSystemOrdinaryComparison
  (lem-pur-system-geometric-ordinary-comparison): construct exact termwise inverse image
  and the ordinary tensor/singleton comparisons, with their four normalizations.
- SheafOfModules.geometricSystemDerivedLift
  (lem-pur-system-geometric-derived-lift): given those specified ordinary comparisons,
  construct their derived lifts with the four derived normalization equations.

The flat-model part is proved in the parent by geometricLevelKFlat,
singletonFlatModelsFromScalar and singletonFlatModels. No holes are hidden in these
private helpers. This delivery is a decomposition, not a net closure of the original
mathematical argument: one hole closed, two added, net minus one. A longer proof draft
was explored but is not claimed as verified or included in this packet.

## No longer needed

The parent no longer directly imports GeometricModuleConstruction,
GeometricModuleTransport, CoefficientComparisonsBalancedConstruction,
ExtensionEvaluationComparison or AdjunctionMateTranspose. Their work is retained in the
ordinary and derived child nodes as appropriate; it has not been pruned from the
mathematical argument. Their unneeded proof imports are absent from the new ordinary
statement module. No existing public import is removed.

The balanced coefficient-square construction with identity structural coefficient maps
replaces a separate application of lem-pur-independent-inverse-image-tensor-comparison
(Sheaf.SecSmoothPurity.CochainInverseComparison). Its private triple-product construction
is also not required by the binary-product semilinear transport argument. These are
route choices recorded in the ordinary child; no upstream declaration is withdrawn.

The identity coefficient-map case of lem-pur-system-singleton-scalar-extension supplies
the flat-term K-flat singleton models. There is no separate componentwise tensor and
totalization proof in this parent. Thus def-pur-sheaf-tensor-product,
def-pc-tensor-complex-sheaves, def-pc-kflat-complex and def-pc-flat-sheaf-modules are not
separate direct proof dependencies. Their definitions remain in the statements or the
imported singleton theorem. lem-pur-system-ringed-sequence-site remains a statement
dependency. The resolving-class argument in the derived child uses
systemLevel_kFlatResolution from lem-pur-system-single-derived-extension, rather than
a separate application of lem-pc-kflat-resolution.

No existing module is withdrawn, and no claim is made that these direct-route changes
remove modules from the targets' transitive import closure.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction is proposed. The ordinary and derived pieces
are strictly parts of the original argument: the first contains no derived comparison,
and the second assumes an already constructed exact system functor and normalized
ordinary comparisons. The separate flat-model proof and the assembly remain in the
parent. The blueprint unit's realized route is preserved. In particular, equality of
derived maps is handled by whole-system localization and mates, not by assuming that
level evaluations detect equality of maps.

## New nodes

lem-pur-system-geometric-ordinary-comparison, in
Sheaf.CategoryTheory.SystemGeometricOrdinaryComparison, contains the ordinary exact
semilinear construction and its normalized tensor/singleton comparison. Edge cases:
above the selected index both values are zero; at the selected index tensor units give
multiplication; no coefficient flatness is required. The zero ring is allowed.

lem-pur-system-geometric-derived-lift, in
Sheaf.CategoryTheory.SystemGeometricDerivedLift, consumes that ordinary construction
and gives the normalized derived comparisons, representatives, multiplication and
lower-singleton square. Its resolving class consists of flat-term K-flat complexes,
so arbitrary nonflat transitions and unbounded inputs are allowed. Repeated equal
indices reduce to the normalized tensor unit. No change record is needed because no
existing statement or definition is changed.

## Second reading by F9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
