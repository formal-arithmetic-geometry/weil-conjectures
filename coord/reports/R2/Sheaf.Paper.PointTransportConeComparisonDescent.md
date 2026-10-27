## What changed

Proved the five original obligations in `Sheaf.Paper.PointTransportConeComparisonDescent`
without changing their statements or the canonical maps. Removed the redundant identity
cast in `reductionUnit`, keeping its original domain and codomain explicit; the change record
is `coord/changes/point-transport-reduction-unit-cast.md`. There are no external Lean users
of this helper, and its tensor unit and section functor are unchanged. The canonical comparison,
augmentation and arrow definitions also have explicit original result types, with unchanged
bodies, so downstream proofs retain the small named interfaces instead of expanding the
localization and mapping-cocone implementations. The section-complex functor and module localization are now named definitions rather than
abbreviations, with their original bodies and types. This retains small interfaces in proof
terms while preserving the canonical maps definitionally. The proved public API lemma `sections_map_isIso` records exact sections followed by
derived localization, supplying the same inverse instance at the unchanged roof statement.
It realizes the existing exact-sections clause and is attached to the same node.
The model equality is reflexive. The named constructions `reductionTower` and `pullbackTower`
now expose each tower as one object. The corresponding functors retain the original maps
and functor laws; private reflexivity lemmas verify equality of the entire functors with
the original constructions. These two definitions are attached to the existing node.
This packaging prevents input-complex conversions from expanding all sectionwise module
actions of a tower.

The delivery also refactored the unclaimed `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`
(`scalarReductionExistence`/`scalarReductionExtension` as aliases of the unrestricted
constructions). The independent reader withdrew that change: it broke the published importer
`Sheaf.Paper.IntegralReductionTowerWellDefinedUnrestricted` (`towerReduction_quasiIso`, line 462,
type mismatch after `simpa only [scalarReductionExtension]`), and it is not needed: this module
compiles against the published scalar-adjunction module. The record
`coord/changes/shared-canonical-scalar-reduction.md` is marked withdrawn; that module is unchanged.

The augmentation condition follows from the existing unconditional quotient-unit compatibility
and product extensionality. Private, proved helpers expose both cone coordinates and their
joint determination. The strict comparison uses the supplied coordinate hypothesis; the
resolution identities use `pointTransportResolutionCancellation` and the existing unique
characterization of integral point transport.

The roof isomorphism follows from integral-operations well-definedness, exact sections and the
natural sections/Roos comparison. The descent proof reuses the proved `naturalIntegralTransport` helper of
`FrobeniusPointTransportNatural` for the actual ambient derived transformation. Its prescribed components determine it
uniquely by natural-transformation extensionality; a private definition and component theorem
name that same transformation once. The proof uses
the canonical source and target comparisons to conjugate it to good complexes. The identity-resolution
case identifies those components with coneArrow; generic naturality and cancellation give the roof equation.
The comparison theorem gives its resolution formula; componentwise equality gives uniqueness
and the resolution recipes give independence. The node proof and its dependency list record
this assembly, including the proved generic coordinate and extensionality APIs imported from
`PointQuotientAugmentationDiagram` and `FiniteFreeCompletedScalarComparison`.
The final proof compiles against the published library (reader's `lcompile.py`, 47 s),
with zero errors and zero remaining holes.
Local elaboration annotations expose the small presentation wrappers and shield derived-category
constructions; they do not change any public attribute or declaration signature. The proof
records each tower component with its literal `P.obj` endpoint types once, and uses explicit
source-map, target-map and inverse equations. This avoids repeated comparison of whole tower
functors and their sectionwise module actions when applying the resolution identities.

## Proved and sorry left

Original holes closed (5):

- `WeilConjectures.PointTransportCone.reductionSectionModel_eq`
- `WeilConjectures.PointTransportCone.augmentation_condition`
- `WeilConjectures.PointTransportCone.pointTransportConeComparison`
- `WeilConjectures.PointTransportCone.pullbackRoof_isIso`
- `WeilConjectures.PointTransportCone.pointTransportConeComparisonDescent`

All five belong to `lem-trf-point-transport-cone-comparison-descent`. No holes are added and no
holes remain in this module. The proof uses the already stated dependencies as intended by
stage 3; this is not a claim that their transitive dependencies are all axiom-free.

## No longer needed

Removed unused private imports of `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`,
`Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients` and
`Mathlib.CategoryTheory.Localization.Predicate`. Their required infrastructure is already
provided by the statement imports or encapsulated in the used proof dependencies.
Removed the proof-dependency edge to `lem-trf-point-cone-lifts-chain-naturality` and the private
import of `Sheaf.TraceFormula.PointConeLiftsChainNaturality`. Its needed theta-coordinate clauses
follow directly from the existing mapping-cocone lift equations and product projections. Its
chain-naturality clauses are unnecessary: naturality of the normalized arrows follows from the
already proved ambient transport and its canonical comparisons. The source file and DAG node
are retained for any other consumers. The cancellation and canonical-comparison dependency
modules remain needed. No unit statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original proof-dependency list did not separately name the unconditional quotient-unit
compatibility used by the augmentation helper on arbitrary complexes. The updated node now
records `lem-trf-strict-quotient-unit-compatible`; restricting that helper to good complexes or
assuming the non-characteristic hypothesis would change its statement and is unnecessary.

A shorter existing route was found in the proved private `naturalIntegralTransport` helper.
It supplies naturality of the actual ambient integral transport, so the delivery does not
repeat the descent/identification construction from the original node plan. The localization
node remains needed for its canonical target comparison, which proves the roof isomorphism.
Its large existential localization package is not needed: the roof formula follows directly
from the two naturality squares and cancellation.

The historical blueprint proof filename in the existing source references is absent from
`literature/blueprint/latest/`. The current unit section and the existing DAG statements and
Lean interfaces were read; the unit route and existing source references are retained.

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
The independent reader (2026-10-26) read the five proofs against the node and withdrew the
unneeded scalar-adjunction refactor described above.
