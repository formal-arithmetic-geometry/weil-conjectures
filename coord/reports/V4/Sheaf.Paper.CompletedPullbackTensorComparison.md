## What changed

Proved `WeilConjectures.pullbackTensorQuotient_existsUnique` with its existing full
K-flat normalization predicate unchanged. The proof supplies the already constructed
comparison of complexes and finite K-flat preservation theorem to the new proved
helper `WeilConjectures.finiteQuotientPullbackDescent`.

The helper module `Sheaf.Paper.FiniteQuotientPullbackDescent` uses the existing
`SequenceDerivedProof.normalizedComparisonDescent`, `kflatWhiskering`, universal
quotient counits and `derivedCochainCounit`. It contains no holes. It is separated from the
item after profiling showed expensive repeated functor conversions in the combined
file; factoring its natural-transformation assembly through an abstract categorical
helper keeps the specialized functor expressions out of that proof. The item imports this module only for its proof.
The large original file exceeded the 60-second limit after profiling and factoring
the new proof. `Sheaf.Paper.CompletedPullbackTowerRealizations` therefore extracts
71 existing coherent-reduction and tower declarations, preserving their names,
signatures, attributes and definition/proof bodies. Its 11 existing holes move
with them; none is a new obligation. The item publicly re-exports this module.
It also retains its original private `pullbackTensorSequenceRing_eq`, because two
existing import-all consumers use it. The original public imports remain in the item. The extracted module imports the
finite construction and omits the later finite-comparison, open-square and
K-flat preservation proof imports that its declarations do not use.
No target statement or existing definition body changes.

Validation: the three delivery files compile. Of the 21 direct importers, 17 pass
unchanged. Four exceed the limit on the original baseline as well as against the
packet, as detailed below. All 21 consumer copies have been removed; no consumer
adaptation is delivered. The unchanged original item itself takes 70 seconds
when rebuilt, further confirming the need for the extraction.

## Proved and sorry left

Closed 1 of the original 21 holes:

- `WeilConjectures.pullbackTensorQuotient_existsUnique`

Added 0 holes. The new helper theorem and all three private helpers are fully
proved. The ordinary quotient comparison remains an existing dependency; this
packet closes the derived existence/uniqueness hole from those declarations.

There are 20 remaining holes across the delivery. The first 11 below now belong
to `def-pur-completed-pullback-tower-realizations`, in the extracted module; the
other nine remain under `def-pur-completed-pullback-tensor-comparison`, in the item.
The declaration names and statements of all these holes are unchanged:

- `WeilConjectures.pullbackTensorReductionModel_existsUnique`
- `WeilConjectures.pullbackTensorReductionEvaluation_existsUnique`
- `WeilConjectures.pullbackTensorRoosModel_existsUnique`
- `WeilConjectures.pullbackTensorPullbackTower_existsUnique`
- `WeilConjectures.pullbackTensorTensorTower_existsUnique`
- `WeilConjectures.pullbackTensorIntegralPullbackModel_existsUnique`
- `WeilConjectures.pullbackTensorReductionGood`
- `WeilConjectures.pullbackTensorIntegralTensorModel_existsUnique`
- `WeilConjectures.pullbackTensorSequenceCochain_existsUnique`
- `WeilConjectures.pullbackTensorSequenceGood`
- `WeilConjectures.pullbackTensorSystemComparison_existsUnique`
- `WeilConjectures.pullbackTensorSystemComparison_evaluation`
- `WeilConjectures.pullbackTensorSystemComparison_associativity`
- `WeilConjectures.pullbackTensorSystemComparison_braiding`
- `WeilConjectures.pullbackTensorSystemComparison_unit`
- `WeilConjectures.pullbackTensorQuotientOrdinary_existsUnique`
- `WeilConjectures.canonicalFinitePullbackTensor_quotient`
- `WeilConjectures.canonicalCommonStagePullbackTensor_existsUnique`
- `WeilConjectures.canonicalIntegralPullbackTensor_scalar`
- `WeilConjectures.canonicalRationalPullbackTensor_scalar`

## No longer needed

No node, module or unit step is withdrawn. The original proof dependencies remain
needed by the declarations of the item and its extracted block. The new proof
adds the proved descent helper and its recorded dependencies. The compile-time
extraction publicly re-exports the tower-realization module.

The item removes these private proof imports, now used only by the extracted
module (which retains them); no public import is removed:

- `Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems`
- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator`
- `Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.PullbackExistsOfUniverses`
- `Sheaf.CategoryTheory.SequenceModulePullbackEvaluation`
- `Sheaf.Paper.IntegralComparisonSequenceDirectEvaluation`

## Where the brief, the DAG or earlier work was wrong

No mathematical statement required correction. The direct importer
`Sheaf.Paper.DerivedPullbackTensorIso`, held by J4, reaches the 120-second diagnostic
stop both against this packet and against the original library in an isolated
scratch root without any sandbox artifacts. The tested source is unchanged;
this pre-existing timeout does not justify adapting another group's module.
`Sheaf.Paper.SixFunctorOperationDatumStages` likewise takes 68 seconds against
the packet and 66 seconds without any sandbox artifacts, above the 60-second
limit in both cases; it is not adapted.

`Sheaf.Paper.DerivedAutomorphismHomEvaluation` takes 83–118 seconds against
the packet. A first check against the published compiled library took 49.5
seconds, but that library did not reproduce the current restored item source.
Rebuilding the unchanged original item in a separate scratch root takes 70
seconds and produces its artifact; the unchanged consumer then takes 86 seconds
against that artifact, without any packet modules. Thus the current-source
baseline also fails, and no adaptation is justified. An attempted proof
optimization was discarded. These baseline checks use the same consumer sources
as the packet checks.

`Sheaf.Paper.RelativeProductBaseChangeFactorSquares` takes 68 seconds against
the packet and 77 seconds against the freshly rebuilt original item in the same
isolated baseline root. This fourth timeout also predates the packet. The other
newly restored direct consumer, `Sheaf.Paper.TwistedPullbackReductionData`, passes
unchanged in 48.7 seconds. Both temporary consumer copies were removed.

The item was initially quarantined
because of an unpublished dependency. Its full source and Lean attachment are
preserved; the shared source was restored during this session.

The quotient extension is not exact, so the existing exact-composite localization
helper does not apply to it. The resolving K-flat comparison theorem does apply,
using the actual quotient counits. The cases of equal quotient levels, the first
quotient, zero complexes and empty schemes use the same argument.

## New nodes

`lem-pur-finite-quotient-pullback-descent` records the fully proved conditional
finite quotient descent theorem in `Sheaf.Paper.FiniteQuotientPullbackDescent`.
Its inputs are a comparison of complexes and K-flat preservation; its output fixes
the full universal-counit square and uniqueness. This is a proved helper extracted
for compile time, with no split-off sorry. A whole-blueprint search for
`quotient pullback` found no duplicate, and the ancestor command confirms
`def-weil-frobenius-coefficient-twists`.

`def-pur-completed-pullback-tower-realizations` records the extracted coherent
reduction, finite evaluation, Roos and strict pullback/tensor tower data. Its 11
holes are the existing holes listed above, moved verbatim. Its attachment lists
all 71 relocated public declarations. A whole-blueprint search for
`coherent reduction Roos` found no duplicate. This is a compile-time relocation,
with the same public names and bodies, rather than a definition or statement
repair. The layout and consumer checks are recorded in
`coord/changes/V4-completed-pullback-tower-extraction.md`.

## Second reading by V4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
