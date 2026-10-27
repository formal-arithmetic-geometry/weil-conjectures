## What changed

Proved `WeilConjectures.integralPullbackComparisonRealization` by specializing the
already stated stronger simultaneous theorem. The proof eliminates its existential
system in Prop and instantiates the coefficient fields and inclusion.

Moved the existing comparison data and coherence definitions verbatim to
`Sheaf.Paper.IntegralComparisonSystemData`, publicly re-exported from the original
module. Adapted only the first import of
`Sheaf.Paper.SimultaneousIntegralPullbackComparisons` to avoid the import cycle.
Updated the existing definition node `def-sf-integral-comparison-system-data`'s Lean
attachment; no new mathematical node or statement was introduced.

Change record: `coord/changes/V5-integral-comparison-interface-cycle.md`.

## Proved and sorry left

Closed one original hole:
`WeilConjectures.integralPullbackComparisonRealization`.
The item has zero holes left. Added zero holes.

The adapted module retains its existing hole
`WeilConjectures.integralPullbackComparisonRealization_simultaneous`
(node `lem-trf-integral-pullback-comparison-realization`). This is an existing stronger
library dependency, not a new split-off lemma. This delivery proves the specialization
from that declaration and does not claim its axioms are sorry-free.

## No longer needed

No mathematical node or source-library declaration is withdrawn. The simultaneous
existence theorem still uses the DAG's normalized-model, whole-counit-substitution,
and strict-system-coherence route. They remain needed for that theorem, and are not
claimed as pruned by this specialization.

The item no longer directly needs these old private imports; the unchanged shared
interface retains the ones used to elaborate its definitions:

- `Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices`
- `Sheaf.Paper.IntegralOperationsPreserveConstructible`
- `Sheaf.Paper.IntegralFinitePullbackComposition`
- `Sheaf.Paper.IntegralOperationsWellDefined`
- `Sheaf.Paper.IntegralScalarExtensionWellDefined`
- `Sheaf.Paper.CoefficientExtensionReductionModel`
- `Sheaf.Paper.ScalarExtensionTowerCoherence`

No whole module is claimed pruned from the targets' import closure.

## Where the brief, the DAG or earlier work was wrong

The main statement node now attaches to the stronger simultaneous theorem rather
than the older theorem in this item. Its proof remains the substantive normalized
construction. Reusing that existing stronger statement proves this older theorem
without duplicating that construction. The definition node owns exactly the moved
interfaces, and its attachment follows their new location.

The effective-model interface assumes ell invertibility on schemes while the older
comparison data asks for primitive models on every scheme. This specialization does
not change either contract or attempt to discharge that stronger domain requirement.

Mathlib searches through the required msearch interfaces found ordinary pullback
associativity and adjunction formulas but no completed integral comparison theorem.
Local source searches found the simultaneous library statement used here.

## Forced adaptations

`Sheaf.Paper.SimultaneousIntegralPullbackComparisons` (holder D3): line 8 changes
only `public import Sheaf.Paper.IntegralPullbackComparisonRealization` to
`public import Sheaf.Paper.IntegralComparisonSystemData`. The original import would
create the cycle original -> simultaneous -> original once the item invokes the
stronger theorem. The source import-direction check reported:
`NO: Sheaf.Paper.SimultaneousIntegralPullbackComparisons already reaches
Sheaf.Paper.IntegralPullbackComparisonRealization; importing it from
Sheaf.Paper.IntegralPullbackComparisonRealization closes a cycle`.
The interface change is precisely the relocation of the original definitions.
No theorem, proof, signature or visibility in the other group's module is changed.

## Forced adaptations

### Sheaf.Paper.SimultaneousIntegralPullbackComparisons
NOT FORCED: the original compiles unchanged against the changed dependencies. Adapted module compiled in the delivered set; the reader judges whether the change is right.

## Second reading by V5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
