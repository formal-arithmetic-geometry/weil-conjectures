## What changed

Replaced the proof hole in
`AlgebraicGeometry.ProEtale.CompactificationBProjection.compactification_b_projection_reduction`
by a proof from two strictly smaller statements. The domain lemma supplies exact
completion-unit isomorphisms, normalized domains, and reconstruction invertibility.
The ordinary-square lemma supplies the ordinary coefficient-first square and
ordinary naturality. The item proves reconstruction naturality from actual
adjuncts, conjugates the ordinary square by the prescribed completion
isomorphisms, proves q and s invertible, derives the conditional inverse equation,
and proves completed naturality by cancellation of the two completion units.

Moved 17 definitions verbatim to
`Sheaf.Paper.CompactificationBProjectionData` to prevent an import cycle, keeping
all declaration names, signatures and bodies identical and publicly re-exported.
The theorem signature is unchanged. There are zero library modules downstream of
the item, and a name search finds no consumers outside it. No adopted source
library module changes. Change record:
`coord/changes/Z7-compactification-b-projection-presentation.md`.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.ProEtale.CompactificationBProjection.compactification_b_projection_reduction`
(node `lem-pur-compactification-b-projection-reduction`).

Added two holes, each the entire proof of a named public theorem in its own module:

- `AlgebraicGeometry.ProEtale.CompactificationBProjection.completion_projection_domains`
  (`lem-pur-compactification-b-projection-domains`): completion units, common
  constructible/Tor bounds, open inverse and pinned reconstruction invertibility.
- `AlgebraicGeometry.ProEtale.CompactificationBProjection.ordinary_projection_reduction_square`
  (`lem-pur-compactification-b-ordinary-square`): ordinary tensor projection
  reduction and naturality, without completed coordinates.

This is a decomposition, not a net hole closure: one original hole closed and
two strictly smaller holes added (net minus one). The item and data module contain
zero remaining holes. No arbitrary object is chosen from an existence theorem;
h and v are proposition-local witnesses, fixed by their exact homomorphisms.

## No longer needed

The following old direct imports are removed from the item; statement dependencies
needed by the moved coordinates are available through the data module. This is
removal of direct imports, not a claim that all these modules leave the global
import closure:

- `public import WeilConjectures.Compactification.RefinementCategory`
- `public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`
- `public import Sheaf.Paper.SmoothPurityCoefficientTowers`
- `public import Sheaf.Paper.SfIntegralConstructible`
- `public import Sheaf.Paper.SmoothPurityNormalizedEquivalence`
- `public import Sheaf.Paper.IntegralDerivedOperationsOnSlices`
- `public import Sheaf.Paper.QcqsCompactSupportRealization`
- `public import Sheaf.Paper.ExchangeProjectionSuppliedDomains`
- `public import Sheaf.Paper.DerivedPullbackTensorHom`
- `public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`
- `public import Sheaf.Paper.ProjectionReductionPresentation`
- `public import Sheaf.SixFunctors.IntegralCompactificationSystemRealization`
- `public import Sheaf.SixFunctors.IntegralSystemCanonicalBridge`
- `public import Sheaf.Paper.SmoothPurityNormalizedTowers`
- `public import Sheaf.Paper.CompleteProjectionMateDescent`
- `public import Sheaf.Paper.ShiftedTensorMorphismCalculus`
- `import Sheaf.Paper.IntegralTensorPullback`
- `import Sheaf.Paper.IntegralTensorProduct`
- `import Sheaf.Paper.PullbackTorAmplitude`
- `import Sheaf.Paper.FiniteCoefficientTensorCtf`
- `import Sheaf.Paper.SmoothPurityReductionDerivedMonoidalTower`
- `import Sheaf.Paper.IntegralTensorShriek`
- `import Sheaf.SixFunctors.OpenTensorNormalization`
- `import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`
- `import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `import Sheaf.Paper.CompleteCompactificationLimitRealization`
- `import Sheaf.Paper.TowerCompactSupportProjectionFormula`
- `import Sheaf.Paper.CompletedOperationTowerSubstitution`

The item now directly uses only the new domain and ordinary-square nodes in its
proof. The old operation/normalized-equivalence/compactification-limit/projection
descent dependencies remain needed by those two steps, with their existing DAG
proofs retained in the corresponding new nodes. No existing module is withdrawn.
`lem-pur-completed-operation-tower-substitution` is not needed by this route:
alpha is defined by explicit h/v conjugation of the ordinary signed projection,
so naturality and cancellation give the completed square directly. No separately
completed tensor symmetry is used. Its obsolete top-level `tool_uses` approval is
also removed, preserving the order of all retained approvals. No unit realization
or chapter route changes.

## Where the brief, the DAG or earlier work was wrong

The mathematics of the original statement is retained. The planned prose passes
between condensed module objects, section modules and strict varying-ring systems;
the named theorem signatures do not make all of those identifications definitionally
equal. The new domain and ordinary-square statements isolate that comparison glue.
Their docstrings give the full argument, retaining the specified reconstruction
counit and every transition. Edge cases checked on the statements: zero inputs,
identity/proper-only/open-only compactifications, empty schemes, shifts (both signed
paths have (-1)^(ab)), and arbitrary ramification through the cofinal ell-powers.

The original item owned both coordinate definitions and their theorem.
Splitting a proof step using those definitions into an importing module requires
the definitions to move to a third shared module. This is a presentation move
only, verified by exact textual comparison of all 17 signatures and bodies.

## New nodes

`def-pur-compactification-b-projection-data` owns the unchanged 17 coordinates and
signed symmetry definitions in the new data module. The original theorem module
publicly re-exports them.

`lem-pur-compactification-b-projection-domains` isolates original proof steps 1, 2,
4 and the domain/invertibility part of 5. It asserts no projection square or
naturality equation.

`lem-pur-compactification-b-ordinary-square` isolates ordinary projection descent
and the signed tensor transpose of steps 3--7. It asserts neither completion-unit
isomorphisms nor the completed square nor the inverse identity.

## Second reading by Z7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
