## What changed

Completed `AlgebraicGeometry.Etale.exists_projectiveLineFullAdjunction` without changing
its signature. Choose the adjunction in `projectiveLineTraceDatum`, then cancel the
ordered proper projection isomorphism in its `counit_normalization` equation to obtain
exactly `projectiveLineTraceEpsilon` on every unbounded object.

The item imports only `Sheaf.AlgebraicGeometry.ProjectiveLineTrace`. Updated
`dag/nodes/sec-smooth-purity/thm-amb-p1-adjunction.json` with the actual three-step
proof and dependencies. The public import pruning is recorded in
`coord/changes/ProjectiveLineFullAdjunction-imports.md`.

Validation after resuming on 2026-10-19: the final item compiled without warnings on
the project server in 10.3 seconds. The unchanged sole direct importer
`Sheaf.AlgebraicGeometry.AffineSpaceAmbientAdjunction` compiled against that proof
in the same sandbox compile set in 6.8 seconds. The theorem signature is unchanged,
and the proof docstring now describes the implemented cancellation argument.
The final preflight checks the item and its axioms.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.Etale.exists_projectiveLineFullAdjunction`
(node `thm-amb-p1-adjunction`). Zero holes remain in the item; zero holes added and
zero split off. No new declarations were introduced.

This proof uses the existing stated theorem
`AlgebraicGeometry.Etale.exists_ordinaryFiniteP1Adjunction`
(node `lem-asd-ordinary-finite-p1-adjunction`) through `projectiveLineTraceDatum`.
That existing dependency is still `sorry`; this delivery proves the assigned theorem
from the recorded dependency, rather than claiming a complete axiom-free closure.

## No longer needed

Removed these direct imports:

- `Sheaf.AlgebraicGeometry.DerivedCategories`
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`
- `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`
- `Sheaf.Paper.FiniteDirectImageComposition`
- `Sheaf.AlgebraicGeometry.ProperProjectionFormula`
- `Mathlib.Topology.Defs.Filter`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`
- `Sheaf.AlgebraicGeometry.ProperUnboundedBaseChange`
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`
- `Sheaf.AlgebraicGeometry.ProperStability`
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `Mathlib.AlgebraicGeometry.ZariskisMainTheorem`
- `Mathlib.AlgebraicGeometry.Noetherian`
- `Sheaf.Paper.RingedExchangeTensorCoherence`
- `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Decomposition`
- `Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalIntegrals`

A source import-graph comparison rooted at `TargetsCheck` shows that this change
removes exactly two library modules from the targets' import closure:
`Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalIntegrals` and
`Sheaf.AlgebraicGeometry.ProperStability`.

The following old direct proof dependencies are not used in this module's proof:

- `lem-weil-derived-direct-image-composition`
- `lem-amb-p1-diagonal-integrals`
- `lem-kun-proper-base-change-torsion-ring`
- `lem-kun-proper-stability`
- `lem-weil-pbc-closed-immersion-proper`
- `lem-weil-pbc-ringed-exchange-tensor-coherence`
- `thm-amb-p1-decomposition`

The normalized datum supplies the adjunction, including its unit and triangle laws,
so this consumer does not reconstruct the diagonal kernel, base-change exchanges,
or the decomposition. Some removed imports remain transitive dependencies of the
normalized datum; removing their direct imports does not assert that those modules
have left the targets' entire import closure.

Removed all four obsolete top-level `tool_uses` approvals from this node:
`lem-weil-pbc-ringed-exchange-tensor-coherence`,
`lem-kun-proper-base-change-torsion-ring`,
`lem-weil-derived-direct-image-composition`, and `lem-kun-proper-stability`.
Their mathematics remains where the existing normalized-datum theorem needs it.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox had a successful proof but stored its node update outside
`dag/nodes/`, left the old proof steps unchanged despite changing the dependency list,
and omitted the change-record path from its report. These delivery defects are fixed.

The current library already packages the diagonal construction and both triangles
in `OrdinaryFiniteP1Datum`, furnished by `exists_ordinaryFiniteP1Adjunction`.
Its counit normalization determines the desired counit after cancellation. Repeating
that construction here would duplicate an existing obligation. The unit record
`dag/units/sk-prop-sf-cbc.json` has empty `realized.statement` and `realized.steps`;
no unit statement or recorded unit step is changed or withdrawn.

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
