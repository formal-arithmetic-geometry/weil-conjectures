# Restoring the bounded constructible base-change interface

## Reason

The assigned row of coord/rework.tsv records a module removed after a cluster restore was
reverted. Its archived source is already hole-free and compiles against the current published
dependencies. The concrete repair restores this missing source module, including its actual
pullback-square comparison, three exchange steps, base-change transformation and proved API.
This is restoration of the assigned missing library interface, not a claim to close a proof hole.
No mathematical definition is replaced or changed.

## Old

The live path is absent:
`lean/WeilConjectures/SixFunctors/ProEtale/ModuleObject/BaseChangeTheorems/MorphismDefs.lean`.
Its authoritative source remains at the same path under `quarantine/` instead of `lean/`.
The archive has zero sorry proofs. In the existing counit node, lean.statement still describes
the superseded explicit-k, unbundled-scheme interface.

## New

The live module is restored byte for byte from the archive. Every declaration, public import,
attribute, proof, definition body, universe and coefficient restriction is retained.
In particular, the comparison is inverse composition, square equality, then composition;
base change is precisely unit insertion, square transport and counit contraction.
The counit node's Lean attachment is corrected to the actual implicit-k, Over-object theorem
signature, including X.left. The mathematical statement and proof dependencies do not change.
No target statement or definition changes meaning, so no new target semantic review is needed.

## Users

The live direct-import scan with tools/downstream.py finds LowerShriekDefs. The table also
includes every direct importer found by scanning both live roots and both quarantine roots.
No consumer is edited. ContinuousCoefficientCommRing was compiled from its unchanged archive
against the restored module in the C3 sandbox overlay (2.4 seconds, no errors or warnings).
The source module compiled independently in 3.3 seconds, without errors or warnings.

| module | group holding it | effect |
| --- | --- | --- |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriekDefs | unclaimed | Live reexport; unchanged interface, no adaptation. |
| Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing | unclaimed | Archived importer compiled unchanged against the restored module; not included for restoration. |
| Sheaf.Paper.CondensedERealization | unclaimed | Archived importer; unchanged interface, no adaptation. |
| Sheaf.Paper.ContinuousIntegralComparisons | unclaimed | Archived importer; unchanged interface, no adaptation. |
| Sheaf.Paper.CondensedQbarComparisons | unclaimed | Archived importer; unchanged interface, no adaptation. |
| Sheaf.Paper.FiniteDiscreteExchangeComparison | unclaimed | Archived importer; unchanged interface, no adaptation. |
| Sheaf.Paper.CondensedOpenClosedRecollement | unclaimed | Archived importer; unchanged interface, no adaptation. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | Archived importer; unchanged interface, no adaptation. |
| Sheaf.Paper.FiniteDiscreteRealizationFunctor | unclaimed | Archived importer; unchanged interface, no adaptation. |
| Sheaf.Paper.ContinuousExchangeIntegralModel | unclaimed | Archived importer; unchanged interface, no adaptation. |
| Sheaf.Paper.BoundedExchangeAmbient | unclaimed | Archived importer; unchanged interface, no adaptation. |
| Sheaf.Paper.StratifiedLatticeRank | unclaimed | Archived importer; unchanged interface, no adaptation. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | Archived importer; unchanged interface, no adaptation. |
| Sheaf.Paper.IntegralResidueExchange | unclaimed | Archived importer; unchanged interface, no adaptation. |
| Sheaf.Paper.BoundedConstructibleBaseChange | unclaimed | Archived importer; unchanged interface, no adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | Archived importer; unchanged interface, no adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeSection | unclaimed | Archived importer; unchanged interface, no adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeMono | unclaimed | Archived importer; unchanged interface, no adaptation. |
| WeilConjectures.TraceFormula.Statement | unclaimed | Archived importer; unchanged interface, no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.UpperLowerStar | unclaimed | Archived importer; unchanged interface, no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | Archived importer; unchanged interface, no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekBaseChange | unclaimed | Archived importer; unchanged interface, no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs | unclaimed | Archived importer; unchanged interface, no adaptation. |

## Status

landed 20261021T014659-L-2443114 2026-10-21 (merge of deliver/C3/WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs)
