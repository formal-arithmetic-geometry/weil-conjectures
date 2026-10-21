# Sheaf.Algebra.Homology.FiniteFreeCompletionExchange public imports

## Reason

The proof now descends the fixed cochain comparison directly. Its public statements need
only the principal quotient model, the arithmetic restriction definitions and module-sheaf
colimits. The discarded public proof imports are recorded under No longer needed in the
worker report. No existing declaration signature, body of a public definition, visibility,
or target statement changes. The local irreducibility attributes and transparency options
prevent expansion of the chosen sheaf tensor and Roos constructions during proofs.

## Old

```lean
public import Sheaf.Algebra.Homology.PrincipalQuotientCompletionModel
public import Sheaf.CategoryTheory.StrictTowerArithmeticRestriction
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import Sheaf.CategoryTheory.StrictRoosComparison
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
```

## New

```lean
public import Sheaf.Algebra.Homology.PrincipalQuotientCompletionModel
public import Sheaf.CategoryTheory.StrictTowerArithmeticRestrictionDefs
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
```

All seven existing public declarations and their signatures are preserved verbatim.
The only other command changes are local proof transparency/irreducibility settings.
The new modules and their public statements have new DAG attachments and do not adapt
any existing source-library declaration.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.FiniteFreeCompletionExchange | E1 | Original theorem is proved from the two separate new results; public imports are pruned. |
| Sheaf.Algebra.Homology.FiniteFreeCompletionExchangeCoherence | M4 (current claim record) | No edit required: it explicitly imports SiteCoveringAxioms, RingedStrictTowerHomotopyLimitIndependentCoefficients and StrictRoosComparison; its arithmetic namespace remains supplied by the definition module. It uses no free-sheaf construction. |

The downstream.py module query lists only FiniteFreeCompletionExchangeCoherence.
Its declaration-uses query for finiteFreeCompletionExchange lists only the item itself.
The existing coherence statements use the preserved public comparison structures.
No consumer is forcibly adapted and no declaration is removed.

## Status

landed 20261021T134323-L-840275 2026-10-21 (merge of deliver/E1/Sheaf.Algebra.Homology.FiniteFreeCompletionExchange)
