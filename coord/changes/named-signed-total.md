# CategoryTheory.CochainPullback.StrictCoefficient.total

## Reason

The reducible alias expands the induced monoidal structure of complexes in every
section formula and type conversion. Give the existing total object a named
semireducible definition. The body, binders and resulting complex are unchanged;
no tensor, sign, coproduct, morphism or hypothesis is changed.

## Old

```lean
abbrev total {R : Sheaf J CommRingCat.{w}} (P Q : Complex R) : Complex R := P ⊗ Q
```

## New

```lean
noncomputable def total {R : Sheaf J CommRingCat.{w}} (P Q : Complex R) : Complex R := P ⊗ Q
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SecSmoothPurity.NormalizedCoefficientDiagram | unclaimed | Definitional presentation only. |
| Sheaf.SecSmoothPurity.CoefficientComparisonsStrictTotalization | G4 | Uses the same signed total through its named definition. |
| Sheaf.SecSmoothPurity.CoefficientComparisonsUnitComposition | H1 | Definitional equality preserves its original signature and formulas. |
| Sheaf.SecSmoothPurity.StrictCoefficientComparisonCalculus | unclaimed | The original proof consumes the unchanged strict-totalization conclusion. |
| Sheaf.Paper.BalancedFiniteTowerGeneratorComparison | unclaimed | Transitive consumer; the mathematical object is unchanged. |
| Sheaf.Paper.CompletedComparisonQuotientRealization | unclaimed | Transitive consumer; the mathematical object is unchanged. |
| Sheaf.SecSmoothPurity.NormalizedKappaTransitions | G4 | New proved calculation imports the repaired interface. |
| Sheaf.SecSmoothPurity.NormalizedScalarTensorTransitions | G4 | New proved calculation imports the repaired interface. |
| Sheaf.SecSmoothPurity.CoefficientTransitionSquares | G4 | New proved calculation imports the repaired interface. |
| Sheaf.SecSmoothPurity.PullTensorGeneratorSections | G4 | New proved calculation imports the repaired interface. |

`tools/downstream.py Sheaf.SecSmoothPurity.NormalizedCoefficientDiagram --uses total`
was read before the edit. The unchanged H1 unit/composition consumer compiled in 7.9 seconds against
the named total. All four unchanged consumers compiled against this packet: unit/composition,
strict coefficient calculus, balanced finite-tower comparison, and completed
quotient realization. No consumer adaptation is needed. This presentation does not
change target meaning or any adopted source-library declaration.

## Status

landed 20261024T185821-L-3693383 2026-10-24 (merge of deliver/G4/Sheaf.SecSmoothPurity.CoefficientComparisonsStrictTotalization)
