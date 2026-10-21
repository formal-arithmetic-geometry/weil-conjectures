# AlgebraicGeometry.Scheme.cbc_extension_zero_stratified_perfect

## Reason

Restore the quarantined module assigned to P6 in coord/rework.tsv. The upstream sync removed
`Scheme.LocallyClosedStratification`; the current `IsIntegralStratifiedPerfect` definition
quantifies over `Scheme.Stratification`. The archived private constructor still used the old
name, causing the recorded unknown-identifier error. Use the current type without changing
any fields or the public theorem. The existing Noetherian argument supplies constructibility.
Remove the obsolete public import of the now empty compatibility module. The current type
is already provided by the remaining public imports. No adopted source module is edited.

## Old

```lean
public import Sheaf.AlgebraicGeometry.LocallyClosedStratification
```

The type line of the archived private `extendStratification`:

```lean
    (s : LocallyClosedStratification U) : LocallyClosedStratification T where
```

## New

The obsolete import is removed, without a replacement import. The private type line is:

```lean
    (s : Stratification U) : Stratification T where
```

All other Lean lines, including the public theorem signature and complete proof, are verbatim
from the quarantine archive. Its dependency predicate already uses this type. On Noetherian
schemes locally closed subsets are constructible, so the extra field does not change the
mathematical notion. The existing construction proves that field, including on the closed
complement. No target statement or definition changes meaning.

## Users

`tools/downstream.py` with `--allow-missing --uses cbc_extension_zero_stratified_perfect`
reports zero active downstream modules and zero active mentions: the item is quarantined.
A supplementary source import traversal over both lean/ and quarantine/ finds 28 downstream
modules. The sole direct importer is the quarantined
`Sheaf.Paper.IntegralCompactSupportUniformRestriction`; its import is retained, and restoration
provides exactly the same public theorem. Every combined downstream module is listed below.
No consumer is edited or withdrawn. There are no active local claim records in this snapshot.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CommonStageFourierWeightUpper | no active local claim recorded | Unchanged public theorem; no adaptation. |
| Sheaf.Paper.CompactFiberStalk | no active local claim recorded | Unchanged public theorem; no adaptation. |
| Sheaf.Paper.CompactSupportCondensedRealization | no active local claim recorded | Unchanged public theorem; no adaptation. |
| Sheaf.Paper.DualBaseChange | no active local claim recorded | Unchanged public theorem; no adaptation. |
| Sheaf.Paper.ExchangeFunctoriality | no active local claim recorded | Unchanged public theorem; no adaptation. |
| Sheaf.Paper.ExtensionZeroStratifiedPerfect | no active local claim recorded | Unchanged public theorem; no adaptation. |
| Sheaf.Paper.FiniteCompactificationEigenvalues | no active local claim recorded | Unchanged public theorem; no adaptation. |
| Sheaf.Paper.FiniteCompactificationStalkReturn | no active local claim recorded | Unchanged public theorem; no adaptation. |
| Sheaf.Paper.FiniteExtensionCompactSupportBaseChange | no active local claim recorded | Unchanged public theorem; no adaptation. |
| Sheaf.Paper.FiniteHorizontalShriekMate | no active local claim recorded | Unchanged public theorem; no adaptation. |
| Sheaf.Paper.FixProjectionCompactificationComparison | no active local claim recorded | Unchanged public theorem; no adaptation. |
| Sheaf.Paper.FourierKernelConvolution | no active local claim recorded | Unchanged public theorem; no adaptation. |
| Sheaf.Paper.FrobeniusExchangeEquivalence | no active local claim recorded | Unchanged public theorem; no adaptation. |
| Sheaf.Paper.GeneralCondensedWeilRealization | no active local claim recorded | Unchanged public theorem; no adaptation. |
| Sheaf.Paper.IdentificationCoefficientTransport | no active local claim recorded | Unchanged public theorem; no adaptation. |
| Sheaf.Paper.IntegralCompactSupportUniformRestriction | no active local claim recorded | Unchanged public theorem; no adaptation. |
| Sheaf.Paper.ProperProductCounitTranspose | no active local claim recorded | Unchanged public theorem; no adaptation. |
| Sheaf.Paper.QbarCompactSupportBaseChange | no active local claim recorded | Unchanged public theorem; no adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | no active local claim recorded | Unchanged public theorem; no adaptation. |
| Sheaf.Paper.RationalCompactSupportCoefficientCoherence | no active local claim recorded | Unchanged public theorem; no adaptation. |
| Sheaf.Paper.RationalPurityPresentation | no active local claim recorded | Unchanged public theorem; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | no active local claim recorded | Unchanged public theorem; no adaptation. |
| Sheaf.Paper.SixFunctorMixedSupportCupProduct | no active local claim recorded | Unchanged public theorem; no adaptation. |
| Sheaf.Paper.WeilFourierInversion | no active local claim recorded | Unchanged public theorem; no adaptation. |
| Sheaf.Paper.ZlFrameworkPbcOpenComparisonData | no active local claim recorded | Unchanged public theorem; no adaptation. |
| Sheaf.Paper.ZlFrameworkPbcOpenExchangeComparison | no active local claim recorded | Unchanged public theorem; no adaptation. |
| Sheaf.Paper.ZlOpenDiagramComparisonTransport | no active local claim recorded | Unchanged public theorem; no adaptation. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | no active local claim recorded | Unchanged public theorem; no adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | no active local claim recorded | Unchanged public theorem; no adaptation. |

The private type cannot occur in a consumer's public signature. The removed compatibility
module is empty and exports no declarations. Therefore no consumer adaptation is necessary.
The named theorem's statement, all hypotheses, universes, coefficient objects, and conclusion
remain byte-identical to the archived declaration. The unit route and node attachment stay.

## Status

landed 20261021T155522-L-3343981 2026-10-21 (merge of deliver/P6/Sheaf.Paper.ExtensionZeroStratifiedPerfect)
