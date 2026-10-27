# WeilConjectures.PurityFiniteSetting.finite_setting_comparison_hypotheses

## Reason

Prune imports unused by the theorem's unchanged statement. Compactification definitions
suffice; neither the refinement category nor smoothness appears in the signature.
Coefficient-ring finiteness is needed only by the proof.

## Old

```lean
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.Compactification.RefinementCategory
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
```

## New

```lean
public import WeilConjectures.Compactification.Defs
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
```

Every existing declaration signature and definition remains unchanged. This change only
reduces the names re-exported by the item module. No target definition changes meaning.

## Users

`python3 tools/downstream.py Sheaf.Paper.PurityFiniteSettingComparisonHypotheses
--uses finite_setting_comparison_hypotheses` reports zero downstream modules; the only
textual occurrence of the declaration is its definition in the item itself. A separate
search of both Lean roots finds no direct importers. Thus no consumer adaptation is needed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.PurityFiniteSettingComparisonHypotheses | U8 | Proof completed; signature unchanged. |

## Status

landed 20261023T103415-L-3133770 2026-10-23 (merge of deliver/U8/Sheaf.Paper.PurityFiniteSettingComparisonHypotheses)
