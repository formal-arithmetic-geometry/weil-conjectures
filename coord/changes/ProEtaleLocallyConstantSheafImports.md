# Sheaf.Paper.ProEtaleLocallyConstantSheaf imports

## Reason

Remove two redundant direct public imports during second reading. Both modules are
already publicly imported through `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`:
that module publicly imports `Mathlib.CategoryTheory.Sites.ConstantSheaf`, which
publicly imports `Mathlib.CategoryTheory.Sites.Sheafification`. Thus the complete
set of public transitive imported modules is unchanged. A source-graph comparison
checked equality of the before/after sets (2837 modules). The preflight requires a
change record for removal of any direct public import, including this redundancy.

All existing declaration signatures, definition bodies and visibility remain
identical. Neither target statements nor their definitions change, so no target
statement review is reopened. No downstream module is adapted by this delivery.

## Old

```lean
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
```

## New

```lean
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
```

## Users

All transitive consumers listed by `tools/downstream.py
Sheaf.Paper.ProEtaleLocallyConstantSheaf --names` are included below. Their available
public imports, definitions and statement meanings are identical, since the
removed direct imports remain public through the retained dependency. Group
holders are from the read-only claim records at second reading.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProEtaleConstantSheafStalk | E2 | Identical statements and public exports; no adaptation. |
| Sheaf.Paper.FiniteCtfTriangulated | unclaimed | Identical statements and public exports; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientExchange | unclaimed | Identical statements and public exports; no adaptation. |
| Sheaf.Paper.FiniteDiscreteConstructibleEncoding | D2 | Identical statements and public exports; no adaptation. |
| Sheaf.Paper.FiniteDiscreteExchangeComparison | unclaimed | Identical statements and public exports; no adaptation. |
| Sheaf.Paper.FiniteDiscreteExchangeRealization | unclaimed | Identical statements and public exports; no adaptation. |
| Sheaf.Paper.FiniteRingConstructibleSheafOrigin | unclaimed | Identical statements and public exports; no adaptation. |
| Sheaf.Paper.FiniteTensorConstructibleCohomology | unclaimed | Identical statements and public exports; no adaptation. |
| Sheaf.Paper.FiniteTorsionConstructibility | unclaimed | Identical statements and public exports; no adaptation. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | Identical statements and public exports; no adaptation. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | Identical statements and public exports; no adaptation. |
| Sheaf.Paper.IntrinsicFiniteTorsionConstructibility | unclaimed | Identical statements and public exports; no adaptation. |
| Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated | unclaimed | Identical statements and public exports; no adaptation. |
| Sheaf.Paper.ProEtaleConstructibleSheaf | unclaimed | Identical statements and public exports; no adaptation. |
| Sheaf.Paper.ProEtaleFiniteLocalConstancyReflection | unclaimed | Identical statements and public exports; no adaptation. |
| Sheaf.Paper.ProEtaleFixedModuleLocalConstancy | unclaimed | Identical statements and public exports; no adaptation. |
| Sheaf.Paper.ProEtaleLisseOrigin | D3 | Identical statements and public exports; no adaptation. |
| Sheaf.Paper.ProEtaleResidueTorTest | unclaimed | Identical statements and public exports; no adaptation. |
| Sheaf.Paper.ProEtaleStratifiedCounit | unclaimed | Identical statements and public exports; no adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | Identical statements and public exports; no adaptation. |
| TargetsCheck | unclaimed | Identical statements and public exports; no adaptation. |
| WeilConjectures | unclaimed | Identical statements and public exports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf | unclaimed | Identical statements and public exports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.DualPerfect | unclaimed | Identical statements and public exports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.LocalizationConstructible | unclaimed | Identical statements and public exports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.LocalizationFiniteTor | unclaimed | Identical statements and public exports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Identical statements and public exports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Identical statements and public exports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | Identical statements and public exports; no adaptation. |

## Status

landed 20261016T133217-L-3234173 2026-10-16 (merge of deliver/F4/Sheaf.Paper.ProEtaleLocallyConstantSheaf)
