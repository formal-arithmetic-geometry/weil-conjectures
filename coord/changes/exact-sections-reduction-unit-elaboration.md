# Sheaf.Paper.ExactSectionsReductionUnit elaboration commands

## Reason

The completed proof uses Mathlib's backward definitional-equality elaboration through
scalar restriction and sheafification. Three module-local elaboration options enable
those coercion identifications. Scoped `omit ... in` commands ensure that new private
helpers depend only on the derived-category instances they actually need. Preflight
classifies changes to these commands as an interface change and requires this record.
No existing declaration signature, visibility, instance body, construction, or public
import changes. Every new helper is private and proved. Only theorem proofs and private
helpers use these commands; options do not become options of importing modules.

## Old

The original elaboration option block was:

```lean
@[expose] public noncomputable section
set_option autoImplicit false
```

There were no `omit ... in` commands. The existing declarations, including the full
signature of `SheafOfModules.PrincipalReduction.Setup.exactSectionsReductionUnit`,
remain verbatim. No definition repair is proposed.

## New

```lean
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

Before each of `ordinaryAdjunction` and `sheafCounit_adjunction`:

```lean
omit [HasDerivedCategory.{wR} (ModuleCat.{r} R)]
  [HasDerivedCategory.{wA} (ModuleCat.{r} D.A)] in
```

Before `sections_t_regular`:

```lean
omit [HasDerivedCategory.{wO}
    (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O))]
  [HasDerivedCategory.{wS}
    (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.S))]
  [HasDerivedCategory.{wR} (ModuleCat.{r} R)]
  [HasDerivedCategory.{wA} (ModuleCat.{r} D.A)] in
```

Before `module_c_isIso`:

```lean
omit [HasDerivedCategory.{wO}
    (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.O))]
  [HasDerivedCategory.{wS}
    (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J D.S))] in
```

Each `omit` applies only to the immediately following new private theorem.

## Users

`tools/downstream.py Sheaf.Paper.ExactSectionsReductionUnit --uses` with all eight
existing declaration names reports no importing modules. The DAG parent route is
preserved, and no module is withdrawn. No adaptation is required.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ExactSectionsReductionUnit | V3 | Local elaboration commands support the completed proof; existing public declarations are unchanged. |

## Status

landed 20261021T144016-L-36705 2026-10-21 (merge of deliver/V3/Sheaf.Paper.ExactSectionsReductionUnit)
