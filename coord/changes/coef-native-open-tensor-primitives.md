# WeilConjectures.CoefSupportOpenTensor.SystemOpenCochains and FiniteOpenCochains

## Reason

The sequence and finite existence lemmas need the two explicit specialized types
before importing the parent existence theorem. Factor their transparent bodies
into a definition module to prevent an import cycle. The original types remain
transparent aliases, with identical elaborated mathematical data.

## Old

```lean
abbrev SystemOpenCochains {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :=
  letI := ProEtale.VaryingRing.extensionAdditive
    (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) j
  letI := ProEtale.VaryingRing.extensionLimits
    (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) j
  letI := ProEtale.VaryingRing.extensionColimits
    (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) j
  letI := ProEtale.VaryingRing.pullAdditive
    (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) j
  letI := ProEtale.VaryingRing.pullLimits
    (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) j
  letI := ProEtale.VaryingRing.pullColimits
    (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) j
  @OpenTensorCochainData.{u + 1, u, u} (ℕ × Z.ProEt) _
    (ProEtale.VaryingRing.sequenceSiteSmall Z)
    (coefficientSequenceTopology (ProEt.topology Z)) (coefficientSequenceCommRingSheaf.{u, u} l E Z)
    (ℕ × X.ProEt) _ (ProEtale.VaryingRing.sequenceSiteSmall X)
    (coefficientSequenceTopology (ProEt.topology X)) (coefficientSequenceCommRingSheaf.{u, u} l E X)
    (ProEtale.VaryingRing.extension (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) j)
    (ProEtale.VaryingRing.pull (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) j)
    (ProEtale.VaryingRing.extensionAdditive (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) j)
    (ProEtale.VaryingRing.pullAdditive (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) j)
    (ProEtale.VaryingRing.moduleJAdj (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) j)
    (ProEtale.VaryingRing.baseChange j) (pullSection l E j)

/-- Finite-coefficient specialization of ordinary open tensor data.
Source: Stacks 0E8I (blueprint: lem-coef-native-open-tensor-cochains). -/
abbrev FiniteOpenCochains {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (n : ℕ) :=
  letI := ProEtale.StrictTower.moduleJ_additive (compactSupportSystemLevel l E n) j
  letI := ProEtale.StrictTower.moduleJ_finiteLimits (compactSupportSystemLevel l E n) j
  letI := ProEtale.StrictTower.moduleJ_finiteColimits (compactSupportSystemLevel l E n) j
  letI := proEtaleRingModulePullback_additive j
    (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) Z)
    (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) X)
    (ProEtale.StrictTower.constantRingIso (compactSupportSystemLevel l E n) j)
  letI := proEtaleRingModulePullback_preservesFiniteLimits j
    (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) Z)
    (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) X)
    (ProEtale.StrictTower.constantRingIso (compactSupportSystemLevel l E n) j)
  letI := proEtaleRingModulePullback_preservesFiniteColimits j
    (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) Z)
    (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) X)
    (ProEtale.StrictTower.constantRingIso (compactSupportSystemLevel l E n) j)
  @OpenTensorCochainData.{u + 1, u, u} Z.ProEt _
    (ProEtale.VaryingRing.siteSmall Z) (ProEt.topology Z)
    (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) Z)
    X.ProEt _ (ProEtale.VaryingRing.siteSmall X) (ProEt.topology X)
    (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) X)
    (ProEtale.StrictTower.moduleJ (compactSupportSystemLevel l E n) j)
    (ProEtale.StrictTower.modulePullback (compactSupportSystemLevel l E n) j)
    _ _
    (ProEtale.StrictTower.moduleJAdj (compactSupportSystemLevel l E n) j)
    (proEtaleBaseChange j) (finitePullSection l E j n)

```

Original public imports:

```lean
public import Sheaf.Paper.CoefOpenTensorEvaluationData
public import Sheaf.SixFunctors.OpenTensorCochainData
```

## New

```lean
abbrev SystemOpenCochains {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :=
  WeilConjectures.CoefSupportOpenTensor.NativeOpenTensorPrimitives.SystemOpenCochainsData l E j

/-- Finite-coefficient specialization of ordinary open tensor data.
Source: Stacks 0E8I (blueprint: lem-coef-native-open-tensor-cochains). -/
abbrev FiniteOpenCochains {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (n : ℕ) :=
  WeilConjectures.CoefSupportOpenTensor.NativeOpenTensorPrimitives.FiniteOpenCochainsData l E j n

```

Both original public imports remain verbatim. Add
`public import Sheaf.Paper.CoefNativeOpenTensorPrimitives` for the aliases;
the existence lemmas are imported privately. The primitive bodies are exactly
the old specialization expressions, with renamed declarations in their own namespace.
No target or theorem signature changes. No existing module besides the item is edited.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CoefNativeOpenTensorModelsDataExistence | unclaimed in current snapshot | Direct importer; both abbreviations reduce to the identical explicit OpenTensorCochainData specializations. Compiled unchanged by delivery related-module check. |

No other source mentions either specialized declaration. The new finite and sequence
existence modules import the primitive types and are compiled in the same packet.
Targets retain their meanings; there is no definition-data or hypothesis change.

## Status

landed 20261027T180758-L-3900819 2026-10-27 (merge of deliver/R8/Sheaf.Paper.CoefNativeOpenTensorCochains)
