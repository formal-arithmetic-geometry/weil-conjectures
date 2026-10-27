# AlgebraicGeometry.Etale.SfP1Transport.supportedMap

## Reason

The original direct importer SfP1IntegralTransportData was rejected at 65 seconds in the
consumer check. Profiling found approximately 16 seconds checking supportedMap and
another 3 to 4 seconds checking its generated instance proof, alongside other independent
constructions. A baseline with the original kernel definitions has the same expensive
checks. Earlier instance caching and a general-scheme wrapper did not provide enough
margin. Separate the existing supported Ext realization into a module of its own, as
per the compile-time splitting rule. SfP1IntegralTransportData is unclaimed.

## Old

In lean/Sheaf/AlgebraicGeometry/SfP1IntegralTransportData.lean:

```lean
/-- The supported Ext representative with the ordinary functor endpoints fixed.
Source: exact closed direct image and Ext realization in the diagonal calculation.
(blueprint: def-sf-p1-integral-transport-data). -/
@[irreducible]
def supportedMap (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (S : Scheme.{u})
    (κ : Ext
      ((lowerStar (ModuleCat.{u + 1} A) (pullback.diagonal (ProjectiveLine S ↘ S))).obj
        (ordinaryFiniteConstant A (ProjectiveLine S)))
      (Scheme.finiteEtaleTateLine
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N A hA) 2) :
    (ordinaryFinitePushforward A (pullback.diagonal (ProjectiveLine S ↘ S))).obj
        (ordinaryFiniteUnit A (ProjectiveLine S)) ⟶
      (ordinaryFiniteLine A N hA
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))⟦(2 : ℤ)⟧ :=
  supportedExactDerivedMap
    (lowerStar (ModuleCat.{u + 1} A) (pullback.diagonal (ProjectiveLine S ↘ S)))
    (ordinaryFiniteConstant A (ProjectiveLine S))
    (Scheme.finiteEtaleTateLine
      (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N A hA) κ
```

## New

The same declaration, signature, attribute and body are in
lean/Sheaf/AlgebraicGeometry/SfP1SupportedExtMapData.lean. Only its blueprint docstring
attachment changes to def-sf-p1-supported-ext-map-data. The original module retains all
four original public imports and adds:

```lean
public import Sheaf.AlgebraicGeometry.SfP1SupportedExtMapData
```

All its other declarations remain verbatim. No mathematical map, hypothesis or conclusion
changes, and the node's mathematical statement is unchanged. Its Lean attachment excludes
the moved declaration, and its statement dependencies name the extracted definition node.
The new module imports only FiniteP1DiagonalKummerComponentFormula, which already supplies
the construction and all the types in its signature. No proof hole is added.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.SfP1IntegralTransportData | unclaimed | Publicly re-exports the same supportedMap; other declarations unchanged. |
| Sheaf.AlgebraicGeometry.SfP1IntegralTransport | unclaimed | Same definition, signature and body through the re-export; no edits. |
| Sheaf.AlgebraicGeometry.SfP1ChartMapComposition | H2 | Direct importer checked unchanged. |
| Sheaf.AlgebraicGeometry.SfP1IntegralTraceComparison | unclaimed | Direct importer checked unchanged. |
| Sheaf.AlgebraicGeometry.SfP1ChartExchange | unclaimed | Direct importer checked unchanged. |
| Sheaf.AlgebraicGeometry.SfP1IntegralSectionComparison | U3 | Direct importer checked unchanged. |
| Sheaf.Paper.RootTowerInnerSupport | unclaimed | Textual supportedMap match in ProEtale.RootInnerSupport; unrelated. |

The users table covers the supportedMap matches reported by tools/downstream.py --uses
and every direct importer of the changed module. The direct importers are compiled against
the split before delivery; unchanged sandbox copies are then removed. No held module is
adapted. No Challenge target statement or mathematical definition is changed; this is a
module split of an existing construction.

Validation: the complete 16-file compilation passed after the extractions, including
all direct importers and additional unit/counit users. No consumer edits were required;
only the six intended delivery source files remain in the sandbox.

## Status

landed 20261026T222540-L-666663 2026-10-26 (merge of deliver/A4/Sheaf.AlgebraicGeometry.SfDiagonalKernelIntegrals)
