# AlgebraicGeometry.ProEtale.SupportedConstructibleOriginComparison.constantModuleComparison

## Reason

The expanded adjunction construction is duplicated verbatim by the existing source
`AlgebraicGeometry.ProEtale.comparisonUpperStarConstantSheafIso`. The interrupted pass recorded profiling of the item showing expensive kernel checking
and private-module linting of its existing definitions:
two checking tasks used about 16 and 25 seconds, with module linting taking about 39
seconds concurrently. The final file sometimes exceeded the single-file limit.
Reuse the existing canonical definition through a public import rather than reconstructing
its large term. The definition remains irreducible, with exactly its original signature.
The terminal-object witnesses agree by subsingleton elimination, so the adjunction
normalization and constant-section identification are identical.

## Old

```lean
@[irreducible] def constantModuleComparison (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ⋙
      comparisonUpperStar (ModuleCat.{u + 1} A) T ≅
        constantSheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A) :=
  (((constantSheafAdj T.smallEtaleTopology (ModuleCat.{u + 1} A)
      (Scheme.Etale.isTerminalMkId T)).comp
      (comparisonAdjunction (ModuleCat.{u + 1} A) T)).ofNatIsoRight
    ((Scheme.toProEt T).sheafPushforwardContinuousCompSheafSectionsObjIso
      (ModuleCat.{u + 1} A) T.smallEtaleTopology (Scheme.ProEt.topology T)
      (Opposite.op (Scheme.Etale.mk (𝟙 T))))).leftAdjointUniq
    (constantSheafAdj (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)
      (MorphismProperty.Over.mkIdTerminal _ _))
```

## New

```lean
@[irreducible] def constantModuleComparison (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ⋙
      comparisonUpperStar (ModuleCat.{u + 1} A) T ≅
        constantSheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A) :=
  comparisonUpperStarConstantSheafIso A T
```

Add public import `WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf`, which exports
the reused definition used by this public definition body. No existing public import
is removed, and no source-library declaration or module is changed.

## Users

`python3 tools/downstream.py Sheaf.SecSmoothPurity.SupportedConstructibleOriginComparison
--uses constantModuleComparison` reports zero downstream importers and the item itself
as the only declaration user. A source search agrees. The local coefficient comparison
uses the same normalized canonical constant comparison, with no type or behavior change.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SecSmoothPurity.SupportedConstructibleOriginComparison | M6 | Reuse the existing canonical constant comparison; coefficientComparison has unchanged type and composite. |

No target signature or target definition meaning changes. The source definition used
here already implements exactly the previous universal-property construction.

## Status

landed 20261022T152904-L-3359907 2026-10-22 (merge of deliver/M6/Sheaf.SecSmoothPurity.SupportedConstructibleOriginComparison)
