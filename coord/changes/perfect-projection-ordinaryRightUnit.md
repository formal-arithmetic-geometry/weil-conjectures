# AlgebraicGeometry.Scheme.PerfectProjection.ordinaryRightUnit

## Reason

Construct the ordinary right unitor explicitly through the tensor/sheafification
comparison, presheaf right unitor and sheafification counit. The public theorem
`ordinaryRightUnit_eq` proves equality with the original monoidal unitor. This
avoids repeated expansion of the localized monoidal structure. The complete
module compiled in 35.7 seconds. No mathematical statement is changed.

## Old

```lean
def ordinaryRightUnit (T : Scheme.{u}) (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (M : proEtaleRingModules T R) :=
  letI := SheafOfModules.monoidalCategory R
  ρ_ M
```

## New

```lean
def ordinaryRightUnit (T : Scheme.{u}) (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (M : proEtaleRingModules T R) :
    ((proEtaleOrdinaryTensor T R).obj M).obj
      (SheafOfModules.unit ((adicLisseForget T).obj R)) ≅ M :=
  letI := SheafOfModules.monoidalCategory R
  let S := PresheafOfModules.sheafification.{u + 1}
    (𝟙 ((adicLisseForget T).obj R).obj)
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1}
    (𝟙 ((adicLisseForget T).obj R).obj)
  SheafOfModules.tensorObjIsoSheafification M
      (SheafOfModules.unit ((adicLisseForget T).obj R)) ≪≫
    S.mapIso (ρ_ M.val) ≪≫ (asIso adj.counit).app M
```

## Users

`tools/downstream.py Sheaf.Paper.PerfectProjectionFormula --uses ordinaryRightUnit`
reports 1,197 import descendants and one actual declaration user.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.PerfectProjectionFormula | H4 | The operation equals the original unitor by ordinaryRightUnit_eq. Resolution.totalInverse rewrites this equality when supplying its unit-coherence proof. Its chain map and inferred signature are unchanged by proof irrelevance. |

No external consumer needs adaptation. Targets retain the same meaning through
the proved equality. The explicit type annotation of ordinaryTensorHom is
recorded separately in perfect-projection-ordinaryTensorHom.md.

## Status

landed 20261020T051358-L-1658222 2026-10-20 (merge of deliver/H4/Sheaf.Paper.PerfectProjectionFormula)
