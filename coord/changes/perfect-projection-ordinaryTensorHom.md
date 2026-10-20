# AlgebraicGeometry.Scheme.PerfectProjection.ordinaryTensorHom

## Reason

Give the existing tensor operation an explicit result type in terms of
`proEtaleOrdinaryTensor` and the actual unit sheaf. This type is definitionally
equal to the original inferred type; the value and all parameters are unchanged.
The unit-coherence argument can then keep the localized monoidal structure
irreducible instead of repeatedly expanding its construction. The final proof uses an explicit right-unitor construction with a proved
equality to the monoidal unitor, and compiled afresh in 35.7 seconds against
the shared library. No target statement or mathematical definition changes.

## Old

```lean
def ordinaryTensorHom (T : Scheme.{u}) (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    {M N P Q : proEtaleRingModules T R} (v : M ⟶ N) (w : P ⟶ Q) :=
  letI := SheafOfModules.monoidalCategory R
  v ⊗ₘ w
```

## New

```lean
def ordinaryTensorHom (T : Scheme.{u}) (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    {M N P Q : proEtaleRingModules T R} (v : M ⟶ N) (w : P ⟶ Q) :
    ((proEtaleOrdinaryTensor T R).obj M).obj P ⟶
      ((proEtaleOrdinaryTensor T R).obj N).obj Q :=
  letI := SheafOfModules.monoidalCategory R
  v ⊗ₘ w
```

## Users

`tools/downstream.py Sheaf.Paper.PerfectProjectionFormula --uses ordinaryTensorHom`
reports 1,197 import descendants, and exactly one module using this declaration:

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.PerfectProjectionFormula | H4 | Same definitionally equal type and unchanged value; unit coherence is proved. |

There are no external declaration users to adapt. The target's interpretation is
unchanged; the explicit type records the same ordinary tensor and actual unit.

## Status

landed 20261020T051358-L-1658222 2026-10-20 (merge of deliver/H4/Sheaf.Paper.PerfectProjectionFormula)
