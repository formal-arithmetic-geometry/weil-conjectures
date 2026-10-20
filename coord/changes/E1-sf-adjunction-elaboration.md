# sfModelDerivedAdjunction and sfModelWeilDerivedAdjunction

## Reason

Replace `unfold` by `delta` for the explicitly named right-adjoint definition.
This avoids simplification of the newly proved adjoint-existence witness. The
result remains the same `Adjunction.ofIsLeftAdjoint` with the same explicit proof.
The two public types and irreducibility attributes are unchanged.

## Old

```lean
def sfModelDerivedAdjunction (f : X₀ ⟶ Y₀) :
    zlPull D l hl Ω f ⊣ sfModelDerivedPush D l hl Ω f := by
  unfold sfModelDerivedPush
  exact @Adjunction.ofIsLeftAdjoint _ _ _ _ (zlPull D l hl Ω f)
    (sfModelPull_isLeftAdjoint D l hl Ω f)

def sfModelWeilDerivedAdjunction (f : X₀ ⟶ Y₀) :
    IsoAlgebra.mapOfNatIso (zlFrobeniusSquare D l hl Ω f) ⊣
      sfModelWeilDerivedPush D l hl Ω f := by
  unfold sfModelWeilDerivedPush
  exact @Adjunction.ofIsLeftAdjoint _ _ _ _ (IsoAlgebra.mapOfNatIso (zlFrobeniusSquare D l hl Ω f))
    (sfModelWeilPull_isLeftAdjoint D l hl Ω f)
```

## New

```lean
def sfModelDerivedAdjunction (f : X₀ ⟶ Y₀) :
    zlPull D l hl Ω f ⊣ sfModelDerivedPush D l hl Ω f := by
  delta sfModelDerivedPush
  exact @Adjunction.ofIsLeftAdjoint _ _ _ _ (zlPull D l hl Ω f)
    (sfModelPull_isLeftAdjoint D l hl Ω f)

def sfModelWeilDerivedAdjunction (f : X₀ ⟶ Y₀) :
    IsoAlgebra.mapOfNatIso (zlFrobeniusSquare D l hl Ω f) ⊣
      sfModelWeilDerivedPush D l hl Ω f := by
  delta sfModelWeilDerivedPush
  exact @Adjunction.ofIsLeftAdjoint _ _ _ _ (IsoAlgebra.mapOfNatIso (zlFrobeniusSquare D l hl Ω f))
    (sfModelWeilPull_isLeftAdjoint D l hl Ω f)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.SfCommonStageDirectImage | E1 | Same adjunction types; proof elaboration avoids simplification. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed | Same irreducible adjunction and counit API; no adaptation. |
| Sheaf.Paper.DlConstantFieldCharts | G8 | Same irreducible adjunction and counit API; no adaptation. |
| Sheaf.Paper.WeilOpenImageDelta | E7 | Same irreducible adjunction and counit API; no adaptation. |

The consumer modules are unchanged. No target statement or mathematical definition
changes. The selected adjunction retains its universal-property normalization.

## Status

landed 20261020T051204-L-1589890 2026-10-20 (merge of deliver/E1/Sheaf.Paper.SfCommonStageDirectImage)
