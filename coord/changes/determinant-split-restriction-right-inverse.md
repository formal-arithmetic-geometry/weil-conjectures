# AlgebraicGeometry.Scheme.Modules.determinant_split_comparison_restriction

## Reason

Upstream review #1428 rejected the old unconstrained `c` generator statement because of a
sectionwise rescaling counterexample. The repository already landed the naturality-family repair;
this delivery records the repaired interface while keeping callers compatible.

## Old

```lean
theorem determinant_split_comparison_restriction {X : Scheme.{v}}
    (S : ShortComplex X.Modules) (r₁ r₂ r₃ : ℕ)
    (V : X.Opens) (d : ∀ (W : X.Opens), W ≤ V →
      (exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃).val.obj (op W)
        ≃ₗ[X.presheaf.obj (op W)] (exteriorSheaf S.X₂ r₂).val.obj (op W))
    (d₀ : ∀ (W : X.Opens), W ≤ V →
      (exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃).val.obj (op W)
        →ₗ[X.presheaf.obj (op W)] (exteriorSheaf S.X₂ r₂).val.obj (op W))
    (hn : ∀ (W Z : X.Opens) (hW : W ≤ V) (hZW : Z ≤ W) y,
      (exteriorSheaf S.X₂ r₂).val.map (homOfLE hZW).op (d₀ W hW y) =
        d₀ Z (hZW.trans hW)
          ((exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃).val.map
            (homOfLE hZW).op y))
    (hd : ∀ W hW y, d W hW y = d₀ W hW y) :
    ∀ (W Z : X.Opens) (hW : W ≤ V) (hZW : Z ≤ W) y,
      (exteriorSheaf S.X₂ r₂).val.map (homOfLE hZW).op (d W hW y) =
        d Z (hZW.trans hW)
          ((exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃).val.map
            (homOfLE hZW).op y)
```

## New

```lean
theorem determinant_split_comparison_restriction {X : Scheme.{v}}
    (S : ShortComplex X.Modules) (r₁ r₂ r₃ : ℕ)
    (V : X.Opens) (d : ∀ (W : X.Opens), W ≤ V →
      (exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃).val.obj (op W)
        ≃ₗ[X.presheaf.obj (op W)] (exteriorSheaf S.X₂ r₂).val.obj (op W))
    (dNatural : ∀ (W : X.Opens), W ≤ V →
      (exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃).val.obj (op W)
        →ₗ[X.presheaf.obj (op W)] (exteriorSheaf S.X₂ r₂).val.obj (op W))
    (hn : ∀ (W Z : X.Opens) (hW : W ≤ V) (hZW : Z ≤ W) y,
      (exteriorSheaf S.X₂ r₂).val.map (homOfLE hZW).op (dNatural W hW y) =
        dNatural Z (hZW.trans hW)
          ((exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃).val.map
            (homOfLE hZW).op y))
    (hd : ∀ W hW y, d W hW y = dNatural W hW y) :
    ∀ (W Z : X.Opens) (hW : W ≤ V) (hZW : Z ≤ W) y,
      (exteriorSheaf S.X₂ r₂).val.map (homOfLE hZW).op (d W hW y) =
        d Z (hZW.trans hW)
          ((exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃).val.map
            (homOfLE hZW).op y)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Modules.DeterminantSplitComparison | unclaimed | This delivery only renames d₀ to dNatural; no positional caller adaptation is required. |

## Status
landed 20261013T222408-L-1225049 2026-10-13 (merge of deliver/P2/Sheaf.AlgebraicGeometry.Modules.DeterminantSplitComparisonLocal)

Complete; the delivered module compiles.
