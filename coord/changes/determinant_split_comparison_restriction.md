# determinant_split_comparison_restriction

## Reason

Repair E2 of reviewer X-3eef1. The arbitrary tuple family in the old generator
hypothesis need not commute with restriction. For Spec(Q[t]), A=0, B=C=O_X,
f=0, g=id and ranks (0,1,1), take d_X=id, d_W=2 id on proper subopens,
and c_W=d_W. The formula holds but restriction to D(t) fails.
The corrected theorem transfers naturality from a given linear family by equality.
It is proved by substitution and applies to empty opens, zero rings and zero ranks.
No definition or target statement changes.

## Old

```lean
theorem determinant_split_comparison_restriction {X : Scheme.{v}}
    (S : ShortComplex X.Modules) (r₁ r₂ r₃ : ℕ) (hr : r₂ = r₁ + r₃)
    [S.X₁.IsFiniteLocallyFreeOfRank r₁] [S.X₃.IsFiniteLocallyFreeOfRank r₃]
    (V : X.Opens) (d : ∀ (W : X.Opens), W ≤ V →
      (exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃).val.obj (op W)
        ≃ₗ[X.presheaf.obj (op W)] (exteriorSheaf S.X₂ r₂).val.obj (op W))
    (c : ∀ (W : X.Opens), W ≤ V →
      (Fin r₃ → S.X₃.val.obj (op W)) → Fin r₃ → S.X₂.val.obj (op W))
    (hd : ∀ W hW (a : Fin r₁ → S.X₁.val.obj (op W))
      (b : Fin r₃ → S.X₃.val.obj (op W)),
      d W hW (tmulSection (exteriorSheafSection S.X₁ r₁ W a)
        (exteriorSheafSection S.X₃ r₃ W b)) =
      exteriorSheafSection S.X₂ r₂ W
        (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op W) (a j))
          (fun j ↦ c W hW b j) (Fin.cast hr i))) :
    ∀ (W Z : X.Opens) (hW : W ≤ V) (hZW : Z ≤ W) y,
      (exteriorSheaf S.X₂ r₂).val.map (homOfLE hZW).op (d W hW y) =
        d Z (hZW.trans hW)
          ((exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃).val.map
            (homOfLE hZW).op y)
```

## New

```lean
theorem determinant_split_comparison_restriction {X : Scheme.{v}}
    (S : ShortComplex X.Modules) (r₁ r₂ r₃ : ℕ) (_hr : r₂ = r₁ + r₃)
    [S.X₁.IsFiniteLocallyFreeOfRank r₁] [S.X₃.IsFiniteLocallyFreeOfRank r₃]
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

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Modules.DeterminantSplitComparisonLocal | V1 | Own interface corrected and proved; local construction signature unchanged. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantSplitComparison | unclaimed | Forced proof adaptation; retains the natural family from determinant_split_linear_maps_exists and its naturality while constructing equivalences. All signatures and visibility unchanged. |

These are all textual users reported by tools/downstream.py --uses.
Other downstream modules consume determinant_split_comparison_exists, whose statement,
visibility and definitions are unchanged; they require no adaptation or target review.

Changed caller lines: add proof-only imports at 14–15 for the linear-map existence
and bijectivity declarations. Replace proof lines 90–105: retain hn from the
unique natural construction, obtain a bijective chart, convert the original maps,
reuse hd₀ for the wedge formula, and pass hn plus definitional equality to the
corrected restriction theorem. This supplies the new hypotheses that the original
local theorem's conclusion does not contain. No other caller lines change.

## Status

landed 20261013T072409-L-1126183 2026-10-13 (merge of deliver/V1/Sheaf.AlgebraicGeometry.Modules.DeterminantSplitComparisonLocal)
