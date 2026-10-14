# determinant_split_comparison_restriction

## Reason

Rebase the returned repair onto the current repository. The current restriction
helper is true and proved; the earlier false arbitrary-tuple statement was already
corrected upstream. Retire the substitution helper by inlining its only use.
Preserve the canonical proof using the existing linear-map construction and local
bijectivity; do not replace it with a new sorry.

## Old

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
            (homOfLE hZW).op y) := by
  intro W Z hW hZW y
  simpa only [hd] using hn W Z hW hZW y

```

## New

The helper is removed. The empty compatibility module retains a private infrastructure
import for declaration probes. In the canonical comparison, remove only the private
local-module import and replace the helper application with:

```lean
  · intro W Z hW hZW y
    exact hn W Z (hW.trans hVU) hZW y
```

All surviving signatures, visibility, definitions and target statements are unchanged.
The historical local-construction attachment is retired consistently with its existing
statement_change; its current canonical realization remains unchanged.

## Users

A repository-wide search for both retired names finds only the restriction helper's
own module and its canonical caller. Other importers do not use either name.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.Modules.DeterminantSplitComparison | unclaimed | forced proof adaptation after helper removal; signature unchanged |

The original caller fails against the empty local module at the removed helper's
identifier. Its linear construction, bijectivity imports and proof are retained.
No definitions change, so no target meaning changes.

## Status

landed 20261014T092935-L-608889 2026-10-14 (merge of deliver/K3/Sheaf.AlgebraicGeometry.Modules.DeterminantSplitComparisonLocal)
