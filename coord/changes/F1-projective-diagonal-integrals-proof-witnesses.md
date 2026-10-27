# AlgebraicGeometry.Etale.projectiveLine_diagonal_integrals

## Reason

Consumer validation found a 69-second kernel-heavy compile, above the 60-second
limit. Profiling found roughly 40 seconds of kernel checking both with and
without the F1 overlay. The proof destructured Chern arrows and a transport
system but used only the supported Ext representative and its boundary clause.
The already proved ordinary_supported_kummer_uniqueBoundary provides exactly
those data. Use it directly; no extra statement or hole is introduced. This
module was unclaimed when adapted. The theorem signature, public imports and
mathematical proof steps remain unchanged.

## Old

```lean
  obtain ⟨κ, c, c₁, t, hc, hκ, hκc, hκc₁, hκt⟩ :=
    ordinary_supported_kummer (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N hN A hA hT
      (pullback.diagonal (ProjectiveLine S ↘ S)) hI
```

## New

```lean
  obtain ⟨κ, hκ, _⟩ :=
    ordinary_supported_kummer_uniqueBoundary
      (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N hN A hA hT
      (pullback.diagonal (ProjectiveLine S ↘ S)) hI
```

A private proof import of OrdinarySupportedCartierKummer names the existing
helper. No definition body, public attribute or statement is changed.
The revised proof compiled in 23.8 seconds (c53d3ad0ff31b284cee94e2f);
the subsequent change only wraps its overlong application line.

## Users

The theorem's signature is unchanged; importers need no adaptation. Its users
are included in the compatibility validation documented in report.md.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalIntegrals | unclaimed | proof only; fewer witness types |
| Sheaf.AlgebraicGeometry.FiniteP1DiagonalKummerComponentFormula | F1 | same public import |

## Status

landed 20261026T222636-L-676965 2026-10-26 (merge of deliver/F1/Sheaf.AlgebraicGeometry.FiniteP1DiagonalKummerComponentFormula)
