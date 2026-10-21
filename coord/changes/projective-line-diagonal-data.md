# Projective-line diagonal data module move

## Reason
The diagonal projection, chart, trace, and alpha definitions are needed by the
split-off Chern and trace statements. Their declarations are housed in a public
data module so those statements can import the data without importing the
parent theorem and creating a cycle.

## Old
The four declarations were defined in
`Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalIntegrals`.

## New
The declaration bodies are in
`Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalData`; the target publicly imports
that module. Signatures and visibility are unchanged.

The data module also holds two new declarations (reviewer fix): the chart
pushforward `projectiveLineDiagonalChartPushforward` (the trace's prefix, formerly in
`ProjectiveLineDiagonalChernComponents`) and the factorization lemma
`projectiveLineDiagonalTrace_eq`. Both are owned by `def-amb-p1-diagonal-data`.

## Users
`Sheaf.AlgebraicGeometry.FiniteP1ArbitraryBaseIntegrals`;
`Sheaf.AlgebraicGeometry.FiniteP1DiagonalAlpha`;
`Sheaf.AlgebraicGeometry.FiniteP1DiagonalKummerComponentFormula`;
`Sheaf.AlgebraicGeometry.ProEtaleProjectiveLineTrace`.

## Status

landed 20261021T014706-L-2445300 2026-10-21 (merge of deliver/G4/Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalIntegrals)
