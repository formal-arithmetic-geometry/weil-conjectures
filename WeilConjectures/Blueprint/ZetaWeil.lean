/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

/-!
# Zeta functions and the Weil conjectures

The zeta-function layer: the trace series and its logarithm, the Euler product over
closed points, the trace-to-determinant factorization, the rationality criterion and its
descent, root purity, weight separation and duality reciprocity, and the assembly of the
five Weil statements from the trace formula, Poincaré duality and the weight estimate.

The zeta function and the two headline statements are already formalized, as
`AlgebraicGeometry.Scheme.zetaSeries` in `WeilConjectures.ZetaSeries` and
`WeilConjectures.zetaSeries_rational` and `WeilConjectures.weil_conjectures` in
`WeilConjectures.Statement`. Statements here cite those and are added only for the nodes
with no counterpart there.

Blueprint block `sec-zeta-weil`.
-/
