## What changed

Proved six of the seven theorem declarations in `Sheaf.Paper.SignedLineScalarTensorTower`.
Private basis and tensor helpers construct the signed comparisons and prove their
tensor, tower and identity laws by local coefficients. The proof reuses the proved private
basis-coordinate and scalar-extension basis-isomorphism API of
`ScalarExtensionDualLocalIso` through a proof-only `import all`.
All eleven existing public signatures, four definition bodies and public imports of the
item are unchanged.

Changed the unclaimed `InvertibleTensorScalarExtensionDefinitions.scalarTensorPower`
recursion to an ordinary recursor on positive exponents. Its original three computation
rules are proved explicitly, and a private all-exponent equality proof verifies preservation
of the original construction. Adapted three simplification steps in
`InvertibleTensorScalarExtension` and one `rw` in `CommonLinePositiveScalarPowers`;
these changes are forced by dependent intermediate types exposed by the new recursor.
The adapted consumers compile in 27.1 and 38.5 seconds. Other consumer checks and original
controls are recorded in `coord/changes/X8-scalar-tensor-power-recursion.md`.
The six-proof item compiled on the project server in 47.1 seconds.
Local elaboration commands are recorded in
`coord/changes/X8-signed-line-proof-elaboration.md`. No adopted source-library file changes.

## Proved and sorry left

Closed: `existsUnique_signedLineBasisPowers`, `signedLineDual_isIso`,
`exists_signedLineComparison`,
`signedLineComparison_tensor`, `signedLineComparison_tower`, and
`signedLineComparison_identity`. The item closes 6 of 7 holes. The existing
`existsUnique_signedLineProduct` remains `sorry` at
`lem-pur-signed-line-scalar-tensor-tower`; no new holes were added; 0 statements were split off. The three new computation theorems
`scalarTensorPower_zero`, `scalarTensorPower_one` and `scalarTensorPower_succ` are proved
by reflexivity and attached to the existing data node
`def-sp-scalar-tensor-comparison-data`.

Unchanged consumer hole: `SheafOfModules.exists_positiveScalarPowers` in
`Sheaf.Paper.CommonLinePositiveScalarPowers` remains `sorry`
(node `lem-pur-common-line-positive-scalar-powers`). Its proof is not changed by this packet.

## No longer needed

Removed imports of `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing` and
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal`; the proof
uses the existing scalar/tensor generator APIs for the six completed clauses.
The unfinished product clause retains its complete original proof plan in its docstring.
The removed DAG dependencies and tool-use entries are
`lem-pur-sheaf-hom-cover-gluing` and
`lem-pc-sites-sheaf-tensor-bilinear-universal`. Their modules are no longer needed by this
proof. All other declared dependencies remain used.

## Where the brief, the DAG or earlier work was wrong

The completed comparison clauses do not need the separate cover-gluing or
bilinear-universal imports. A full product proof was developed using internal-Hom
gluing, but did not meet the full-module compile limit; that proof is not in this packet.
The original named product theorem remains for the next worker. The canonical scalar dual
local-isomorphism and tower-core APIs already provide the needed dual and associator
formulas.

## Forced adaptations

`Sheaf.Paper.InvertibleTensorScalarExtension` is unclaimed. Against the changed ordinary
recursor, its three simplification steps left dependent occurrences of
`scalarTensorPower R M (n + 1)` exposed as `Nat.rec`; the original compiler error was a
type mismatch in the successor comparison. The three changed simplification lists now use
`scalarTensorPower_zero`, `scalarTensorPower_one`, and
`simp only [scalarTensorPower_succ]`, respectively. These are the only changed lines in
that module and the adapted file compiles.

`Sheaf.Paper.CommonLinePositiveScalarPowers` is unclaimed. Its successor `rw` produced the
same dependent type mismatch after the recursor was exposed; changing that one `rw` to
`erw` supplies the definitional equality. The adapted file compiles and its public
signature is unchanged.

## Second reading by X8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
