## Worker report

The module states `AlgebraicGeometry.Scheme.IdealSheafData.exists_section_of_ample_ideal`.
The scheme `Y` and its quasi-compactness are rendered by `{Y : Scheme.{u}} [CompactSpace Y]`;
`M` is an invertible module via `(M : Y.Modules) [M.IsInvertible]`, and ampleness is
`hM : Scheme.Modules.IsAmple Y M`. The quasi-coherent ideal sheaf is Mathlib's
`J : Y.IdealSheafData`, whose affine-local ideal-sheaf data is represented by
`J.toModules`; the point outside its zero set is `hy : y ∉ (J.support : Set Y)`.
The conclusion gives `n : ℕ` with `0 < n`, a global section `u : Γ(M.tensorPow n, ⊤)`,
and a preimage `v` in `Γ(J.toModules.tensorObj (M.tensorPow n), ⊤)` under the tensor of
`J.toModulesι` with the identity, followed by the left unitor. The final clause is
`y ∈ Scheme.Modules.nonvanishingLocus (M.tensorPow n) u`, exactly the nonvanishing locus
used by the ample-module definition.

Dependencies used: `Sheaf.AlgebraicGeometry.Ample`, declaration
`AlgebraicGeometry.Scheme.Modules.IsAmple`; Mathlib/WeilConjectures declaration
`AlgebraicGeometry.Scheme.IdealSheafData` and its `toModules`, `toModulesι`, `support`.
The tensor map is `CategoryTheory.MonoidalCategoryStruct.tensorHom`, and sections are
`AlgebraicGeometry.Scheme.Γ` notation.

Edge cases checked: `n` is explicitly positive (so the zero power is excluded); no
nonemptiness of `Y` or of the ideal is assumed, so the empty scheme and zero ideal retain
their vacuous behavior; arbitrary universe `u` is retained.

Searches: `msearch.py leanfinder/loogle/grep` and `rg` over Mathlib, WeilConjectures,
and `lean/Sheaf` for ample ideal sections and `lem-sc-ample-ideal-section`; no existing
statement was found. `IsAmple` in `Sheaf.AlgebraicGeometry.Ample` is the dependency,
while the source repository's `IsAmple` is a different relative very-ample notion.
No statement fault or `STATEMENT-DISPUTED` applies.

## Earlier second reading (a previous round; superseded)

The node and module were read clause by clause. `CompactSpace Y`, invertibility, ampleness,
ideal support complement, positive tensor power, ideal-tensor preimage, and nonvanishing
locus all appear explicitly. The Mathlib `IdealSheafData` representation supplies the
quasi-coherent ideal sheaf and its support; no additional hypothesis was introduced.

## Second reading by K1

I reread the Stacks Proposition 01Q3 statement and the Lean declaration clause by clause. The
introduced objects and their Lean renderings are: a quasi-compact scheme `Y` is
`{Y : Scheme.{u}} [CompactSpace Y]`; an ample invertible module is `(M : Y.Modules)` with
`[M.IsInvertible]` and `hM : Scheme.Modules.IsAmple Y M`; a quasi-coherent ideal sheaf is
`J : Y.IdealSheafData`, represented by `J.toModules` and inclusion `J.toModulesι`; and a point
outside its zero set is `{y : Y}` with `hy : y ∉ (J.support : Set Y)`. These match the node's
objects and hypotheses without extra finiteness, separatedness, characteristic, or universe
assumptions.

The conclusion is rendered as `∃ n : ℕ, 0 < n`, followed by a section
`u : Γ(M.tensorPow n, ⊤)`, a section
`v : Γ(J.toModules.tensorObj (M.tensorPow n), ⊤)`, and the equality expressing that `u` is the
image of `v` under the ideal inclusion tensored with the identity and the left unitor. This is
exactly the node's section of `J M^{⊗ n}` viewed in `M^{⊗ n}`; the final clause
`y ∈ Scheme.Modules.nonvanishingLocus (M.tensorPow n) u` is exactly `y ∈ Y_u`. Quantifier
order and positivity agree. The explicit preimage `v` records membership in the image sheaf and
introduces no stronger mathematical conclusion than the node's notation.

Edge cases checked: `n = 0` is excluded by `0 < n`; no nonemptiness of `Y`, no nonzero ideal,
and no characteristic assumption is added, so empty schemes and zero ideals retain the source's
vacuous behavior. The universe is arbitrary (`Scheme.{u}`), with no independent test universe.

I searched Mathlib, `WeilConjectures`, and `lean/Sheaf` with `rg` and the recorded
LeanFinder/Loogle/grep searches for ample ideal sections and `lem-sc-ample-ideal-section`; no
existing declaration states this result. `IdealSheafData.toModules` and `toModulesι` are the
recorded project bridge for Mathlib's ideal-sheaf data, and `Scheme.Modules.IsAmple` is the
recorded ample notion. The source repository's other `IsAmple` declaration is a different
relative very-ample notion.

No mismatch was found, so no Lean or node statement change was required. The module compiled
cleanly with `scompile.py` (only the permitted `sorry` declaration remains).
