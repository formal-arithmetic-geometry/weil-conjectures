## What changed

Reduced `AlgebraicGeometry.exists_constant_fibre_dimension_neighbourhood_of_depth_eq_ringKrullDim`
without changing its signature, visibility, existing docstring, or public imports.
The main module imports two new proof modules. It constructs the fibre map of a chart,
proves the pullback square by cancellation, applies base-change instances, transports
local dimension through an open fibre immersion, and intersects the chart open with W.
Both transport lemmas are private, fully proved Lean declarations.

`Sheaf.AlgebraicGeometry.CohenMacaulayFlatQuasiFiniteChart` states the geometric chart
construction from the first half of the proof of Stacks 00RH. Its conclusion consists
of morphisms, flatness, local quasi-finiteness, finite presentation, and a composition
identity; it contains no fibre-dimension constancy conclusion. It is the remaining
construction task, rather than a renaming of the original dimension statement.

`Sheaf.AlgebraicGeometry.FlatQuasiFiniteSmoothDimension` is completely proved.
For each source neighbourhood its image is nonempty and open by 01UA. The existing
smooth dimension theorem computes the target and image dimensions. Quasi-finiteness
bounds the source dimension above, while flat quasi-finite coheight invariance bounds
it below. This works for finite inseparable maps and nonreduced finite flat sources;
no etaleness or separability hypothesis was added.

Added an attachment node for the already proved source-library smooth dimension theorem,
so the new proof's DAG records the actual tool it uses. The source theorem and coheight
theorem were read and checked with `#print axioms`: only `propext`, `Classical.choice`,
and `Quot.sound`. The three delivered Lean modules compile in import order.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.exists_constant_fibre_dimension_neighbourhood_of_depth_eq_ringKrullDim`
(node `lem-sbc-cohen-macaulay-fibre-dimension-neighbourhood`). There is no sorry in the
item module, including either private transport lemma.

Added one hole:
`AlgebraicGeometry.exists_flat_quasiFinite_chart_of_fibre_depth_eq_ringKrullDim`
(node `lem-sbc-cohen-macaulay-flat-quasi-finite-chart`), in its own new module.
Its proof is exactly `by sorry`; its docstring states the source and complete chart argument.

Also fully proved the new theorem
`AlgebraicGeometry.topologicalKrullDimAt_eq_of_flat_quasiFinite_to_smooth`
(node `lem-sbc-flat-quasi-finite-smooth-local-dimension`).
The attachment node `lem-sbc-smooth-fixed-dimension-over-field` introduces no declaration
and no hole.

This delivery is a decomposition: one original hole closed and one construction hole
added, hence zero net holes closed. The dimension calculation and all combination and
transport work are proved; the chart construction is not claimed proved.

## No longer needed

No original imports were removed: all six public imports support the existing statement.
The original direct proof dependencies are replaced by the two new modules.

`lem-sbc-restricted-fibre-locally-noetherian`
(`Sheaf.AlgebraicGeometry.RestrictedFibreLocallyNoetherian`) is no longer used on this
proof route. The chart argument works with finite-type affine fibre algebras and the
existing finite-type-field dimension theorem instead. This does not assert that the
module is globally unreachable from other targets.

The original algebraic dependencies remain required by the chart construction:
`lem-weil-pbc-dimension-at-point-local-ring-trdeg`,
`lem-weil-pbc-quasi-finite-over-polynomial-algebra`,
`lem-weil-pbc-miracle-flatness`, `lem-weil-pbc-criterion-flatness-fibre`, and
`lem-weil-pbc-openness-of-flatness`. They were not pruned or imported as unused
proof dependencies of the main theorem. The local-dimension definition is still used.
The dimension calculation after the chart no longer needs a residue-field
transcendence-degree comparison or miracle flatness; it uses the proved coheight tool.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The DAG's single long step had not exposed the chart
construction as a Lean interface. The needed interfaces were inspected: polynomial
factorization is a ring-level theorem, while the main goal is a statement about scheme
fibres and arbitrary source opens. The new chart module isolates that construction;
the main proof now supplies the remaining geometric combination in Lean.

The existing dimension-partition and zero-dimensional-stalk neighbourhood modules
cannot supply a shortcut: they depend on this item. They were not imported.
The unit's realized statement and steps are empty in its record; the polynomial-chart
route of 00RH is preserved, and no unit-level assertion is bypassed.

The local literature checkout contains citation lists but not the Stacks source.
The authoritative online texts of 00RH and 0A21 were read. LeanSearch returned an
Internal Server Error, recorded as unavailable. LeanFinder, Loogle, Mathlib grep,
source-library searches, and whole-blueprint searches were performed; no exact
Mathlib chart or flat quasi-finite dimension theorem was found.

## New nodes

`lem-sbc-cohen-macaulay-flat-quasi-finite-chart`: the first part of 00RH's construction,
with a single named sorry and the original algebraic proof dependencies.

`lem-sbc-flat-quasi-finite-smooth-local-dimension`: a fully proved field-level theorem,
combining openness, the smooth dimension theorem, and the closed source coheight tool.
The coheight node belongs to another unit but is an already proved source-library tool;
its use does not replace the polynomial-chart route of the current unit.

`lem-sbc-smooth-fixed-dimension-over-field`: attaches
`AlgebraicGeometry.topologicalKrullDim_eq_of_smoothOfRelativeDimension` from the source
library, with its exact signature, proof location and standard-axiom check.

No change record or forced adaptation is needed; no existing interface was changed.

## Second reading by U2

1. Compared the delivered item module with the repository version. The target theorem
   signature, visibility, docstring, and original public imports are unchanged; only
   proof imports, private helpers, and the proof body were added. Verdict: pass.
2. Compiled all three delivered modules in import order with `lcompile.py`. The target
   and the dimension theorem have no errors or forbidden declarations; the only
   remaining `sorry` is the named chart theorem. Axioms are standard, with `sorryAx`
   occurring only through that intentionally split chart theorem. Verdict: pass.
3. Checked the new chart and dimension statements against their docstrings and DAG
   nodes. The chart exposes only the geometric construction needed by the target, and
   the dimension theorem is strictly lower-level and includes no constancy conclusion.
   No duplicate library declaration was found in source searches. Verdict: pass.
4. Read the proof route from the target downward. It uses the chart node, the proved
   flat quasi-finite smooth dimension node, and the explicit open-fibre transport; the
   chart construction and polynomial route of the unit are retained. The attachment
   node records the existing smooth dimension theorem. Verdict: pass.
5. Checked the DAG `proof`, `proof_deps`, `proof_origin`, Lean records, and report
   against the delivered imports and declarations. The new nodes and the split hole
   agree with the Lean files, and the removed dependency is documented under
   `## No longer needed`. Verdict: pass.

I changed only this second-reading report section; no Lean proof or statement required
repair after compilation and axiom checks.
