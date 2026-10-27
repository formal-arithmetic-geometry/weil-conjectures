## What changed

Replaced the hole in
`AlgebraicGeometry.EtaleChartTaylor.exists_unique_taylor_iso` by a complete assembly
from finite polynomial jets. All existing public signatures, definitions and public
imports are unchanged.

The proved private helper `taylor_of_finite_jets` works over an arbitrary Noetherian
local ring with a specified coefficient-field map and centered coordinates. It
identifies the finite quotient maps with the maps induced by polynomial evaluation,
applies the existing proved
`RingTheory.pair_henselization_completion_data`, and composes with Mathlib's
`MvPowerSeries.toAdicCompletionAlgEquiv`. It proves the Taylor formula, scalar and
coordinate images, uniqueness by completion extensionality, bijectivity, locality,
the maximal-ideal formula, and residue normalization. In dimension zero it proves
both scalar bijections; surjectivity before completion uses the injective completion
map of a Noetherian local ring.

The remaining geometric input is stated in the new module
`Sheaf.AlgebraicGeometry.EtaleChartFiniteJets`. This is the finite-level part of
original proof steps 1--3 and 5, together with their Noetherianity and maximal-ideal
generation assertions. It asserts no power-series map, inverse-limit statement,
uniqueness, local isomorphism, residue normalization or dimension-zero scalar
bijection. Its natural-language proof specifies how the original declared
geometric dependencies establish it. Its statement includes r=0 and n=0.

New proof imports are `Mathlib.RingTheory.AdicCompletion.Noetherian`,
`Mathlib.RingTheory.MvPowerSeries.Equiv`, `Mathlib.RingTheory.MvPowerSeries.Inverse`,
`WeilConjectures.RingTheory.PairHenselizationCompletionData`,
`WeilConjectures.RingTheory.PowerSeriesQuotientVariables`, and
`Sheaf.AlgebraicGeometry.EtaleChartFiniteJets`. The item's node now follows this proof.

Validation: both modules compile through lcompile.py. The finite-jet module
compiled in 2.8 seconds and the final item in 9.5 seconds, without warnings.
The item's public theorem statement and public import list were compared with
the repository version and are unchanged.

## Proved and sorry left

Closed upper hole:
`AlgebraicGeometry.EtaleChartTaylor.exists_unique_taylor_iso`
(node `lem-trf-etale-chart-rational-point-taylor-iso`). The assigned module has zero
remaining holes. The private helper `taylor_of_finite_jets` is fully proved.

Added one hole:
`AlgebraicGeometry.EtaleChartTaylor.rational_point_finite_jets`
(node `lem-trf-etale-chart-rational-point-finite-jets`), in
`Sheaf.AlgebraicGeometry.EtaleChartFiniteJets`.

This is a decomposition: one upper hole closed, one lower hole added, net zero.
No hole is added to a definition or an anonymous/private declaration. The separate
polynomial-completion node is an exact Mathlib leaf and adds no hole.

## No longer needed

The item no longer directly imports:

- `Mathlib.AlgebraicGeometry.AffineScheme`
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`
- `Mathlib.AlgebraicGeometry.Noetherian`
- `Mathlib.RingTheory.FiniteType`
- `Mathlib.RingTheory.Localization.Submodule`
- `Sheaf.AlgebraicGeometry.UnramifiedMaximalIdealResidueCriterion`
- `Sheaf.AlgebraicGeometry.UnramifiedMorphism`
- `Sheaf.RingTheory.MonoidCompletionCoefficients`
- `WeilConjectures.RingTheory.FlatLocalCompletionIso`

`lem-trf-monoid-completion-coefficients` and its module
`Sheaf.RingTheory.MonoidCompletionCoefficients` are unnecessary for this route:
Mathlib already supplies the exact polynomial variables-adic completion equivalence
and its truncation formula. No claim is made that other consumers cease to need them.

The other geometric dependencies of the original proof remain needed by the new
finite-jet node: etale base change, affine space and polynomial coordinates,
affine-stalk localization, Noetherianity and its local-finite-type permanence,
etale/flat/unramified notions, the unramified maximal-ideal criterion, and flat local
completion comparison. Local completion locality, adic completion, power series,
and localization are retained where used. The old direct tool-use entries `lem-weil-pbc-flat-local-completion-iso` and
`pqf-lem-locnoeth-lft` are removed from the parent node; the finite-jet argument
still uses both. No module is withdrawn and no source
library declaration is removed. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition was found. The original plan's use of the much
more general monoid coefficient theorem is unnecessary: the exact polynomial
completion equivalence is already in the pinned Mathlib. The original item
Docstring retains the original proof plan; the updated node and implemented proof
record the shorter completion argument.

The geometric assertion is tested on the identity affine-space chart, an open
subscheme containing the point, r=0 (both quotient rings are zero), n=0 (the
rational etale stalk is the coefficient field), and arbitrary field extensions.
No global finite-type or quasi-compactness hypothesis is introduced.

## New nodes

`lem-trf-etale-chart-rational-point-finite-jets` is the one unfinished geometric
step, with its own module, source, full proof in words, and Lean statement. It
inherits the original chart's field extension, rationality and structural scalar
normalization and records exactly the induced finite quotient maps.

`lem-trf-polynomial-variables-adic-completion` records the exact Mathlib
polynomial-completion equivalence, polynomial-image formula and truncation formula.
It needs no new Lean module or proof. Searches used LeanSearch, Loogle and grep;
Loogle found the exact declarations and their sources were read.

No change record is required: no existing interface or definition changes.

## Second reading by T2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
