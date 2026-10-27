## What changed

Replaced the sole `sorry` in
`AlgebraicGeometry.Scheme.Hom.exists_etale_open_of_regular_coordinate_fibre`
with a complete Lean proof from one new numerical lemma and existing library
declarations. The theorem's signature and public imports are unchanged. No
shared definition, existing module other than the item, or target is changed.

The proof establishes local finite presentation by permanence, obtains formal
unramifiedness from `unramifiedLocus_baseChange` applied to the given cartesian
square, and proves flatness on the base fibre by regular-local depth and miracle
flatness. The pointwise fibrewise flatness criterion then proves flatness of the
actual stalk map. A proved private affine-chart argument transports this map to
prime localizations and applies the existing étale-at-prime criterion to produce
the requested basic open neighbourhood.

The new module
`Sheaf.AlgebraicGeometry.RegularCoordinateFibreDimensionFormula` isolates the
numerical comparison from the last paragraph of Stacks Tag 0FUE. The item imports
it privately. Both node records describe the actual revised route. All three
private helpers in the item have complete proofs; no private hole is introduced.

## Proved and sorry left

Original holes: 1. Closed in the item: 1, namely
`AlgebraicGeometry.Scheme.Hom.exists_etale_open_of_regular_coordinate_fibre`
(node `lem-pur-etale-near-regular-coordinate-fibre`). The item itself now has
zero `sorry` occurrences.

Added holes: 1, namely
`AlgebraicGeometry.Scheme.Hom.fibre_dimension_formula_of_regular_coordinate_fibre`
(node `lem-pur-regular-coordinate-fibre-dimension-formula`), in its own new module.
Its proof is exactly `:= by sorry`; its docstring gives the source and full
argument in words. This is a decomposition, not a net proof: one upper hole
closed minus one lower hole added gives zero net holes closed by this packet.
The upper theorem still depends on this numerical obligation, as well as the
existing declarations used by its proof.

The proved private helpers are `regular_local_depth_ge`,
`flat_of_regular_dimension_formula`, and
`etale_open_of_flat_unramified_stalk`. The last one includes both the transport
between stalks and affine prime localizations and the construction of an actual
étale neighbourhood; these steps are not delegated to a new hole.

## No longer needed

Removed these proof imports from the item:

- `WeilConjectures.RingTheory.SmoothFibreRegularLocal`
- `Sheaf.RingTheory.SmoothOverFieldRegularLocal`
- `WeilConjectures.RingTheory.Etale.LocalDimension`
- `WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints`
- `WeilConjectures.RingTheory.FlatOfFlatClosedFiber`
- `Sheaf.RingTheory.RelativeRegularEquationsBaseChange`

The smooth-fibre regularity, relative-regular-equation base change, étale local
dimension, and étale-fibre declarations remain dependencies of the numerical
node. They are not claimed as globally pruned work. The item uses the existing
smooth-stalk regularity API directly, and uses the already stated scheme-level
fibrewise criterion instead of assembling its ring-localization version from
`FlatOfFlatClosedFiber` inside this file. The explicit Nakayama/differentials
base-change descent planned in the old final step is replaced by the already
proved unramified-locus base-change theorem. Localization of differentials is
still used in the private affine argument.

No node or module is withdrawn. No source-library declaration is removed.
No globally pruned module is claimed. The unit's realized statement and proof
steps remain unchanged.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original plan left substantial affine and
fibre-stalk identifications implicit. Existing scheme-level APIs for fibrewise
flatness and base change of the unramified locus close those steps without new
geometry lemmas. The parent node now names these dependencies and the separate
numerical comparison. The original theorem, including all binders and the
coordinate regularity hypothesis, is preserved.

The remaining dimension argument has not been formalized by this delivery;
calling the result an unconditional completed proof would be inaccurate. No
consumer adaptations or change record are needed because no existing interface
changes.

## New nodes

`lem-pur-regular-coordinate-fibre-dimension-formula` is realized by
`Sheaf.AlgebraicGeometry.RegularCoordinateFibreDimensionFormula` and asserts only
`dim L = dim T + dim(L / m_T L)` for the actual map between the local rings of
the two base fibres. It is strictly the numerical step before miracle flatness
in Tag 0FUE: it supplies neither flatness, formal unramifiedness, finite
presentation nor an open étale neighbourhood. The combining proof supplies all
of those. Its proof plan identifies the two regular-sequence quotients, compares
their dimensions through the étale slice, and identifies the closed local fibre
as a field. Dependencies for each step are existing stated nodes. The record
includes a self-contained statement, source, complete proof plan, search records,
and the verbatim Lean statement.

Edge cases checked in words: when `b = 0`, both regular sequences are empty and
the argument reduces to the dimension and closed-fibre statements for an étale
map. When `a = 0`, the slice is étale over the base and its fibre local ring has
dimension zero. The point `y` ensures all relevant local rings and quotient
points are nonempty; the argument makes no assertion about a nonexistent point
on an empty scheme. The residue-field and pullback identifications use precisely
the maps in the statement, not a different local homomorphism. No change records
are added.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
