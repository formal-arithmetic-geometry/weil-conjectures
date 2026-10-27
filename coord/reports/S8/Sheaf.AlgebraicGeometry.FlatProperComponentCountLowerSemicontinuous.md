## What changed

Replaced the hole in `Scheme.Hom.geometricComponentCount_lowerSemicontinuous`
with a proof from a finite clopen partition adapted to the marked geometric fibre.
The signature is unchanged. The proof establishes finiteness independently from
Noetherianity, converts the existing base-change theorem from ENat.card to
Nat.card, identifies the marked component count with the partition size, intersects
the open images, injects the partition indices into nearby component quotients,
and descends the inequality along the open étale map.

Added `Sheaf.AlgebraicGeometry.ProperGeometricFibreClopenPartition`, containing
`Scheme.Hom.exists_etale_geometricFibre_clopen_partition`. This isolates steps 1,
2 and 4 of the original plan: Stein factorization, integral étale splitting and
connectedness of its marked geometric pieces. It assumes only properness and
states no semicontinuity or nearby-fibre cardinal inequality. It is a genuine
geometric construction step; the flatness, openness, component-cardinality and
neighbourhood arguments are proved in the item module.

Updated the item's DAG proof and proof dependencies, and supplied the new node
with its source, complete proof in words, Lean attachment and actual search records.
No statement or definition was changed, and no consumers need adaptation.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Hom.geometricComponentCount_lowerSemicontinuous`
(node `lem-weil-pbc-flat-proper-component-count-lower-semicontinuous`).
There are zero sorry proofs left in the item module.

Added one split-off hole:
`AlgebraicGeometry.Scheme.Hom.exists_etale_geometricFibre_clopen_partition`
(node `lem-weil-pbc-proper-geometric-fibre-clopen-partition`).
Its proof is exactly `by sorry`, with no data definition or arbitrary witness
chosen in a definition. This delivery is a decomposition: 1 hole closed, 1 added,
net 0, rather than a claim of eliminating the mathematical proof obligation.

The private helpers `finite_geometricComponents`,
`natCard_geometricComponents_baseChange`, and `card_le_of_clopen_partition`
are fully proved. The construction handles an empty fibre and a zero-piece
partition; the empty intersection is the whole base and the injection is empty.
The new lemma was also checked on these cases, a connected nonempty fibre,
and a split disconnected proper fibre. Pure inseparability is used only on the
intermediate marked fibres, never assumed of the original geometric fibre.

Validation: both delivered modules are checked with lcompile.py; final compiler
and preflight results are recorded by deliver3.py.

## No longer needed

Removed these private imports from the item module:
`Mathlib.Algebra.Algebra.Defs`,
`Mathlib.AlgebraicGeometry.Geometrically.Irreducible`,
`Mathlib.Topology.Connected.Basic`,
`Mathlib.FieldTheory.PurelyInseparable.Basic`,
`Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective`,
`Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`,
`Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`,
`Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`,
`WeilConjectures.AlgebraicGeometry.SteinFactorizationAffine`,
`Sheaf.AlgebraicGeometry.IntegralFibreEtaleSplitting`, and
`Sheaf.AlgebraicGeometry.SteinFiniteFibresResidueFields`.
Kept the universally-open import because the proof uses it directly. All
pre-existing public imports remain unchanged. The generic Noetherian topology
module, scheme Noetherianity, base-change invariance, and the partition module
are the private proof imports.

The Stein, splitting, purely inseparable and radicial dependencies remain in the
new partition node: they have been localized, not pruned from the argument.
The field-extension faithfully-flat tensor-product route and spectrum-surjectivity
nodes (`lem-weil-pbc-field-extension-base-change-faithfully-flat` and
`lem-weil-pbc-faithfully-flat-surjective-spectrum`) are unnecessary for this
proof: Mathlib's `Scheme.Pullback.exists_preimage_pullback` supplies a geometric
point above a compatible pair directly. No other modules are withdrawn, and
no claim is made that other consumers no longer need these nodes.

## Where the brief, the DAG or earlier work was wrong

No false statement or changed target was found. The old plan proves finiteness
by the full étale Stein partition; Noetherianity of each proper field fibre gives
it independently and is also the first paragraph of the cited Tag 0BUI proof.
The old nonemptiness argument expands faithfully flat tensor products; the
existing scheme-pullback point theorem gives the same conclusion directly.

The blueprint unit route is preserved. This item is below the unit's realized
statement and proof steps; the new node retains exactly the original Stein
splitting construction. The existing, closed Noetherian connected-component
instance is used as a generic tool from `lem-sfb-noetherian-connected-components-open`.

## New nodes

`lem-weil-pbc-proper-geometric-fibre-clopen-partition` states only the pointed
étale clopen partition for a proper morphism. Its source is Tag 0BUI's Stein
factorization and étale splitting paragraph. Its proof dependencies are the
original item's Stein and integral-splitting statements and the definitions
used for the singleton purely inseparable geometric fibres. LeanSearch and
LeanFinder returned general proper/étale definitions, not this construction;
the recorded Mathlib grep returned no match. Searches of the project modules,
DAG and blueprint found no existing equivalent statement. It remains one
strict geometric step, with no flatness or lower-semicontinuity conclusion.

`lem-weil-pbc-scheme-pullback-compatible-point` records the exact existing
Mathlib theorem `AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback`
(PullbackCarrier.lean:306-308), the compatible-point consequence of Tag 01JT.
LeanSearch, Loogle and grep each found that declaration. This is a Mathlib leaf,
with an existing attachment and no new Lean file or proof hole.

## Second reading by S8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
