## What changed

Proved `AlgebraicGeometry.generic_fibre_points_smooth` in
`Sheaf.TraceFormula.GenericFibrePointsSmooth` without changing its signature.
The proof uses geometric reducedness as already supplied by `hred s`, density
of the fibre smooth locus, the existing dense-open/component-generic-point
lemma, and the proved pointwise flat-fibre smooth-locus criterion. The chosen
neighbourhood is exactly `p.smoothLocus`; Mathlib's open-immersion smooth-locus
API proves its restriction is smooth.

Removed two private proof imports and added private imports of
`WeilConjectures.AlgebraicGeometry.FlatFibreDimensionStrataCover` and
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber`.
Updated the item's proof, proof_deps and proof_origin to this argument.
Public imports and all existing declarations' signatures are unchanged.

Repair of the return for head `d30874104`: removed the inherited
`set_option warn.sorry false` line. The landing scanner treated the option's
name as an unattributed hole at line 24, although the theorem body was complete.
Warnings now use Lean's default setting; no proof hole is suppressed or added.

Validation: the module compiles through lcompile.py (10.6 seconds, then 3.0
seconds with the explicit pointwise-criterion import). `#print axioms` reports
exactly `propext`, `Classical.choice`, and `Quot.sound`; there is no `sorryAx`.
The repaired file compiles in 4.4 seconds; the hole scanner reports no markers
or warnings. Both added imports pass tools/import_direction.py. No new Lean module,
statement, definition, or consumer adaptation is necessary. Empty fibres
have no supplied component generic point; no nonemptiness is assumed.
The argument also handles reducible fibres using the component lemma, and
uses the density theorem over arbitrary residue fields, without a perfect-field
assumption. The unit's realized statement and steps are unchanged.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.generic_fibre_points_smooth`
(node `lem-trf-generic-fibre-points-smooth`).
Added 0 holes; split off 0 holes; 0 sorries remain in the delivered Lean file.
This is a proof, not a decomposition. Every invoked theorem has a complete
proof in the current source; no new intermediate Lean statement was introduced.

## No longer needed

Removed proof imports:
- `Sheaf.AlgebraicGeometry.SmoothAtPointFibreCriterion`;
- `Sheaf.RingTheory.GeometricReducednessFiniteInseparableTest`.

The item's direct proof no longer needs:
- `lem-trf-smooth-at-point-fibre-criterion`: its needed implication is already
  proved as `Scheme.Hom.fiberι_mem_smoothLocus` in the source library;
- `lem-trf-geometric-reducedness-algebraic-closure-test` and
  `Sheaf.AlgebraicGeometry.GeometricallyReducedAlgebraicClosureTest`: the Lean
  hypothesis already gives geometric reducedness of each residue-field fibre;
- `lem-trf-geometric-reducedness-finite-inseparable-test` and its module above:
  likewise no conversion of a weaker reducedness hypothesis is needed;
- `lem-weil-pbc-lfp-affine-opens-finite-presentation`,
  `lem-weil-pbc-finite-presentation-base-change-composition`, and
  `lem-weil-pbc-fibre-product-affine-spectra`: explicit affine chart construction
  is replaced by Mathlib's finite-presentation base-change instance.

These are removals from this proof's dependencies, not withdrawal requests:
other consumers may still need all these nodes and modules. Both existing
approved tool uses (fibre density and component generic points) are retained.
No source-library declaration or module is removed or changed.

## Where the brief, the DAG or earlier work was wrong

The old DAG Step 1 converts reducedness of one algebraic-closure base change
into geometric reducedness. The actual Lean hypothesis `hred` already states
`GeometricallyReduced` for every residue-field fibre, so that preparation is
redundant. The source library has already proved the exact pointwise implication
needed in Step 3, so importing the still-unproved Sheaf equivalence is unnecessary.
No mathematical statement was corrected or weakened.

The returned landing failure was caused by the inherited warning-suppression
option being counted as an unattributed hole. Removing that unnecessary option
repairs the packet without changing the theorem or its proof.

## New nodes

`lem-trf-flat-fibre-smooth-locus-image` attaches the existing, proved
`AlgebraicGeometry.Scheme.Hom.fiberι_mem_smoothLocus` in
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber` (lines 154-202).
It states the implication for a globally flat, locally finitely presented
morphism, with an arbitrary point in an arbitrary fibre. This is strictly
separate from generic-point density and is the precise interface used here.
Source: Stacks morphisms.tex, Tag 01V9, (2) implies (1).
LeanSearch, Loogle, Mathlib grep, local library grep and blueprint search were
run. Mathlib searches found smooth-locus APIs but not this implication; direct
source-library search found its existing complete proof. No Lean module or
hole is added for this node. No definition or statement changes. The diagnostic
option removal is documented in
`coord/changes/X7-generic-fibre-smooth-warning-option.md`, including all 45
downstream consumers; no consumer adaptation is necessary.

## Second reading by X7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
