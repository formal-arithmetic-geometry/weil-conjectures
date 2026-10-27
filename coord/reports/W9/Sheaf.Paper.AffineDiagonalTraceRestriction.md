## What changed

Replaced the single hole in `Sheaf.Paper.AffineDiagonalTraceRestriction` by an
assembly of actual integration isomorphisms and the diagonal cancellation calculation.
The private, proved helper `presentedTranspose_isIso` applies the existing
`AlgebraicGeometry.Etale.affineCoordinateCounit_baseChange` to the tower counit
transpose. The unit-coherence theorem identifies its last unit comparison with
identity. All remaining factors of the presented transpose are canonical
isomorphisms, including the exceptional mate of the coordinate isomorphism.
This applies uniformly to the original projection, self-product projection,
and normalized normal-cone presentation.

Two strictly smaller transport obligations have separate modules and nodes:
the ordinary etale self-product trace equation, and the section coherence of
ordered Tate coefficients. The main proof applies the comparison functor,
cancels the source comparison and the pulled-back exceptional mate, and uses
naturality of the section compositor. Statements and definitions are unchanged.
The old module's public construction import is retained; added proof imports
are private. The existing node's proof and proof dependencies now describe this route.

## Proved and sorry left

The original module had one hole. Closed its body in
`WeilConjectures.PurityFiniteSetting.affineDiagonalTraceRestriction`.
The private `presentedTranspose_isIso` has a complete proof.

Added two holes, so this is a decomposition, not a net proof gain:

- `WeilConjectures.PurityFiniteSetting.affineDiagonalPresentedTranspose_selfBaseChange`
  in `Sheaf.Paper.AffineDiagonalPresentedBaseChange`, node
  `lem-pur-affine-diagonal-presented-base-change`.
- `AlgebraicGeometry.Etale.orderedTateSectionPullback` in
  `Sheaf.AlgebraicGeometry.OrderedTateSectionPullback`, node
  `lem-pur-ordered-tate-section-pullback`.

The first is only the ordinary self-product equation, with no normal-cone
objects, existential isomorphisms, invertibility or diagonal restriction.
The second concerns only canonical coefficient pullbacks along an arbitrary
section; it has no integration, trace, exceptional inverse image or normal cone.
The original theorem is unchanged and is assembled from these two equations
and existing declarations. No data is selected from an unproved existence theorem:
the three isomorphisms are `asIso` of the original explicitly defined maps.

## No longer needed

No public imports or library modules are removed. No module is withdrawn.
The main proof no longer directly uses the vector-bundle purity theorem,
the vector-integration site comparison, the unit-input projection-coherence
lemma, the finite compact-support projection formula, or pro-etale compact-support
base change. Invertibility instead uses the already stated actual ordered-counit
transpose theorem. The first new transport obligation still uses ordinary
affine counit base change and the trace-transpose argument. Thus no claim is
made that those underlying modules can be deleted. No unit route is bypassed. Concretely, the old main-node proof dependencies
`lem-pur-vector-integration-site-comparison`, `thm-amb-vector-bundle-purity`,
`lem-pur-projection-formula-coefficient-coherence`,
`lem-weil-finite-compact-projection-formula`, and
`thm-cbc-finite-level-proetale` are not needed by the new assembly.
`lem-weil-pbc-finite-type-over-noetherian` and `sbc-lem-affine-space-smooth`
remain encapsulated in the existing construction interfaces.
`lem-amb-affine-space-top-trace` and `lem-pur-trace-transpose-base-change`
are used in the first new step's proof plan.
`lem-weil-pbc-proetale-derived-pullback-composition` is replaced in the
assembly by the explicit ordinary etale section compositor already used by
`diagonalComparedRestriction`, followed by the comparison functor.
The existing `lem-trf-section-coordinate-counit-normalization` is used only
as a generic theorem about the ordinary tower transpose: the proof takes
`affineCoordinateCounit_baseChange`'s invertibility clause, with no trace-formula
or deformation conclusion.

## Where the brief, the DAG or earlier work was wrong

The original proof plan's geometric argument is applicable, but the concrete
Lean declarations do not directly state the required coefficient/presentation
transport equations. `affineCoordinateCounit_baseChange` already supplies the
actual tower transpose's invertibility, making the longer projection-formula
route unnecessary for this item. The remaining missing glue is recorded precisely
as the two new steps. Rank zero gives the identity tower; empty schemes and
the zero coefficient ring do not invalidate either transport equation.

## New nodes

`lem-pur-affine-diagonal-presented-base-change` is Step 3 of the item's
source argument, specialized to the explicit product coordinate presentation.
Its proof in words explains the ordered counit base-change equation, compact-support
and Tate transports, and exceptional adjunction transpose. Searches found no
existing concrete presented-transpose equation.

`lem-pur-ordered-tate-section-pullback` is the coefficient part of Step 4.
Its proof in words is induction on the ordered tensor length, using the
normalized root and pure-tensor line comparisons and the canonical derived
pullback composition/unit laws. Searches found generic pullback composition
lemmas, but no theorem about this concrete ordered coefficient comparison.

No definition or statement change records are required.

Validation: all three modules compiled through `lcompile.py`; the final proof
was checked with temporary profiling (42.2 seconds) and profiling was removed
before delivery. The scoped unused-variable linter option only covers the
unchanged original signature, whose existing `z` let is unused.

## Second reading by W9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
