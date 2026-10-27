## What changed

Proved `AlgebraicGeometry.Scheme.Hom.smooth_pair_blowup_local_models` with its exact
existing signature and all four existing definitions unchanged. Added four proved private
helpers for polynomial-coordinate reindexing, pullback of the coordinate-center ideal,
the first-factor canonical blowup projection, and equality transport of the blowup map.
Only the assigned Lean module and its DAG node change.

Local finite presentation follows directly from the already proved source-library
`locallyOfFinitePresentation_of_comp`, using smoothness of the two structure maps and
`hi`. The proved `Scheme.Hom.fg_ideal_ker` then supplies the finite-type ideal condition.
The existing simultaneous-coordinate theorem supplies the chart and its generators.
The remainder explicitly computes the polynomial ideal pullback and assembles the two
specified canonical flat comparisons and their projection identities. The etale conclusion
uses base change and composition instances.

Validation: the delivered module compiled cleanly through `lcompile.py` in 5.0 seconds.
All lines are at most 100 characters; all existing public signatures and definition bodies
are unchanged, and the only changed node fields are `proof`, `proof_deps`, and `proof_origin`.

The sole new proof import is
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`.
The DAG now records the actual route, including the proved cancellation and kernel
base-change tools. The inherited unit route and the two approved tool uses are retained.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.Hom.smooth_pair_blowup_local_models`
(node `lem-trf-smooth-pair-blowup-local-models`).
Added 0 holes; split off 0 statements. There are no textual `sorry` declarations in the
delivered module. Existing imported coordinate-theory dependencies remain available
for subsequent work; they are not claimed proved by this delivery.

## No longer needed

Removed the proof import `Sheaf.AlgebraicGeometry.ClosedImmersionFinitePresentationIdeal`
and the dependency `lem-trf-closed-immersion-finite-presentation-ideal`: the two smooth
structure maps and proved finite-presentation cancellation give the required immersion
finiteness directly. The planned finite-generator gluing across the center and its
complement is unnecessary. No other original direct import or original proof-dependency
node is removed, and no existing module is withdrawn.

The local-coordinate theorem's regular-sequence, cartesian-coordinate-square and etale
center-map conclusions are unused; its simultaneous chart and generator conclusions are
still essential. The coordinate-subspace blowup-chart theorem is not used; the existing
public module is retained because its polynomial-ring and center definitions occur in
the statement and existing definitions.

## Where the brief, the DAG or earlier work was wrong

The planned finite-type gluing argument and subsequent application of the unproved
closed-immersion finite-presentation criterion were longer than necessary. The adopted
source library already proves both cancellation of local finite presentation and finite
generation of the kernel on affine opens of a closed immersion locally of finite
presentation. This is a proof-route improvement, with no statement or definition repair.

The polynomial comparison uses the existing Sum.inr variables and the supplied
finSumFinEquiv/ULift reindexing exactly. The equality transport is checked over V,
so neither canonical comparison is replaced by an unconstrained isomorphism.
Edge cases remain valid: empty C makes the chart clause vacuous, empty P and R=0 are
allowed, b=0 is handled by empty spans, and a=0 uses the same coordinate equivalence.
No positivity, nontriviality or compactness assumption is added.

## Second reading by Y3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
