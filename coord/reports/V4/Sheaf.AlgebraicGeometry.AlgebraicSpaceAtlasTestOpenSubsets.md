## What changed

Filled `AlgebraicGeometry.AlgebraicSpace.exists_atlas_test_open_subsets` in
`Sheaf.AlgebraicGeometry.AlgebraicSpaceAtlasTestOpenSubsets`, preserving its signature.
The proof follows Stacks 03BX and 03H4: choose the scheme fibre product, transport
scheme-test properties along its unique isomorphisms, prove naturality on residue-field
point classes, and establish the subset identities and openness by scheme topology.
Four proved private helpers handle naturality, equivalence of the common-field relation,
the conversion from equality of quotient classes to explicit witnesses, and transport
of a scheme-test property. Updated the item's DAG proof to record this conversion and
its existing Mathlib-leaf dependency. No other existing module or node is changed.

Validation: `lcompile.py` compiled the completed module cleanly in 4.3 seconds.
The existing public theorem signature is byte-for-byte unchanged; no `sorry` remains
in the Lean file, and every line satisfies the 100-character limit.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.AlgebraicSpace.exists_atlas_test_open_subsets`
(node `lem-a1-space-atlas-test-open-subsets`). Added zero holes; split off zero
statements. No `sorry` remains in the delivered module.

## No longer needed

None of the original proof dependencies is pruned. The proof uses the existing
`exists_scheme_fibreProduct_point` declaration and the scheme étale-open Mathlib leaf.
No project module or DAG node is withdrawn. The new proof imports are
`Mathlib.AlgebraicGeometry.PullbackCarrier`, `Mathlib.CategoryTheory.Limits.Yoneda`,
and `Mathlib.Data.Quot`; all support the proved helpers. No original import is removed.

## Where the brief, the DAG or earlier work was wrong

The planned invocation of the fibre-product point lemma needs a nontrivial interface
bridge: that lemma accepts explicit common-field witnesses, whereas this theorem uses
equality in `Point`, implemented by a generated `Quot`. The proof supplies the bridge,
including transitivity by a residue field of a point of the fibre product of two field
spectra. This is an implementation gap, not a false mathematical statement. The atlas
and test-map square properties are also transported explicitly, since the predicates
supply potentially different representing schemes. The fixed unit route is preserved.

## Second reading by V4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
