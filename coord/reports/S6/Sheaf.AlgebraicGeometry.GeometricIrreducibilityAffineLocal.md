## What changed

Replaced the single `sorry` in
`AlgebraicGeometry.geometricallyIrreducible_affineLocal`, in
`Sheaf.AlgebraicGeometry.GeometricIrreducibilityAffineLocal`, with a proof of both
implications and the nonempty-open assertion. Its signature and docstring are unchanged.
Added the proof-only import `Mathlib.Topology.Sets.OpenCover`.

The forward implication and the nonempty-open assertion use Mathlib's open-immersion
instance, with nonemptiness giving surjectivity to the spectrum of the base field.
For the converse, work in an arbitrary field-valued pullback square. Its first projection
is surjective by the two Mathlib leaves recorded in the DAG. Index by all nonempty affine
opens of X; their inverse images cover the pullback, are irreducible by the hypothesis and
pullback pasting, and meet pairwise by irreducibility of X and surjectivity of the projection.
`IsPreirreducible.of_subset_iUnion` proves preirreducibility; surjectivity also supplies
nonemptiness. This implements all three existing DAG steps without changing the route.

## Proved and sorry left

Closed: `AlgebraicGeometry.geometricallyIrreducible_affineLocal`
(node `lem-zl-geometric-irreducibility-affine-local`), the sole original hole.
No `sorry` remains in the module. No holes are added or split off.
Single-file `lcompile.py` passed with exit code 0 in 3.4 seconds and no diagnostics.
Delivery preflight supplies the independent axiom probe before push.

## No longer needed

None. No imports are removed and no nodes or modules are pruned. Both declared proof
dependencies, `lem-pc-field-extension-surjective` and
`lem-weil-pbc-surjective-base-change`, are used through their recorded Mathlib instances.

## Where the brief, the DAG or earlier work was wrong

The retained proof had elaboration defects: pullback schemes needed explicit coercions
to their underlying types in `IrreducibleSpace` and `isIrreducible_univ`, and the pairwise
intersection relation used unqualified `on` notation. The cover member also needed to be
unfolded explicitly to the inverse-image set. These are repaired without changing any
statement or mathematical step.

The prior attempt's compile-server outage is no longer the only diagnostic: this attempt's
initial dry run reached Lean and reported those elaboration errors. The retained report's
claim that no dry run had been attempted is superseded by this report.

No mathematical discrepancy found. Stacks Tag 038G in `literature/stacks-project/varieties.tex`
and both dependency nodes and their Mathlib declarations were read. LeanFinder, Loogle,
the search service's grep and searches of both library roots found no existing affine-local
converse. The nonempty-open hypotheses are unchanged; no reducedness, finite-type,
separatedness or quasi-compactness hypothesis is introduced. The unit route is preserved.

## Second reading by S6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
