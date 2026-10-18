## What changed

Proved `AlgebraicGeometry.locallyOfFiniteType_of_fpqcCover` without changing its signature.
Added the proof-only import `Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent`.
Kept the existing fpqc criterion: its affine descent hypothesis follows directly from
Mathlib's descent instance, since a map between affine schemes is quasi-compact.
Updated the theorem's proof description and its node's proof, proof dependencies and origin.
The unit sk-thm-p1's realized statement and proof steps are unchanged.
Compilation through lcompile.py succeeded (1.9 seconds, no warnings).

## Proved and sorry left

Closed the original single hole in `AlgebraicGeometry.locallyOfFiniteType_of_fpqcCover`
(node `lem-weil-pbc-fpqc-descend-locally-finite-type`). Proved 1 of 1 original sorries;
0 holes added, 0 split off, 0 sorries left in the delivered Lean module.
The imported `AlgebraicGeometry.fpqc_local_on_base_criterion` is already proved.

## No longer needed

No original import was removed: both the public fpqc import and the proof-only criterion
import are used. No Sheaf statement modules from the longer affine-ring argument are
needed. The following original proof-dependency edges are removed:

- `def-weil-finite-type-morphism`
- `def-weil-pbc-finite-type-algebra`
- `def-weil-surjective-morphism`
- `def-pc-fibre-product`
- `def-weil-affine-spectrum`
- `lem-weil-pbc-flat-ring-map-iff-flat-affine`
- `lem-weil-pbc-flat-surjective-spectrum-faithfully-flat`
- `def-weil-pbc-faithfully-flat-ring-map`
- `lem-weil-pbc-open-preimage-fibre-product`
- `lem-weil-pbc-cartesian-square-pasting`
- `lem-weil-pbc-fibre-product-affine-spectra`
- `lem-weil-pbc-lft-affine-pairs`
- `lem-weil-pbc-finite-type-descends-faithfully-flat`
- `def-weil-pbc-fpqc-covering`

The definition nodes remain available through statement dependencies where relevant;
removing their redundant proof edges does not remove those notions from the statement.
The flatness/faithful-flatness and tensor-product lemmas are unnecessary as separate
steps here because Mathlib's existing single-morphism descent instance supplies their
combined argument. The pointwise criterion, base-change lemma and general fpqc
criterion remain dependencies. Pruning is local to this proof; other consumers may
still require the removed nodes.

## Where the brief, the DAG or earlier work was wrong

The earlier search correctly identified Mathlib's single-morphism descent instance,
but the six-step plan expanded its affine-ring proof unnecessarily. Combined with the
now-proved fpqc criterion, it gives the full covering-family statement immediately.
No mathematical statement or definition needed repair. The Mathlib leaf
`lem-galois-lft-formally-unramified-single-fpqc-descent` is reused for its independent
local-finite-type clause; no new node or cross-unit unproved tool is introduced.
The source read was Stacks descent.tex, lemma-descending-property-locally-finite-type
(Tag 02KX), including its application of Tag 02KP.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
