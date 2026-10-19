## What changed

Proved `AlgebraicGeometry.affineLine_connectedComponents` in
`Sheaf.AlgebraicGeometry.PurityAffineLineComponents` using existing Mathlib openness and
geometric irreducibility of affine-space projections. The punctured fibres are nonempty
preirreducible inverse images under the open embedding. The quotient-map component formula
then gives both component identities, and explicit unit-section points prove all three
intersection clauses. Updated the existing node’s proof and proof dependencies to this route.
The theorem’s signature, visibility, definitions and public imports are unchanged.

## Proved and sorry left

Replaced the sole original hole with a complete proof body:
`AlgebraicGeometry.affineLine_connectedComponents`
(node `lem-pur-a1-components`). Original holes: 1. Holes left: 0. Holes added: 0.
No result was split off and no other module was modified. The single-file compiler accepted
this proof in 3.2 seconds. The resumed session repaired the pointwise unit-section identity
by applying `congrArg` to `AffineSpace.oneSection_comp_over`; the previous unfolding-based
rewrite did not match. The final version compiles cleanly and passes `deliver3.py --no-push`, including the
declaration/axiom probe and server preflight. The dry run classifies the delivery as CODEX
because the existing DAG node is updated.

## No longer needed

Removed the proof imports:

- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber`
- `Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen`
- `Mathlib.AlgebraicGeometry.Fiber`
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`
- `Mathlib.Algebra.Polynomial.Basic`
- `Mathlib.Algebra.Field.Defs`

The separate smoothness-to-openness route is unnecessary:
`sbc-lem-affine-space-smooth`, `sbc-lem-smooth-criterion`, and
`lem-weil-pbc-flat-lfp-open`. Mathlib `AffineSpace.isOpenMap_over` supplies openness.
The explicit fibre calculation and domain proof need no additional direct dependencies on
`def-pc-scheme-fibre`, `def-pc-fibre-product`, `def-weil-polynomial-ring`, `def-weil-field`,
or `def-weil-affine-spectrum`: the affine-space geometric irreducibility instance already
contains them. These nodes are removed only from this node’s proof dependencies;
statement dependencies remain unchanged. Retained `Mathlib.Topology.Connected.Clopen` and
the existing connected-fibre quotient node, whose result underlies the component formula.
No public import was removed and no module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement repair was needed. The ten-step plan expanded results already
proved by Mathlib. The proof uses no finiteness or separatedness assumptions on the base,
and no special complement property beyond the supplied open immersion and unit lift;
all original hypotheses stay in the signature. Thus disconnected/nonreduced bases and
arbitrary nonclosed base points require no extra argument. The unit’s component/section
route remains intact, and its realized records were not changed. Read the current
main-20261015 statement, the older complete proof, the unit record, the cited dependency
signatures, Mathlib’s geometric irreducibility proof and component theorem, and Stacks
`topology.tex` labels `lemma-connected-fibres-quotient-topology-connected-components`
and `lemma-connected-fibres-connected-components` (0377/0378).

## Second reading by M9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
