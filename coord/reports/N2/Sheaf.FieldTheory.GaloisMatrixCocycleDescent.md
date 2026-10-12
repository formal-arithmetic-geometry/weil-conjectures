## What changed

Replaced the sole sorry in `Sheaf.FieldTheory.GaloisMatrixCocycleDescent` with a
complete proof from matrix Hilbert 90. All existing signatures and public imports
are unchanged. Added the proof-only import `Sheaf.FieldTheory.GaloisMatrixHilbert90`
and four Mathlib proof imports for fixed fields, finite-dimensional descent and
finrank calculations.

The private `Field.fixed_matrix_descent` is fully proved: fixed entries uniquely
come from K, entrywise preimages form an algebra homomorphism, faithful scalar
extension proves injectivity, and equal finite dimensions prove surjectivity.
The private `Field.matrixConjugation` explicitly constructs an algebra automorphism
and its inverse, with all structure proofs closed. The main proof conjugates e
and uses the invariant-basis equation to prove its entries are Galois-fixed.

The new Hilbert 90 statement concerns only the prescribed cocycle b and no algebra
D or splitting e. It is strictly the invariant-basis step of the original argument,
not a restatement of algebra descent. The node copy records this route.

## Proved and sorry left

Closed the original hole `Field.exists_algHom_matrix_of_galois_cocycle`
(node `lem-sc-galois-matrix-cocycle-descent`). Its proof is conditional on the
new matrix Hilbert 90 theorem. There are no sorries in the item's module.

Added exactly one hole: `Field.exists_galois_matrix_invariant_basis` in
`Sheaf.FieldTheory.GaloisMatrixHilbert90`, node `lem-sc-galois-matrix-hilbert90`.
Its proof is exactly `by sorry`; its docstring contains the finite quotient,
invariant averaging, automorphism independence and basis extraction argument.
This is a decomposition, with one hole closed and one added, hence net zero
holes, not an unconditional proof of the whole descent theorem.

The two private helpers are proved with no sorry. In particular, the fixed-entry
construction uses witnesses supplied by a proved Mathlib fixed-field theorem,
whose base-field preimages are unique by injectivity of the algebra map. No public
definition chooses arbitrary data from an unproved existence theorem.

The entire delivered set compiles cleanly through lcompile.py. The dimension and
faithful extension argument covers n=0 as well as n>0, and no restriction on the
characteristic or central simplicity is added.

## No longer needed

No existing import, node or module was pruned. The original node had no named
proof dependencies. All original public imports are retained for its unchanged
statement. The proof needs no separate finite-Galois descent of the algebra D,
or choices of a finite field containing coefficients of e and e inverse:
infinite-Galois fixed fields and faithful extension plus finrank handle that
step directly. Only the cocycle's invariant-basis step remains open.

## Where the brief, the DAG or earlier work was wrong

The existing node's single non-elementary proof step had no named dependencies.
This delivery makes the matrix Hilbert 90 step explicit and fully proves the
remaining descent. The existing node and statement are unchanged mathematically.

The Stacks source is a sketch, not a ready-made general-linear Hilbert 90 proof.
Read https://stacks.math.columbia.edu/tag/03R7 and the original parent node's
invariant averaging expansion; the new theorem documents that expansion rather
than claiming the source supplies the Lean argument. Local literature is absent
on this machine, so the source was read online. LeanSearch returned HTTP 500;
this is recorded as unavailable, not as a negative search result. LeanFinder,
Loogle and source grep ran successfully. Mathlib scalar Hilbert 90 does not
state the general-linear result. The existing matrix algebra invariant scalar
map theorem concerns conjugation actions on matrices, not an invariant basis
for the prescribed semilinear action on vectors, so it is not applied as if it
were matrix Hilbert 90.

Checked the new statement at n=0 (trivial general linear group), trivial b
(t=1), separably closed K (trivial Galois group), and arbitrary characteristic
(no averaging division). The cocycle identity forces b(1)=1 without an added
normalization hypothesis. The fixed-entry proof uses the infinite Galois
fixed-field theorem, avoiding an erroneous finite-dimensional assumption on
SeparableClosure K.

The unit `sk-thm-br` realizes no internal nodes here; its Brauer-injectivity/Tsen
route is untouched. Blueprint searches for matrix Hilbert, Galois descent and
fixed matrix returned no match. Hilbert 90 matched only the scalar Picard/units
nodes, not this result. The ancestor helper could not resolve this existing
node's module-valued created.item; the new node follows the parent split node's
recorded blueprint ancestor `lem-sc-brauer-zero` and records the intervening
nodes explicitly.

## New nodes

`lem-sc-galois-matrix-hilbert90`, in
`dag/nodes/sec-curve-estimates/lem-sc-galois-matrix-hilbert90.json`, states the
invariant-basis part of general-linear Hilbert 90 for a locally constant absolute
Galois cocycle. Its new module is
`lean/Sheaf/FieldTheory/GaloisMatrixHilbert90.lean`, with the public declaration
`Field.exists_galois_matrix_invariant_basis`. The statement is independent of
D and e, and the main module formally carries out all descent from its witness.
No change record or forced adaptation is needed: all existing interfaces stay
identical and every added import is proof-only.

## Second reading by N2

1. Compared `Sheaf.FieldTheory.GaloisMatrixCocycleDescent.lean` with the repository version. The public theorem signature and all existing declarations are unchanged byte for byte; the added `GaloisMatrixHilbert90` module is a new split-off node, and its statement matches the recorded DAG node.

2. Compiled both delivered modules with `lcompile.py --all`; compilation succeeds with no errors. The descent theorem has no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The only remaining `sorry` is the named split theorem `Field.exists_galois_matrix_invariant_basis`, with its source, proof sketch, and node recorded. The proved theorem's generated axioms are limited to the permitted base axioms plus the split theorem's `sorryAx` through its explicit dependency.

3. Checked the split-off invariant-basis statement at `n = 0`, the trivial cocycle, separably closed fields, and arbitrary characteristic. It is independent of `D` and `e`, is strictly the invariant-basis step needed by the descent proof, and is not duplicated by Mathlib or existing `lean/Sheaf` declarations according to the recorded searches.

4. Read the proof top down. It uses the split theorem, explicit matrix conjugation, infinite-Galois fixed-entry descent, faithful scalar extension, and finite-dimensional rank comparison. The route preserves the `sk-thm-br` unit route through the matrix cocycle node. No old proof dependency or import became unused; all added imports are proof-only imports.

5. Checked both DAG nodes against the Lean declarations. The descent node records the exact proof steps and its sole named dependency; the Hilbert-90 node records the new theorem, source, proof steps, and `status: split`. No unit `realized` entry requires modification.

I changed only this report section; no Lean proof or statement required repair after compilation and comparison.
