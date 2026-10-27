## What changed

Proved `AlgebraicGeometry.WeilSheaf.geometric_factors_pairwise_nonisomorphic`
with its original signature. Its proof finds the least positive Frobenius period
of a simple factor, chooses an eigenembedding, constructs the cyclic sum of its
distinct translates as a nonzero lisse Weil subobject, and compares the resulting
multiplicity-free decomposition with the given one.

Added `Sheaf.DeligneLaumon.SimpleFrobeniusEigenembedding`, whose theorem
`AlgebraicGeometry.WeilSheaf.exists_simple_frobenius_eigenembedding` is also
proved. It supplies the coefficient-linear structure locally, proves that the
Hom space embeds in a finite-dimensional stalk Hom space, and applies Mathlib's
eigenvalue theorem to the Frobenius return on this Hom space. Its hypotheses
require only a lisse Weil sheaf and one periodic embedded simple local system.
The main module imports it and the existing geometric-constituent API privately.
The original public import and every existing declaration signature are unchanged.
Updated the item's proof plan and added the helper's node.
Both modules compiled through `lcompile.py --all` (11 s and 17 s respectively);
the delivery additionally runs its compile and axiom probe.

## Proved and sorry left

Closed the original one hole in
`AlgebraicGeometry.WeilSheaf.geometric_factors_pairwise_nonisomorphic`
(node `lem-zl-geometric-multiplicity-one`). Proved the new theorem
`AlgebraicGeometry.WeilSheaf.exists_simple_frobenius_eigenembedding`
(node `lem-zl-simple-frobenius-eigenembedding`) completely as well.
There are zero remaining `sorry`s in either module and zero holes added.
This is a proof, not a decomposition into new unproved obligations.

## No longer needed

The proof no longer needs `lem-wf-schur-scalar`: it uses nonzero maps between
simple local systems being isomorphisms, but never scalar classification of
endomorphisms. The eigenvector lives directly in `Hom(S,V)` instead of a
multiplicity space obtained by identifying isotypic blocks. Thus grouping the
original factors into blocks, proving transitivity on those blocks, and
identifying their scalar matrix endomorphisms are unnecessary. The corresponding
proof dependency is removed from this item's node; no declaration or module is
withdrawn, and no existing import is removed. The unit's geometric-constituent
route and every parent statement are preserved.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed or changed. The original DAG describes a longer
isotypic-block route. The Hom-space eigenvector argument realizes the same
source eigenline while avoiding those constructions. The supplied semisimple
carrier already makes the isomorphism class of any embedded simple factor
periodic by a finite pigeonhole argument. This replaces the need to first prove
that Frobenius acts transitively on isotypic blocks. Both the finite-period
argument and the final comparison of decompositions are proved explicitly.

## New nodes

`lem-zl-simple-frobenius-eigenembedding`, in
`Sheaf.DeligneLaumon.SimpleFrobeniusEigenembedding`, is the proved periodic-simple
factor eigenembedding step from paragraphs 1--2 of the current blueprint proof.
It does not assume arithmetic irreducibility, a semisimple carrier, or a finite
simple decomposition. It concludes a compatible embedding for a single given
periodic simple factor, rather than multiplicity one. The case of period zero
is included; the proof's nontrivial Hom space comes from the supplied embedding
of the nonzero simple object. No change record is required: no existing shared
statement, definition, or public import changes.

## Second reading by H9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
