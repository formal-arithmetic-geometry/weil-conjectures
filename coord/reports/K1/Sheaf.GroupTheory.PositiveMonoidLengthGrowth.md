## What changed

Proved `AddSubmonoid.positiveMonoid_length_growth` in
`Sheaf.GroupTheory.PositiveMonoidLengthGrowth`, following all seven steps of
`lem-trf-positive-monoid-length-growth`. Updated that node's proof descriptions
and proof origin to describe the implementation.

The private, proved helpers construct the attained maximal decomposition length
using `Nat.findGreatest`; obtain finite words in nonzero generators; prove weight
and coordinate bounds; embed bounded-length points into a finite integer box;
select independent generators by spanning rational coordinates; and compare the
finite convolution with the independent lower box and the upper coordinate box.
The polynomial bounds use the constants `a / (3^d * (4*r*W)^r)` and
`b * (2*C+1)^r`. Rank zero is handled separately by the zero lattice and a
singleton convolution. The theorem's signature and existing docstring are preserved.
All added imports are private proof imports, and all added declarations are
proved private helpers.

Read ILO Expose VI, section 1.6(i)--(ii), printed page 70 (PDF page 76), and the
current blueprint's `sk-i-curve-zero` section. As the node already records, ILO
provides the formal-model context; the lattice counting refinement is agent supplied.
The unit route is preserved.

## Proved and sorry left

Closed the sole original hole:
`AddSubmonoid.positiveMonoid_length_growth`
(node `lem-trf-positive-monoid-length-growth`).

Holes closed: 1. Holes added: 0. Holes left: 0. Split statements: 0.
All thirteen private helper theorems are proved. Both rank zero and exponent zero
are covered, as are zero monoid elements and the boundary case `n = 2` of the
convolution estimates.

Validation uses the project remote single-file compiler and the delivery's
preflight and axiom probe.

## No longer needed

Removed the redundant direct proof import
`Mathlib.LinearAlgebra.LinearIndependent.Lemmas`; its API is available through
`Mathlib.LinearAlgebra.Dimension.Constructions`, which is used for coordinate
space dimension and independent-subfamily selection.

No DAG nodes or project modules are pruned. The declared basis and the two
linear-algebra Mathlib leaves remain used: their selection and dimension
arguments are packaged by `Submodule.exists_fun_fin_finrank_span_eq`.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The elementary steps in the DAG require
substantial formal glue for finite words, subtype cardinalities, scalar
restriction, and natural division; all that glue is now proved in the item.

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
