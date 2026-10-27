## What changed

Preserved the statement and public import of
`AlgebraicGeometry.squareResolution_localClass`. Its proof transports the open equality,
precomposes the complex-level local-class calculation with the supplied restricted-resolution
section comparison, and postcomposes with the supplied classical resolution comparison.
The final identity uses the explicit integer-to-natural-degree homology factors.
The final files compile without warnings: the item in 41.6 seconds, the local-class statement
in 13.4 seconds, and the generic comparison in 4.6 seconds (later cached).

Added proof-only imports of `Sheaf.AlgebraicGeometry.DirectImageComplexLocalClass` and
`Sheaf.CategoryTheory.TotalClassicalResolutionComparison`. No existing shared definition,
public signature, source-library declaration or other existing module was changed.
The original module's transparency options now respect transparency.

The total/classical comparison is proved for every additive functor between the stated
abelian categories and every supplied injective resolution. The proof derives the compatibility
of the total and bounded-below units, first computes on the chosen resolution, and then uses
an augmentation-preserving resolution comparison and naturality to handle the supplied one.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.squareResolution_localClass`, node
`lem-weil-pbc-square-resolution-local-class`, by reduction to the complex local-class calculation
and a completely proved total/classical comparison.

Proved `CategoryTheory.Functor.totalClassicalResolutionComparison`, node
`lem-weil-pbc-total-classical-resolution-comparison`, including its private unit, normalization
and naturality helpers, without adding a hole to that module.

One new hole remains: `AlgebraicGeometry.directImageComplex_localClass`, node
`lem-weil-pbc-direct-image-complex-local-class`. This is the cocycle/sheafification step of the
original argument, without a coefficient object, augmentation, classical derived functor or
restricted-resolution choice. It states the actual maps on a nonnegative complex whose integer
extension is K-injective. Its source and complete proof in words are in its docstring and node.
The zero complex, degree zero and empty open require no additional hypotheses.

Thus one existing hole is closed and one strictly smaller local computation is added: this is
a decomposition, with net hole change zero, not a claim that the entire item is axiom-free.

## No longer needed

No original import was removed and no module was withdrawn. The proof does not need to
construct a restricted injective resolution: `RestrictedResolutionSections` already supplies
it. The former proof dependency `lem-weil-pbc-module-open-restriction-injectives` and its module
`WeilConjectures.AlgebraicGeometry.ModuleOpenRestrictionInjectives` are therefore unnecessary
for this argument. The former proof dependency `lem-weil-pbc-higher-direct-image-presheaf`
and its module `Sheaf.Paper.HigherDirectImagePresheaf` do not identify the normalized local-class
map and are not used. Their declarations and any uses elsewhere remain intact.

`src-right-derived-functor-plus-compatibility` remains needed through the proved total/classical
comparison. `lem-trf-unbounded-direct-image-section-presheaf` remains needed through the
complex-level local-class calculation and the original definitions. No blueprint unit's own
statement or realized proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The four original dependencies do not directly state the normalization identity required by
the second proof step. The universal-property statement for the higher direct-image presheaf
alone cannot identify that fixed map. This delivery isolates exactly the remaining local
cocycle calculation and proves the distinct total/classical normalization step rather than
repeating the original obligation under a different name. No original statement was found false.

## New nodes

`lem-weil-pbc-total-classical-resolution-comparison` is the completely proved generic comparison
between total derived cohomology and classical derived cohomology computed on an arbitrary
supplied resolution. Its module is `Sheaf.CategoryTheory.TotalClassicalResolutionComparison`.

`lem-weil-pbc-direct-image-complex-local-class` is the remaining local sheafification calculation
on a nonnegative K-injective model. Its module is
`Sheaf.AlgebraicGeometry.DirectImageComplexLocalClass`. It is strictly the cocycle step, separate
from the now-proved total/classical and resolution-transport argument.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
