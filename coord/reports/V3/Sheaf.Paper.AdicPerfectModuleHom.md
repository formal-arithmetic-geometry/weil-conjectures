## What changed

Replaced the `adicPerfectModuleHom` hole by a complete finite-dual-basis argument.
For an arbitrary additive functor H on modules and additive functor F to a preadditive
category, an additive comparison natural under precomposition and bijective for source A
is bijective for every finite projective source. The proof explicitly reconstructs sections
and morphisms with a finite projective splitting. Injectivity follows coordinatewise;
surjectivity is the sum of coordinate preimages. This includes the empty rank-zero family.
The original theorem keeps its exact signature, two-variable naturality and successor law.

The remaining geometric assertion is in the new `Sheaf.Paper.AdicPerfectUnitHom` module:
construct the comparison, prove its naturality and successor law, and compute it on source A.
It does not assert the finite-free or finite-projective result. The generic reconstruction
and its specialization in the original module are proved Lean, not new assumptions.

Extracted the three existing functor definitions and their additive instances, without
changing their signatures or bodies, to `Sheaf.Paper.AdicPerfectModuleFunctors` to avoid an
import cycle. The original module publicly imports them and keeps its original public
imports. No consumer or adopted source-library module is changed. The sole direct importer,
`Sheaf.Paper.AdicPerfectHomCochains`, was checked unchanged against the extraction.
Remote compilation passed: the item in 17.1 s and its importer in 40.7 s; the new
functor and rank-one modules previously compiled in 11.5 s and 11.4 s respectively.
The unchanged temporary consumer copy was then removed from the packet.

## Proved and sorry left

Closed one existing hole: `AlgebraicGeometry.Scheme.adicPerfectModuleHom`, node
`lem-sfb-adic-perfect-module-hom`. The item now contains zero sorry occurrences.

Added one hole: `AlgebraicGeometry.Scheme.adicPerfectUnitHom`, node
`lem-sfb-adic-perfect-unit-hom`. This is the only sorry in the new modules. It is the ordinary
comparison construction and rank-one calculation, with the source and complete argument
in its docstring. The extracted functor module has zero holes.

This is a decomposition, with one hole closed and one added, net zero. The proved part
is the finite-projective reconstruction from the rank-one case. It is not a claim that the
geometric quotient comparison has been proved without sorry dependencies.

## No longer needed

No existing module or node is globally pruned. The old node's direct proof dependencies
`lem-pur-site-constant-module-hom`, `lem-sfb-adic-constructible-finite-reductions` and
`lem-weil-pbc-site-constant-restriction` are now dependencies of the rank-one node, where
their geometric construction belongs; they remain needed. The item directly uses only
`lem-sfb-adic-perfect-unit-hom` for that geometric input and Mathlib's finite projective
splitting for its own argument. No original public import is removed.

The new functor-only module imports `AdicPerfectReductionModelComplexes`, sufficient for
its definitions, rather than the larger `AdicPerfectReductionModels`. This does not remove
that latter import from the original module or prune it from the targets.

## Where the brief, the DAG or earlier work was wrong

No false original statement or altered unit route was found. Searches in Mathlib and both
source roots found finite-projective splitting, constant internal Hom and scalar-balancing
APIs, but no ready-made ordinary quotient comparison with its successor law. In particular,
the constant internal Hom theorem does not directly supply the quotient-and-completion
comparison. The finite-projective step can be isolated and proved without that geometry;
this delivery does so instead of introducing another finite-projective comparison theorem.
The rank-one source condition is strictly smaller: the new theorem contains no finite-free
or finite-projective bijectivity assertion. Edge cases zero ring, unit ideal, zero modules,
and empty slice agree with the source argument; the finite reconstruction works for rank 0.

## New nodes

`def-sfb-adic-perfect-module-functors` attaches the unchanged ordinary local and quotient
functors and successor balancing isomorphism to their new definition-only module. It
introduces no new mathematical definition and no hole.

`lem-sfb-adic-perfect-unit-hom` records the geometric natural comparison and only its
rank-one computation, leaving all finite-projective reasoning to the proved original node.
Its proof dependencies retain the original geometric dependencies and its source is the
ordinary-module specialization of Stacks Tags 093T and 09C6.

Change record: `coord/changes/V3-adic-perfect-module-functors.md`.

## Second reading by V3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
