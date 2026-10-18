## What changed

Proved `AlgebraicGeometry.Scheme.Modules.invertible_stalk_linearEquiv` with its exact
original signature. Choose a neighbourhood trivialization using `IsInvertible.exists_isoUnit`,
compose with `restrictFunctorIsoPullback`, and transport the unit generator through the inverse
isomorphism. `isFreeGenerator_restrict_iff` and restriction along `ι_image_top` give a free
generator on the original open. The existing proved private `stalk_generator_bijective`
then makes `LinearMap.toSpanSingleton` bijective; the inverse of `LinearEquiv.ofBijective`
has the required direction.

Use `import all WeilConjectures.AlgebraicGeometry.NonvanishingSectionTrivializes` to access
that existing helper in its current source module. Updated the node's proof and proof-origin
module references after the upstream sync. The mathematical route and all three declared
proof dependencies are unchanged. No definitions, signatures, or public imports changed.

Validation: the final proof compiled through `lcompile.py` in 3.8 seconds with no warnings.
A separate compilation with `#print axioms` reported exactly `propext`, `Classical.choice`,
and `Quot.sound`, with no `sorryAx` or other axioms.
The local construction works on arbitrary schemes and imposes no affine, integral, or
nonempty hypothesis; an input point already supplies the required inhabited neighbourhood.

## Proved and sorry left

Closed the only original hole:
`AlgebraicGeometry.Scheme.Modules.invertible_stalk_linearEquiv`
(node `lem-weil-pbc-invertible-stalk-linear-equiv`).

One of one sorries proved; zero sorries remain; zero holes added; zero split off.

## No longer needed

Removed `import all Sheaf.Paper.NonvanishingSectionTrivializes`: it is now a retired
re-export wrapper, and the private helper belongs to the upstream source module.
Replaced the normal import of
`WeilConjectures.AlgebraicGeometry.NonvanishingSectionTrivializes` with `import all`
of that same module to access its private helper.
Removed the redundant direct import of
`WeilConjectures.AlgebraicGeometry.Modules.Invertible` (already publicly available).
Removed `WeilConjectures.Topology.PresheafModuleStalkFunctor`: the proof needs the existing
Mathlib stalk module structure, not the bundled presheaf module stalk functor.

No DAG proof-dependency nodes are pruned: the final proof follows the existing plan exactly,
including its local-generator argument and reuse of the proved germ helper. No additional
lemmas or modules were introduced, and the unit's route is preserved.

## Where the brief, the DAG or earlier work was wrong

The node's reference to `import all Sheaf.Paper.NonvanishingSectionTrivializes` predates
its retirement at the upstream sync. That module now only re-exports the source module;
its private helper must be accessed using `import all` on the source module itself.
Updated the two stale references. No mathematical statement error was found.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
