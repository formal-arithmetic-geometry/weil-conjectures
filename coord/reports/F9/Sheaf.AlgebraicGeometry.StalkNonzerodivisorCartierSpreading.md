## What changed

Proved both declarations of `Sheaf.AlgebraicGeometry.StalkNonzerodivisorCartierSpreading`
without changing their statements. A proved private helper clears finite generators of the
ideal and the kernel of its localization map. Injectivity of multiplication by the given
stalk generator replaces the unnecessary domain hypothesis of the related existing
`Ideal.exists_notMem_isRegularPrincipal_map_away` theorem. The existing proved
`Ideal.isRegularPrincipal_map_away` completes localization to a principal neighbourhood.
The scheme proof applies the helper directly to the affine germ localization and uses
`IdealSheafData.map_ideal` on the resulting affine basic open. The node now records this
argument. No source-library module was changed, and no definition or statement was changed.

## Proved and sorry left

Closed both original holes:
- `Ideal.exists_away_generator_of_stalk_nonzerodivisor`.
- `AlgebraicGeometry.isInvertible_ker_of_stalk_nonzerodivisor`.

Both realize `lem-sfb-stalk-nonzerodivisor-cartier-spreading`.
There are zero remaining holes and zero added holes; no results were split off.
The private helper `Ideal.exists_clearing_of_regular_generator` is proved in full.
The complete module compiled cleanly with `lcompile.py` in 3.9 seconds. A prior elaboration
timeout at the final application was resolved by explicitly supplying the source and
destination rings; no time or heartbeat limit was changed.

## No longer needed

Removed imports:
- `WeilConjectures.Topology.PresheafModuleStalkFunctor`.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.AffineModuleGermLocalization`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`.

The proof does not use dependency nodes `lem-sbc-affine-module-germ-localization` or
`lem-weil-pbc-affine-module-basic-open-localization`. The hypothesis already presents the
stalk ideal as a map of the affine ideal, and `IdealSheafData.map_ideal` already computes
its restriction to every affine basic open. The node removes those two proof dependencies.
No module is withdrawn; other consumers may still require these dependencies.

## Where the brief, the DAG or earlier work was wrong

The original proof plan unnecessarily reconstructs the ideal-module stalk and its basic-open
sections. The actual hypothesis and ideal-sheaf API already supply these identifications.
The related source-library spreading lemma assumes a domain, so it cannot directly prove this
item: injectivity of multiplication is essential in its place. No disputed statement was
used, no target changed, and the unit route remains intact. The finite-kernel argument is
Stacks Tags 0AG8 and 061L. It handles non-domain ambient rings, unit generators, empty
finite generating sets, empty closed subschemes, and an empty ambient scheme.

## Second reading by F9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
