## What changed

In `Sheaf.Paper.ProfiniteFreeSliceDerivedHom`, proved
`AlgebraicGeometry.ProEtale.ProfiniteFreeSlice.pointModulePullback_exact`.
The abelian point inverse image preserves finite limits by the existing site
inverse-image instances and finite colimits because its displayed composite
adjunction makes it a left adjoint. The existing `mapMod` preservation instances
lift both properties to internal modules. Finite-product preservation supplies
additivity. No declarations, signatures, definitions, or imports changed.

The delivered module compiled cleanly using `lcompile.py` (29.8 seconds).
This is a partial delivery of the module: the second theorem remains unfinished.

## Proved and sorry left

Closed one of the two original holes:

- `AlgebraicGeometry.ProEtale.ProfiniteFreeSlice.pointModulePullback_exact`.

The one remaining hole is unchanged:

- `AlgebraicGeometry.ProEtale.ProfiniteFreeSlice.exists_comparison`
  (`lem-sfb-profinite-free-slice-derived-hom`).

Added zero holes; split off zero statements. The remaining theorem retains its
original seven-step proof docstring and its DAG attachment.

## No longer needed

None. No imports, nodes, or modules were removed. The unfinished comparison still
needs the recorded dependency route; this partial exactness proof does not justify
pruning any of those dependencies.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed or disputed. The exactness hole is a direct
application of existing preservation instances, as the stage-2 review observed.

For continuing the remaining theorem, the cited localization APIs do not directly
supply the arbitrary internal-module restriction comparison needed in steps 3--4.
`proEtaleObjectInverseImageRestriction` supplies set/abelian/ring restriction data
and module restriction for constant coefficients; `sfbCoefficientSectionsLocalization`
supplies abelian restriction and the coefficient/regular-module comparisons.
A normalized comparison for arbitrary internal modules still has to be constructed
from those data. The general K-injective restriction theorem applies to
`SheafOfModules.overFunctor`, so it additionally needs transport to the particular
`CondensedRing.upperStar` used here. Steps 3--5 then need the free-generator Hom
calculation, its chain isomorphism, and the fixed localization equation.

I also explored adjunction/Yoneda constructions of the set and free-module
identifications. The set identification and its generator normalization compiled;
the free-module generator proof still required elaboration work. These unused
private experiments were removed from the delivery. No unproved intermediate
result or claimed reduction of `exists_comparison` is included.

## Second reading by Q5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
