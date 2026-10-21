# AlgebraicGeometry.ProEtale.condensed_cover_restriction_conservative

## Reason

Restore the assigned module from its archive in `coord/rework.tsv` and prove its theorem.
The live source is absent following the cluster-restore rollback. The archived declaration
and all its hypotheses, universes, visibility and definitions are preserved. The completed
proof uses the already proved adopted-library APIs rather than the more elaborate side-tree
slice comparisons. Unused imports are removed, including four public imports. No source-library
file or declaration is changed.

## Old

The live path is absent. The archived module has this public import interface:

```lean
public import Sheaf.Topology.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction
```

The declaration `AlgebraicGeometry.ProEtale.condensed_cover_restriction_conservative`
has its exact archived signature recorded verbatim in the unchanged `lean.statement` of
`lem-zl-condensed-cover-restriction-conservative`; its whole proof is `by sorry`.

## New

Restore that same declaration with its complete proof and one proved private helper.
The public imports required by its statement are:

```lean
public import Sheaf.Topology.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
```

The proof imports, both private, are:

```lean
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
```

No mathematical interface, coefficient construction, instance or target meaning changes.
The change to public reexports is explicit: unrelated side-tree APIs are no longer exported
through this module. The node attachment and statement dependencies are preserved; its proof
steps and proof dependencies now describe the compiled argument.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.CondensedCoverRestrictionConservative
--uses condensed_cover_restriction_conservative --allow-missing` reports zero live downstream
modules. Searching both `lean/` and `quarantine/` finds the three archived importers below.
They are listed rather than silently treating the absent source as withdrawn. No archived
source is deleted or restored by this delivery except the assigned item. Their use of the
conservativity declaration keeps the identical signature and meaning. No forced adaptation
is made. The local shared claim records contain no row for these archived consumers.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.CondensedLisseProEtaleLocality | no local claim record | Archived importer; it explicitly imports all four removed side modules itself. No adaptation. |
| Sheaf.Paper.MateOpenRestriction | no local claim record | Archived importer using the unchanged isomorphism criterion; its module-object APIs have their own public imports. No adaptation. |
| Sheaf.Paper.IntegralHeartLocalDualityDescent | no local claim record | Archived importer using the unchanged zero-detection clause; its module-object and duality APIs have their own public imports. No adaptation. |

## Status

landed 20261021T022434-L-2846862 2026-10-21 (merge of deliver/E4/Sheaf.AlgebraicGeometry.CondensedCoverRestrictionConservative)
