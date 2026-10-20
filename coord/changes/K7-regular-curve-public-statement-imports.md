# AlgebraicGeometry.Scheme.Modules.regular_curve_torsionfree_iff_finiteLocallyFree

## Reason

Restore the quarantined module after the 2026-10-20 upstream sync, preserving the complete
proof recorded at returned head `57b41cc966`. The shared working tree still exposes the
quarantine file; the delivery tool refreshes the delivery base. The repair also simplifies
`finite_stalk` using `Module.Finite.of_isLocalizedModule` instead of an explicit tensor-base-change
equivalence. This private proof change preserves every public signature. The quarantine error was
`Unknown constant AlgebraicGeometry.RingedSpace.IsCoherent`: the definition was only privately
imported. The unchanged public statement needs that definition publicly. Replace the unused
public torsion-subsheaf theorem import by the two public imports supplying its actual statement
requirements: the function field and the scheme stalk-module instance. Prove the theorem fully.

## Old

The quarantine header included:
```lean
public import Sheaf.AlgebraicGeometry.TorsionSubsheafQuotient
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.FunctionField
import Sheaf.AlgebraicGeometry.IsFiniteLocallyFreeOfCoherentFreeStalks
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import WeilConjectures.AlgebraicGeometry.Coherent
import Sheaf.AlgebraicGeometry.CoherentFiniteType
import Sheaf.AlgebraicGeometry.IsRegularScheme
```

## New

```lean
public import Mathlib.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.Coherent
```

Additional imports are private proof imports. The existing theorem signature and all definitions
are unchanged. The stalk-module instance is the same canonical instance previously supplied by
the public torsion-subsheaf import. No source-library file is modified.

## Users

`tools/downstream.py` reports the item as unknown because its source is quarantined. An exhaustive
text search of lean/ and quarantine/ finds one importer, listed below. No active Lean file calls
the declaration. The quarantined consumer already explicitly imports the function-field and
stalk modules, and does not use any declaration re-exported by the removed torsion import.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RegularCurveTorsionfreeFree | K7 | Restored; unchanged statement, complete proof and corrected public imports. |
| Sheaf.AlgebraicGeometry.VectorBundleLineSubbundle | unclaimed | Quarantined; private proof import of the item, unchanged signature and proof. No adaptation required. |

The targets do not use any changed definition: none is changed.

## Status

landed 20261020T145523-L-2406403 2026-10-20 (merge of deliver/K7/Sheaf.AlgebraicGeometry.RegularCurveTorsionfreeFree)
