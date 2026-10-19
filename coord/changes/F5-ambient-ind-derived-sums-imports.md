# AmbientIndDerivedSums imports and private proof helpers

## Reason

The complete proof uses existing coproduct-preservation and truncation APIs. Remove unused
public wrappers, retaining the imports needed by the original statements. This is import
pruning; both public theorem signatures and every definition used by the targets are unchanged.
Add only private proved helpers. The added universe names and ZeroObject scope support them.

## Old

```lean
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.LocalizingClosureExistence
public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.AlgebraicGeometry.ProEtaleBoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
```

Both public theorem signatures are unchanged, verbatim apart from whitespace.

## New

```lean
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.LocalizingClosure
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
```

The proof-only imports are AmbientIndDerivedTriangulated, IndConstructibleFilteredColimits,
WeilConjectures.CategoryTheory.DerivedCategory.HomologyCoproducts, and
WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty.
Private helpers prove zero membership from the empty sum, cohomology sum preservation,
cohomology sum closure, small nonzero support, transport to a cofan, and the localizing predicate.
No public declaration is added or removed and no target meaning changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ProperIndConstructibleUnbounded | K6 | Only direct importer. Its public statements use coefficient rings, derived cohomology, truncations and constructibility, all retained. Its own imports provide tensor and Grothendieck APIs. No signature or proof adaptation needed. |
| Sheaf.Paper.ProperUnboundedWindow | unclaimed | Transitive importer. Uses its own ProperHeartBound, coefficient-ring and derived-functor interfaces. No adaptation needed. |
| Sheaf.Paper.ProperUnboundedCoproducts | U2 | Transitive importer. Explicitly imports ProfiniteCondensedRing and right-derived-functor interfaces. No adaptation needed. |

The downstream search found exactly these three consumers. No consumer mentions either public
theorem name yet; their proofs are still pending. No change to a definition or target statement
requires a renewed semantic target review. All three unchanged consumer sources compiled cleanly against the changed module in a
sequential lcompile.py --all overlay check. The global build verifies import pruning
independently.

## Status

landed 20261019T002545-L-2152705 2026-10-19 (merge of deliver/F5/Sheaf.Paper.AmbientIndDerivedSums)
