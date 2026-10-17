# AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleHom

## Reason

The full delivered module exceeded the unchanged 60-second server compile limit.
A diagnostic prefix through the shriek constructions compiled in 36.9 seconds;
its profiler reported 15.5 seconds in typeclass inference. Terms in the profile
expanded the coefficient inverse image into its underlying sheaf-site construction.
The later internal Hom definitions also use the concrete module and derived
closed structures. Preventing unnecessary local unfolding of these implementations
makes the complete module compile in 53.2 seconds. This repairs elaboration of the
existing definitions without changing their bodies or signatures.

## Old

```lean
@[expose] public section

universe u
```

The imported implementations had their usual transparency. The earlier returned
sandbox marked only `DerivedCategory.monoidalClosed` locally irreducible, starting
at the tensor section; that version still exceeded the current server limit.

## New

```lean
@[expose] public section

-- Keep elaboration from expanding the K-injective construction of internal Hom.
attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint

universe u
```

These attributes are local to elaboration in this file. Every public signature,
definition body, imported declaration and exported attribute remains unchanged.
No axiom, hole, compiler-limit change or consumer adaptation is introduced.
The separate comment-position repair leaves both holed instances' signatures and
complete scanned bodies identical to the shared source.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible | A4 | Avoid unnecessary unfolding of imported internal Hom and coefficient implementations during local elaboration. |

There are no external users of these local attributes. Importers retain the same
public signatures, definition bodies and attributes. No module held by another
group is adapted.

## Status

landed 20261017T021558-L-693260 2026-10-17 (merge of deliver/A4/WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible)
