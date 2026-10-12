# H.openRestrictionExt_bijective: private proof scope

## Reason

The stage-3 interface checker conservatively reports added commands such as variable,
section, universe, omit and attribute as an interface change. This delivery adds a
separate scoped section for private categorical proof helpers and a local instance for
the proved open-immersion property of the constructed inclusion. Existing declaration
signatures, visibility, public imports and global instances are unchanged. This record
makes the conservative flag explicit for the independent reader; no adaptation is needed.

## Old

```lean
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] {X : Scheme.{u}}
```

## New

The old commands remain. Before the existing namespace, the delivery adds:

```lean
section DimensionShift
universe w w' v v' u₁ u₂
variable {C : Type u₁} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {D : Type u₂} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]
```

This section contains only proved private theorems and ends before the existing
namespace. An `omit` command avoids unused section instances on a private Hom-transport
lemma. Inside the existing namespace, the private theorem proving that the base-changed
inclusion is open is registered with:

```lean
attribute [local instance] openBaseChangeInclusion_isOpenImmersion
```

No public declaration mentions these private names in its signature. The target
statement and all its definitions are unchanged; no target statement review reopens.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Cohomology.MayerVietorisOpenExtTransport | unclaimed | Its imported public signatures and definitions remain identical; no adaptation. |

The conservative checker flag names commands, rather than a changed public declaration;
no downstream module uses the added private names or local instance as a public API.
No adapted module is included in this delivery.

## Status

landed 20261012T220523-L-1394352 2026-10-12 (merge of deliver/K1/Sheaf.AlgebraicGeometry.Cohomology.MayerVietorisOpenRestrictionBijective)
