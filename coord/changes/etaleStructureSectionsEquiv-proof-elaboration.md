# AlgebraicGeometry.etaleStructureSectionsEquiv_naturality

## Reason

The stage-3 preflight conservatively classifies changes to module-level commands as
interface changes, including the additional universe names and local irreducibility
attributes used by this proof. This record makes their scope explicit for the reader.
No public declaration's signature, visibility, or definition body changes. No import
changes. No target meaning changes, and no downstream adaptation is necessary.

The local attributes prevent expensive unfolding of tensor/sheaf implementations
while proving module-morphism identities. The final lifted-sheaf proof uses scoped
transparency settings and an equality of additive morphisms rather than repeatedly
normalizing concrete section functions.

## Old

The original elaboration commands preceding the public definitions were:

```lean
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

There were no local irreducibility attributes and no scoped transparency options
on `etaleStructureSectionsEquiv_naturality`; its proof was `by sorry`.

## New

The original commands remain, except the universe declaration is now:

```lean
universe u v w
```

The additional universes occur only in the generic private lifted-sheaf helper.
The following attributes are local to the namespace and are not imported:

```lean
attribute [local irreducible] Scheme.Modules.tensorPullback
  Scheme.Modules.tensorPullbackObj Scheme.Modules.tensorPullbackObjUnitToUnit

attribute [local irreducible] tensorStructureSectionsEquiv etaleStructureSectionsEquiv
```

The final theorem has the following scoped elaboration options:

```lean
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
```

Its original signature and docstring remain verbatim. Its proof now combines the
proved private composition, section, restriction, and ULift calculations. There are
no new public declarations, no changed definitions, and no replacement holes.

## Users

`tools/downstream.py` finds 125 transitive downstream modules; the sole direct
importer and sole external textual user of `etaleStructureSectionsEquiv` is below.
Since the commands are local/scoped and all public declarations are unchanged,
none of the transitive importers require adaptation or a new statement review.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EtaleStructureSectionsEquiv | B3 | Proof elaboration only; sole original hole closed. |
| Sheaf.AlgebraicGeometry.ArtinSchreierDataConstruction | unclaimed | No semantic/interface change; existing canonical equivalences and naturality statement retained. |

## Status

landed 20261012T194100-L-451574 2026-10-12 (merge of deliver/B3/Sheaf.AlgebraicGeometry.EtaleStructureSectionsEquiv)
