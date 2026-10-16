# AlgebraicGeometry.Etale.relativeSectionCocone_isColimit proof scopes

## Reason

The completed proof adds private helpers for finite matching, inverse-image coherence, affine
base change, and directed reindexing. These require extra universe names and namespace scopes.
The preflight scope-command check requires this record. The sole existing theorem keeps exactly
its old signature and visibility; its public import is unchanged. Every added support declaration
is private, and the finite-hypercover instance is local. No existing definition, statement, or
meaning of a target changes. No consumer requires adaptation.

## Old

The original module-level scopes are:

```lean
universe u' u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Etale
variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]
```

The original theorem signature is:

```lean
theorem relativeSectionCocone_isColimit
    {I : Type u} [SmallCategory I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j} (g : i ⟶ j), IsAffineHom (D.map g)]
    (c : Cone D) [CompactSpace c.pt] [QuasiSeparatedSpace c.pt]
    (hc : IsLimit c) (i : I) (G : Sheaf (D.obj i).smallEtaleTopology A)
    (U : (D.obj i).Etale) [CompactSpace U.left] [QuasiSeparatedSpace U.left] :
    Nonempty (IsColimit (((evaluation _ A).obj (op U)).mapCocone
      (relativeSectionCocone A D c i G)))
```

## New

The helper universe and namespace scopes are internal to this module:

```lean
universe u' u v w t
open CategoryTheory Limits Opposite
```

The file opens and closes `AlgebraicGeometry` and `AlgebraicGeometry.Etale` around private helpers,
then reopens `AlgebraicGeometry.Etale` with the original coefficient variables for the theorem.
The backward-transparency options are scoped to individual helper declarations with `in`.
The private `affineOpenOneHypercoverFinite` is registered with `attribute [local instance]`,
used only in the private finite-cover proof.
The public theorem signature remains verbatim:

```lean
theorem relativeSectionCocone_isColimit
    {I : Type u} [SmallCategory I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j} (g : i ⟶ j), IsAffineHom (D.map g)]
    (c : Cone D) [CompactSpace c.pt] [QuasiSeparatedSpace c.pt]
    (hc : IsLimit c) (i : I) (G : Sheaf (D.obj i).smallEtaleTopology A)
    (U : (D.obj i).Etale) [CompactSpace U.left] [QuasiSeparatedSpace U.left] :
    Nonempty (IsColimit (((evaluation _ A).obj (op U)).mapCocone
      (relativeSectionCocone A D c i G)))
```

## Users

`tools/downstream.py --uses relativeSectionCocone_isColimit` lists exactly the two textual users
below. The sole direct importer is the second row; its original source compiles unchanged against
the sandbox. No existing module besides the item is edited. Additional scopes and private helpers
are not part of an importer's interface, so all transitive consumers retain the same theorem and
public imports. No target statement review is reopened.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.GrothendieckEtaleRelativeSectionColimit | C3 | proof replaced; signature unchanged |
| Sheaf.AlgebraicGeometry.GrothendieckEtaleSectionColimit | unclaimed | original source compiles unchanged |

## Status

landed 20261016T081350-L-1435770 2026-10-16 (merge of deliver/C3/Sheaf.AlgebraicGeometry.GrothendieckEtaleRelativeSectionColimit)
