# rationalLocalizingCategory, rationalLocalizingInclusion, rationalTwistFunctor

## Reason

The projective-line triangle theorem imports TateTwistedProjection, which imported
AffineSpaceRationalLine only for these three definitions. Proving the affine-line
theorem from the projective-line theorem therefore required separating these
definitions from the affine-line theorem. Move them verbatim to
Sheaf.Paper.RationalLocalizingTwist, publicly re-export that module from the old
module, and replace TateTwistedProjection's public import of the old module with
the definition module. All names, universes, binders, bodies and reducibility stay
identical. No target meaning changes and no source-library module changes.

## Old

In Sheaf.Targets.AffineSpaceRationalLine:

```lean
/-- The localizing derived category used in the affine-line statement.
Source: blueprint `sk-def-localizing-closure` (blueprint: det-cor-affine-space-rational-line). -/
abbrev rationalLocalizingCategory
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :=
  (CategoryTheory.localizingClosure (constantModelBoundedConstructible Λ X)).FullSubcategory

/-- The full inclusion of the localizing category into the ambient derived category.
Source: blueprint `sk-def-localizing-closure` (blueprint: det-cor-affine-space-rational-line). -/
noncomputable abbrev rationalLocalizingInclusion
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :=
  (CategoryTheory.localizingClosure (constantModelBoundedConstructible Λ X)).ι

/-- Derived tensor with a specified Tate line, placed in degree zero.
Source: blueprint `sk-def-sp-tate-twist` (blueprint: det-cor-affine-space-rational-line). -/
noncomputable def rationalTwistFunctor
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) ⥤
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X)) :=
  (derivedTensor Λ X).flip.obj ((DerivedCategory.singleFunctor _ 0).obj L)
```

TateTwistedProjection had `public import Sheaf.Targets.AffineSpaceRationalLine`.

## New

The identical definitions, in Sheaf.Paper.RationalLocalizingTwist:

```lean
/-- The localizing derived category used in the affine-line statement.
Source: blueprint `sk-def-localizing-closure` (blueprint: det-cor-affine-space-rational-line). -/
abbrev rationalLocalizingCategory
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :=
  (CategoryTheory.localizingClosure (constantModelBoundedConstructible Λ X)).FullSubcategory

/-- The full inclusion of the localizing category into the ambient derived category.
Source: blueprint `sk-def-localizing-closure` (blueprint: det-cor-affine-space-rational-line). -/
noncomputable abbrev rationalLocalizingInclusion
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :=
  (CategoryTheory.localizingClosure (constantModelBoundedConstructible Λ X)).ι

/-- Derived tensor with a specified Tate line, placed in degree zero.
Source: blueprint `sk-def-sp-tate-twist` (blueprint: det-cor-affine-space-rational-line). -/
noncomputable def rationalTwistFunctor
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) ⥤
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X)) :=
  (derivedTensor Λ X).flip.obj ((DerivedCategory.singleFunctor _ 0).obj L)
```

AffineSpaceRationalLine now has `public import Sheaf.Paper.RationalLocalizingTwist`.
TateTwistedProjection replaces the old public import with the same definition-module
public import. Its other lines are unchanged. Thus all actual users retain the same
constants and elaborated signatures. The definition ownership node is updated.

Consumer checks: every actual user still imports either the affine-line module
(which publicly re-exports the new definition module) or TateTwistedProjection
(which publicly imports it). A source-graph traversal of the complete affine-line
import closure, including delivery overlays, found no cycle or missing module.
The moved definition block was compared byte for byte with the old block; the
TateTwistedProjection file differs only in that import line.

## Users

The union of `tools/downstream.py Sheaf.Targets.AffineSpaceRationalLine --uses`
for each of the three names is the following. Claims were checked against the
shared coordination records; no listed consumer has a current claim there.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AffineSpaceRationalInduction | unclaimed | Same constants and types remain publicly available; no edits needed. |
| Sheaf.Paper.RationalAffineTensorCalculus | unclaimed | Same constants and types remain publicly available; no edits needed. |
| Sheaf.Paper.RationalAffineAdjunctionCalculus | unclaimed | Same constants and types remain publicly available; no edits needed. |
| Sheaf.Paper.RationalP1KernelContractions | unclaimed | Same constants and types remain publicly available; no edits needed. |
| Sheaf.Paper.RationalP1Triangle | unclaimed | Same constants and types remain publicly available; no edits needed. |
| Sheaf.Paper.RationalP1UnitCounit | unclaimed | Same constants and types remain publicly available; no edits needed. |
| Sheaf.Paper.TateTwistedProjection | unclaimed | Public import redirected to the unchanged definitions. |
| Sheaf.Targets.AffineSpaceRationalLine | R3 (item) | Definitions moved and re-exported; theorem proved from P1. |

## Status

landed 20261026T002443-L-88663 2026-10-26 (merge of deliver/R3/Sheaf.Targets.AffineSpaceRationalLine)
