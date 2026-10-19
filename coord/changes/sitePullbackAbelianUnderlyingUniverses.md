# CategoryTheory.sitePullback_abelian_underlying_of_hasSheafify

## Reason

The pro-étale site has object universe u+1 and morphism universe u, while its
set-valued sheaves have coefficients Type (u+1). The existing comparison only
accepts SmallCategory C with equal object and morphism universes. Generalize its
existing proof with explicit weak sheafification and left Kan extension hypotheses.
Keep the original declaration as an exact-signature specialization, so existing
consumers need no adaptations. The dependency module is unclaimed.

## Old

```lean
theorem sitePullback_abelian_underlying
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (U : C ⥤ D)
    [U.IsContinuous J K]
    [PreservesFiniteLimits (sheafPullback U (Type u) J K)] :
    Nonempty (sheafPullback U AddCommGrpCat.{u} J K ⋙
        sheafCompose K (forget AddCommGrpCat.{u}) ≅
      sheafCompose J (forget AddCommGrpCat.{u}) ⋙ sheafPullback U (Type u) J K)
```

## New

The old declaration above is retained verbatim. Add the proved general theorem:

```lean
theorem sitePullback_abelian_underlying_of_hasSheafify
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (U : C ⥤ D)
    [U.IsContinuous J K]
    [HasWeakSheafify K (Type (max u v w))]
    [HasWeakSheafify K AddCommGrpCat.{max u v w}]
    [∀ F : Cᵒᵖ ⥤ Type (max u v w), U.op.HasLeftKanExtension F]
    [∀ F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}, U.op.HasLeftKanExtension F]
    [PreservesFiniteLimits (sheafPullback U (Type (max u v w)) J K)] :
    Nonempty (sheafPullback U AddCommGrpCat.{max u v w} J K ⋙
        sheafCompose K (forget AddCommGrpCat.{max u v w}) ≅
      sheafCompose J (forget AddCommGrpCat.{max u v w}) ⋙
        sheafPullback U (Type (max u v w)) J K)
```

## Users

`tools/downstream.py Sheaf.CategoryTheory.SitePullbackAbelianUnderlying --uses
sitePullback_abelian_underlying` identifies the two external callers below, plus
the defining module. `--direct` also identifies this delivery's item.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.SitePullbackAbelianUnderlying | unclaimed | Generalize the existing proof; retain the original signature as a wrapper. |
| Sheaf.CategoryTheory.SitePullbackAbelianExact | unclaimed | No edits; unchanged consumer compiles against the generalized module. |
| Sheaf.CategoryTheory.SiteLerayDegenerate | unclaimed | No edits; unchanged consumer compiles against the generalized module. |
| Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage | W7 | Use the general comparison at universes u+1,u,0. |

All existing declarations, definitions and public imports retain their signatures
and visibility. No target statement or definition used by a target changes. The
new theorem proves the same underlying-sheaf comparison with explicit existence
instances; it makes no arbitrary data choice from an unproved existence theorem.

## Status

landed 20261019T034342-L-424276 2026-10-19 (merge of deliver/W7/Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage)
