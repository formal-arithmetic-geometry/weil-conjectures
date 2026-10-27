# CategoryTheory.SheafFreeModule.normalizedFreeComparison

## Reason

The returned packet changed local instance declaration bodies, and preflight
required this change record and the complete consumer table below. The repaired
packet preserves all nine local instance bodies verbatim from the current source.
They are local aliases of available HasSheafCompose proofs, used only to avoid
repeated expensive inference.
No existing statement, definition body, public import, or global instance changes.
The instance-search attribute adjustments are scoped to single commands with `in`.
Private theorem/abbreviation alternatives were tested but exceeded the compiler's
60-second limit; the local-instance version compiles within the required limit.

## Old

The current source already caches HasSheafCompose witnesses for J, K and T,
with the bodies `:= inferInstance`. These declarations are retained verbatim.
The existing definition is unchanged, verbatim:

```lean
def normalizedFreeComparison
    (L : Sheaf J (Type w) ⥤ Sheaf K (Type w))
    {B : Sheaf J CommRingCat.{w}} {BI : Sheaf K CommRingCat.{w}}
    (F : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w} L B BI)
    (E : Sheaf J (Type w))
    (p : F.modules.obj ((free B).obj E) ≅ (free BI).obj (L.obj E)) :
    L.obj ((moduleSets B).obj ((free B).obj E)) ⟶
      (moduleSets BI).obj ((free BI).obj (L.obj E)) :=
  F.moduleUnderlying.inv.app ((free B).obj E) ≫ (moduleSets BI).map p.hom
```

## New

The definition quoted above is unchanged. The following existing local instance
declarations are retained for each of J, K and T (with the corresponding site
category and EssentiallySmall instance); none is added or changed by this repair.

```lean
local instance : J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w}) := inferInstance
local instance : J.HasSheafCompose (forget CommRingCat.{w} ⋙ uliftFunctor.{w, w}) := inferInstance
local instance : J.HasSheafCompose (forget AddCommGrpCat.{w} ⋙ uliftFunctor.{w, w}) := inferInstance
```

The proof also opens `CategoryTheory.MonoidalCategory` and sets
`backward.isDefEq.respectTransparency.types` to `false` within this file. These
control notation and elaboration only and do not alter exported signatures.
Command-scoped removal of `hasSheafCompose_of_preservesMulticospan` from instance
search is restored immediately after each affected declaration. The current public
construction import is preserved, so none of these settings affects importers.

## Users

The current source has nine transitive downstream modules. The earlier zero-user
claim checked only mentions of `normalizedFreeComparison`; it did not cover the
instance signatures identified by the landing tools. All five modules named in
the return are explicitly recorded below, along with the other four downstream
modules. Their existing signatures and meanings are unchanged: local instances
and command-scoped attributes do not become instance-search attributes in an
importer, and no public definition body or public import is changed relative to
the current source. No consumer adaptation is needed, and no target meaning changes.

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.Sites.NormalizedFreeModuleComparison | X3 | Existing local caches preserved; six theorem proofs completed. |
| Sheaf.Algebra.Homology.RingedSiteKFlatStalkCriterion | unclaimed | RingCat sheaf-composition use unchanged; no adaptation. |
| Sheaf.Algebra.Homology.RingedSitePointFinitePresentationRetract | unclaimed | RingCat sheaf-composition use unchanged; no adaptation. |
| Sheaf.Algebra.Homology.RingedSitePointUniversalTensor | unclaimed | RingCat sheaf-composition use unchanged; no adaptation. |
| Sheaf.CategoryTheory.Sites.InverseImageDifferentials | unclaimed | RingCat and lifted set sheaf composition unchanged; no adaptation. |
| Sheaf.CategoryTheory.Sites.InverseImageFreeModule | unclaimed | Uses the six completed theorems with identical signatures; its own local caches unchanged. |
| Sheaf.AlgebraicGeometry.AlgebraicSpaceSingleComplexTensorInheritance | unclaimed | Transitive proof dependency only; no adaptation. |
| Sheaf.Topology.SheafCotangentComparison | unclaimed | Transitive proof dependency only; no adaptation. |
| Sheaf.Topology.SquareZeroSheafAlgebra | unclaimed | Transitive proof dependency only; no adaptation. |
| Sheaf.Topology.ZariskiSheafAlgebraExtensionExt | unclaimed | Transitive proof dependency only; no adaptation. |

## Status

landed 20261024T022013-L-2890635 2026-10-24 (merge of deliver/X3/Sheaf.CategoryTheory.Sites.NormalizedFreeModuleComparison)
