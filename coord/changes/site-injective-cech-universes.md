# CategoryTheory.site_injective_cech_acyclic

## Reason

Correct the independent-universe defect documented by E2. Exact sheafification and the cofree construction need coefficients large enough for the objects and homs. Stacks 03AW has this ordinary sized interpretation. No target or definition changes.

## Old

```lean
theorem site_injective_cech_acyclic
    {C : Type u} [Category.{v} C]
    {J : Precoverage C} [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    {T : Type w} {U : C} (f : T → C) (hom : ∀ t, f t ⟶ U)
    (hcover : Presieve.ofArrows f hom ∈ J U)
    (S : SiteCechComplex f hom)
    (I : Sheaf J.toGrothendieck AddCommGrpCat.{w}) [Injective I] :
    (∀ p : ℕ, 0 < p → IsZero ((S.cohomologyFunctor p).obj I.obj)) ∧
      Nonempty (((S.cohomologyFunctor 0).obj I.obj) ≅
        I.obj.obj (op U))
```

## New

```lean
theorem site_injective_cech_acyclic
    {C : Type u} [Category.{v} C]
    {J : Precoverage C} [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    {T : Type (max u v)} {U : C} (f : T → C) (hom : ∀ t, f t ⟶ U)
    (hcover : Presieve.ofArrows f hom ∈ J U)
    (S : SiteCechComplex f hom)
    (I : Sheaf J.toGrothendieck AddCommGrpCat.{max u v}) [Injective I] :
    (∀ p : ℕ, 0 < p → IsZero ((S.cohomologyFunctor p).obj I.obj)) ∧
      Nonempty (((S.cohomologyFunctor 0).obj I.obj) ≅
        I.obj.obj (op U))
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.InjectiveSheafCechAcyclic | unclaimed | Existing statement and proof unchanged; max specializes to u+1. |
| Sheaf.CategoryTheory.SiteCechVanishingStep | unclaimed | Small category: max specializes to u. |
| Sheaf.Topology.FilteredInjectiveCechAcyclic | unclaimed | Opens X: max u 0 specializes to u. |
| Sheaf.Topology.DirectedInjectiveDerivedSectionsAcyclic | unclaimed | Existing signature and proof unchanged; Opens X has hom universe 0, so max u 0 specializes to u. |

The downstream scan found 762 transitive importers and exactly these four external direct declaration users. All four originals are compiled against the modified dependency; no adapted module is delivered. Since no definition changes, the meanings and elaborated signatures of the targets are unchanged. Node citers are listed individually in statement_change.

## Status

landed 20261012T150959-L-2233024 2026-10-12 (merge of deliver/X3/Sheaf.CategoryTheory.SiteInjectiveCechAcyclic)
