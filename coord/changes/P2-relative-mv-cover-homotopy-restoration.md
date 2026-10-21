# AlgebraicGeometry.relativeMV_cover_homotopy_data

## Reason

Restore the quarantined module listed in coord/rework.tsv. The archived proof fails
at the default 200000-heartbeat limit in its final backward rewrite chain. A profiler
trace places the failure after the cone isomorphism simplification, while rewriting
through the derived-category and cone maps. Mapping the explicit Mathlib naturality
equation first avoids this search. No definition or public interface changes.

## Old

The public theorem in the quarantined source has this signature:

```lean
theorem relativeMV_cover_homotopy_data
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hpull : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K')
    (U V : X.Opens) (hcover : U ⊔ V = ⊤) :
    let a := relativeMVGlobalArrow f f' g g' hpull K K' φ
    let b := relativeMVLocalArrow f f' g g' hpull K K' φ
    ∃ (C D C' D' : CochainComplex
        (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) ℤ)
      (t : C ⟶ D) (t' : C' ⟶ D') (α : C ⟶ C') (β : D ⟶ D'),
      ∃ (H : Homotopy (t ≫ β) (α ≫ t'))
        (e₁ : DerivedCategory.Q.obj C ≅ a.left)
        (e₂ : DerivedCategory.Q.obj D ≅ (b U).left ⊞ (b V).left)
        (e₃ : DerivedCategory.Q.obj (CochainComplex.mappingCone t) ≅ (b (U ⊓ V)).left)
        (e₁' : DerivedCategory.Q.obj C' ≅ a.right)
        (e₂' : DerivedCategory.Q.obj D' ≅ (b U).right ⊞ (b V).right)
        (e₃' : DerivedCategory.Q.obj (CochainComplex.mappingCone t') ≅ (b (U ⊓ V)).right),
        DerivedCategory.Q.map α ≫ e₁'.hom = e₁.hom ≫ a.hom ∧
        DerivedCategory.Q.map β ≫ e₂'.hom =
          e₂.hom ≫ biprod.map (b U).hom (b V).hom ∧
        DerivedCategory.Q.map (CochainComplex.mappingCone.mapOfHomotopy H) ≫ e₃'.hom =
          e₃.hom ≫ (b (U ⊓ V)).hom
```

## New

The restored theorem has exactly the same signature:

```lean
theorem relativeMV_cover_homotopy_data
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hpull : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K')
    (U V : X.Opens) (hcover : U ⊔ V = ⊤) :
    let a := relativeMVGlobalArrow f f' g g' hpull K K' φ
    let b := relativeMVLocalArrow f f' g g' hpull K K' φ
    ∃ (C D C' D' : CochainComplex
        (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) ℤ)
      (t : C ⟶ D) (t' : C' ⟶ D') (α : C ⟶ C') (β : D ⟶ D'),
      ∃ (H : Homotopy (t ≫ β) (α ≫ t'))
        (e₁ : DerivedCategory.Q.obj C ≅ a.left)
        (e₂ : DerivedCategory.Q.obj D ≅ (b U).left ⊞ (b V).left)
        (e₃ : DerivedCategory.Q.obj (CochainComplex.mappingCone t) ≅ (b (U ⊓ V)).left)
        (e₁' : DerivedCategory.Q.obj C' ≅ a.right)
        (e₂' : DerivedCategory.Q.obj D' ≅ (b U).right ⊞ (b V).right)
        (e₃' : DerivedCategory.Q.obj (CochainComplex.mappingCone t') ≅ (b (U ⊓ V)).right),
        DerivedCategory.Q.map α ≫ e₁'.hom = e₁.hom ≫ a.hom ∧
        DerivedCategory.Q.map β ≫ e₂'.hom =
          e₂.hom ≫ biprod.map (b U).hom (b V).hom ∧
        DerivedCategory.Q.map (CochainComplex.mappingCone.mapOfHomotopy H) ≫ e₃'.hom =
          e₃.hom ≫ (b (U ⊓ V)).hom
```

The proof applies congrArg to mappingCone.map_descShortComplex P P′ m and
simplifies the resulting equality. It retains the same cover-row witnesses,
homotopy, six isomorphisms, dependencies and component equations.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RelativeMVCoverHomotopyData | P2 | Restored from quarantine; final proof calculation repaired, signature unchanged. |
| Sheaf.AlgebraicGeometry.StandardSingleUnionHomotopyChainData | unclaimed, quarantined | Same theorem application; unchanged archived consumer checked separately. |

tools/downstream.py --allow-missing finds zero current library importers. A search
of quarantine finds the consumer above; its DAG proof still uses this item.
No consumer adaptation or target-statement change is required.

## Status

landed 20261021T140850-L-2765260 2026-10-21 (merge of deliver/P2/Sheaf.AlgebraicGeometry.RelativeMVCoverHomotopyData)
