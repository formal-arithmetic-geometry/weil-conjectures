# AlgebraicGeometry.Etale.restrictedOverSingle_composition

## Reason

The preflight conservatively classifies added attribute commands as interface changes.
This delivery adds only local irreducibility attributes and scoped elaborator settings
to keep inverse-image definitions from expanding during private geometric proofs.
All existing declarations, visibility, imports and signatures remain unchanged.
No downstream adaptation is required: both attribute commands use `local`, and each
elaborator setting uses `in`. They are not exported to importers.

## Old

```lean
theorem restrictedOverSingle_composition {W S : Scheme.{u}} (k : W ⟶ S)
    (F : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1})
    {A B C : Over W} (f : B ⟶ A) (g : C ⟶ B) (a : C ⟶ A)
    (ha : a = g ≫ f) (U : S.Etale)
    (hq : rawAffineRestrictedMap a.left (A.hom ≫ k) (C.hom ≫ k)
        (by rw [← Category.assoc, Over.w]) U =
      rawAffineRestrictedMap g.left (B.hom ≫ k) (C.hom ≫ k)
        (by rw [← Category.assoc, Over.w]) U ≫
      rawAffineRestrictedMap f.left (A.hom ≫ k) (B.hom ≫ k)
        (by rw [← Category.assoc, Over.w]) U) :
    (restrictedOverSingleIso k F a U).hom =
      (NatIso.mapHomologicalComplex
        (upperStarComp AddCommGrpCat.{u + 1}
          (rawAffineRestrictedMap g.left (B.hom ≫ k) (C.hom ≫ k)
            (by rw [← Category.assoc, Over.w]) U)
          (rawAffineRestrictedMap f.left (A.hom ≫ k) (B.hom ≫ k)
            (by rw [← Category.assoc, Over.w]) U)
          (rawAffineRestrictedMap a.left (A.hom ≫ k) (C.hom ≫ k)
            (by rw [← Category.assoc, Over.w]) U) hq)
        (ComplexShape.up ℤ)).hom.app (restrictedOverSingle k F A U) ≫
      ((upperStar AddCommGrpCat.{u + 1}
        (rawAffineRestrictedMap g.left (B.hom ≫ k) (C.hom ≫ k)
          (by rw [← Category.assoc, Over.w]) U)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (restrictedOverSingleIso k F f U).hom ≫
      (restrictedOverSingleIso k F g U).hom
```

No local irreducibility attributes occurred in the original module.

## New

```lean
theorem restrictedOverSingle_composition {W S : Scheme.{u}} (k : W ⟶ S)
    (F : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1})
    {A B C : Over W} (f : B ⟶ A) (g : C ⟶ B) (a : C ⟶ A)
    (ha : a = g ≫ f) (U : S.Etale)
    (hq : rawAffineRestrictedMap a.left (A.hom ≫ k) (C.hom ≫ k)
        (by rw [← Category.assoc, Over.w]) U =
      rawAffineRestrictedMap g.left (B.hom ≫ k) (C.hom ≫ k)
        (by rw [← Category.assoc, Over.w]) U ≫
      rawAffineRestrictedMap f.left (A.hom ≫ k) (B.hom ≫ k)
        (by rw [← Category.assoc, Over.w]) U) :
    (restrictedOverSingleIso k F a U).hom =
      (NatIso.mapHomologicalComplex
        (upperStarComp AddCommGrpCat.{u + 1}
          (rawAffineRestrictedMap g.left (B.hom ≫ k) (C.hom ≫ k)
            (by rw [← Category.assoc, Over.w]) U)
          (rawAffineRestrictedMap f.left (A.hom ≫ k) (B.hom ≫ k)
            (by rw [← Category.assoc, Over.w]) U)
          (rawAffineRestrictedMap a.left (A.hom ≫ k) (C.hom ≫ k)
            (by rw [← Category.assoc, Over.w]) U) hq)
        (ComplexShape.up ℤ)).hom.app (restrictedOverSingle k F A U) ≫
      ((upperStar AddCommGrpCat.{u + 1}
        (rawAffineRestrictedMap g.left (B.hom ≫ k) (C.hom ≫ k)
          (by rw [← Category.assoc, Over.w]) U)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (restrictedOverSingleIso k F f U).hom ≫
      (restrictedOverSingleIso k F g U).hom
```

The signature is identical. The added proof-local commands are:

```lean
attribute [local irreducible] upperStar upperStarComp upperStarId
attribute [local irreducible] rawAffineRestrictedMap restrictedOverSingleIso
```

These commands affect elaboration of this module only; no definition or theorem
statement changes. Six new private helpers are proved and do not appear in any
public signature.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RestrictedOverSingleComposition | X3 | Proof elaboration only; identical public interface |
| All importing modules | unchanged | No exported attribute or signature change; no adaptation |

No declaration has changed interface, so there are no affected downstream users
to adapt or target meanings to reopen. No module outside the claimed item is edited.

## Status

landed 20261013T161323-L-1424713 2026-10-13 (merge of deliver/X3/Sheaf.AlgebraicGeometry.RestrictedOverSingleComposition)
