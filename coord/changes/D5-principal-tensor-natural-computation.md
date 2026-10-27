# CategoryTheory.Mod.KFlatScalarTower.natural_computation

## Reason

The assigned theorem needs a natural scalar comparison, whereas the existing public
`realization` theorem gives isomorphisms for an individual representative. Its proof
already constructs the canonical comparison using private helpers. Expose that
comparison in a proved theorem, retaining every existing signature and definition.
The module is unclaimed at the time of this delivery.

## Old

There is no declaration `CategoryTheory.Mod.KFlatScalarTower.natural_computation`.
Every existing signature and definition remains unchanged. The existing realization
proof is refactored to reuse natural_computation, eliminating duplicated calculations.

## New

In the existing namespace and section context, add:

```lean
theorem natural_computation
    (eB : ∀ n, B n ≅ (Mod.comap (q n)).obj (Mod.regular (S n)))
    (hι : ∀ n, (ι n).hom ≫ (eB n).hom.hom = q n)
    (hτ : ∀ n, (τ n).hom ≫ (eB n).hom.hom = (eB (n + 1)).hom.hom ≫ r n) :
    ∃ c : ∀ n, DerivedCategory.Q ⋙ reduction R S q n ⋙ restriction R S q n ⟶
        tensorLevel R B n ⋙ DerivedCategory.Q,
      (∀ n P, (HomologicalComplex.quasiIso (Mod C R) (.up ℤ)).kFlat P →
        IsIso ((c n).app P)) ∧
      (∀ n P, step R S q r h (DerivedCategory.Q.obj P) n ≫ (c n).app P =
        (c (n + 1)).app P ≫ DerivedCategory.Q.map (tensorStep R B τ P n)) ∧
      (∀ n P, (Mod.derivedExtendMapDerivedCategoryAdjunction (q n)).unit.app
          (DerivedCategory.Q.obj P) ≫ (c n).app P =
        DerivedCategory.Q.map (tensorUnit R B ι P n))
```

Attach it to `lem-pe-internal-kflat-scalar-tower-realization`.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.InternalKFlatScalarTowerRealization | unclaimed | Two proved theorems added; realization proof reuses natural_computation. |
| Sheaf.SixFunctors.ProEtale.DerivedCompletion | unclaimed | Sole existing direct importer; no changes required. |
| Sheaf.Paper.PrincipalTensorScalarExtension | D5 | Imports and applies the new theorem. |

All transitive importers retain exactly the same existing declarations and instances.
There is no statement or definition change and no target interpretation change.

The generic `derived_realization` theorem then combines this computation with the
lax tensor comparison and fully faithful precomposition through K-flat localization.
Its full signature follows (in the same section context):

```lean
theorem derived_realization
    (eB : ∀ n, B n ≅ (Mod.comap (q n)).obj (Mod.regular (S n)))
    (hι : ∀ n, (ι n).hom ≫ (eB n).hom.hom = q n)
    (hτ : ∀ n, (τ n).hom ≫ (eB n).hom.hom = (eB (n + 1)).hom.hom ≫ r n) :
    ∃ e : ∀ n, tensorRight ((DerivedCategory.singleFunctor (Mod C R) 0).obj (B n)) ≅
        reduction R S q n ⋙ restriction R S q n,
      (∀ n K, (K ◁ (DerivedCategory.singleFunctor (Mod C R) 0).map (τ n)) ≫
        (e n).hom.app K = (e (n + 1)).hom.app K ≫ step R S q r h K n) ∧
      (∀ n K, ((ρ_ K).inv ≫ K ◁
          (Functor.LaxMonoidal.ε DerivedCategory.Q ≫ DerivedCategory.Q.map
            ((HomologicalComplex.single (Mod C R) (.up ℤ) 0).map (ι n)))) ≫
        (e n).hom.app K =
          (Mod.derivedExtendMapDerivedCategoryAdjunction (q n)).unit.app K)
```

## Status

landed 20261025T162152-L-338856 2026-10-25 (merge of deliver/D5/Sheaf.Paper.PrincipalTensorScalarExtension)
