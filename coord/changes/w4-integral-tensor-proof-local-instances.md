# AlgebraicGeometry.Etale.integral_derivedTensor_boundedBelow_torsion

## Reason

The replacement proof needs local instance selection for coefficient rings, monoidal
additivity, and small colimits. Preflight conservatively classifies its new attribute,
open, section-variable and instance commands as an interface change and requires this
record. The public statement, public imports, and definitions are unchanged. All new
helpers are private, all seven helper instances are explicitly local, and every instance
priority attribute is local. There is no downstream instance registration.

The high-priority local CommRing.toRing instance makes the direct ModuleCat coefficient
ring agree with the ring inherited by DerivedCategoryModule. Without this alignment,
the kernel spends its heartbeat budget comparing large definitionally equal derived
category expressions. No heartbeat budget is raised. Local tensor-additivity and
colimit instances similarly avoid unnecessary instance search.

## Old

The archived public signature, verbatim (its proof was sorry):

```lean
theorem integral_derivedTensor_boundedBelow_torsion
    (T : Scheme.{u})
    (A B : DerivedCategoryModule (ULift.{u + 1} ℤ) T)
    (a b : ℤ)
    (hA : ∀ i : ℤ, i < a →
      IsZero ((DerivedCategory.homologyFunctor
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) i).obj A))
    (hB : ∀ j : ℤ, j < b →
      IsZero ((DerivedCategory.homologyFunctor
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) j).obj B)) :
    (∀ r : ℤ, r < a + b - 1 →
      IsZero ((DerivedCategory.homologyFunctor
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) r).obj
        (((derivedTensor (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) T).obj A).obj B))) ∧
      ((∀ i : ℤ, CategoryTheory.Sheaf.IsTorsion
        ((sheafCompose T.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})).obj
          ((DerivedCategory.homologyFunctor
            (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) i).obj A))) →
        ∀ r : ℤ, CategoryTheory.Sheaf.IsTorsion
          ((sheafCompose T.smallEtaleTopology
            (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})).obj
            ((DerivedCategory.homologyFunctor
              (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) r).obj
              (((derivedTensor (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) T).obj A).obj B))))
```

There were no helper instances or local instance-priority attributes in this module.

## New

The public signature remains verbatim:

```lean
theorem integral_derivedTensor_boundedBelow_torsion
    (T : Scheme.{u})
    (A B : DerivedCategoryModule (ULift.{u + 1} ℤ) T)
    (a b : ℤ)
    (hA : ∀ i : ℤ, i < a →
      IsZero ((DerivedCategory.homologyFunctor
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) i).obj A))
    (hB : ∀ j : ℤ, j < b →
      IsZero ((DerivedCategory.homologyFunctor
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) j).obj B)) :
    (∀ r : ℤ, r < a + b - 1 →
      IsZero ((DerivedCategory.homologyFunctor
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) r).obj
        (((derivedTensor (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) T).obj A).obj B))) ∧
      ((∀ i : ℤ, CategoryTheory.Sheaf.IsTorsion
        ((sheafCompose T.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})).obj
          ((DerivedCategory.homologyFunctor
            (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) i).obj A))) →
        ∀ r : ℤ, CategoryTheory.Sheaf.IsTorsion
          ((sheafCompose T.smallEtaleTopology
            (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})).obj
            ((DerivedCategory.homologyFunctor
              (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) r).obj
              (((derivedTensor (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) T).obj A).obj B))))
```

Its proof is now complete. Private proved helpers and private local instances supply the
argument. The following attributes affect only this module's elaboration:

```lean
attribute [local instance 50000] CommRing.toRing
attribute [local instance 40000] Preadditive.preadditiveHasZeroMorphisms
attribute [local instance 30000] Abelian.toPreadditive
attribute [local instance 20000] SymmetricCategory.toBraidedCategory
attribute [local instance 21000] sheafBraidedCategory
```

The proved private etaleSheaf_monoidalPreadditive helper is also installed with
`attribute [local instance 50000] etaleSheaf_monoidalPreadditive`. All helper instance
commands have the form `private local instance`. The added `open MonoidalCategory`,
`set_option autoImplicit false`, and the private generic helper section are used to write
the proof and do not change a public declaration's type or definition.

## Users

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.IntegralDerivedTensorBoundedTorsion
--allow-missing --uses integral_derivedTensor_boundedBelow_torsion` reports zero current
Lean importers and zero current textual users. The module is quarantined in the baseline;
this delivery restores it, preserving its DAG attachment and its parents' need for it.
No consumer adaptation is required because the public interface is preserved.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.IntegralDerivedTensorBoundedTorsion | W4 | Restored; proof completed; helper instances and priorities local. |

No other module is changed. No source-library declaration or definition is changed.

## Status

landed 20261021T134607-L-1383565 2026-10-21 (merge of deliver/W4/Sheaf.AlgebraicGeometry.IntegralDerivedTensorBoundedTorsion)
