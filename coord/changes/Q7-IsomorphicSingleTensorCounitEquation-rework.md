# AlgebraicGeometry.isomorphic_single_tensor_counit_transport_equation

## Reason

Restore the quarantined module by re-exporting its already proved adopted source
counterpart. The original fails at its redundant local irreducibility assignment
for `derivedPullback`, now globally irreducible upstream. Removing that assignment
alone compiles, but repeating the full proof makes the delivery axiom probe exceed
60 seconds. The shortest route uses the exact existing theorem.

The quarantined and adopted source files have exactly the same two direct imports.
Their public theorem signatures AND proof bodies match verbatim. Re-exporting the
adopted module therefore adds only that proved equation module to the old import
closure and preserves the public declaration with precisely its existing statement
and proof.
The final re-export compiles in 13.8 s. An explicit axiom check reports only
`propext`, `Classical.choice`, and `Quot.sound`. No source-library file is edited.
The DAG attachment moves to that source module;
the mathematical statement, proof plan, proof dependencies, and unit remain intact.

## Old

The quarantined file declares the public equation with private proof helpers,
under this redundant command:

```lean
attribute [local irreducible] derivedPullback Scheme.Modules.tensorPullback
```

Its public signature is:

```lean
theorem isomorphic_single_tensor_counit_transport_equation
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]
    {X P Z : Scheme.{u}} (p : P ⟶ X) (e : Z ≅ P) :
    let c := @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w})))
    let a := fun {A B : Scheme.{u}} (s : A ⟶ B) ↦
      Classical.choose (exists_schemeDerivedAdjunction s
        (hAdd := (Classical.choose exists_derivedPullbackComposition) s)
        ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) s)
        ((Classical.choose (Classical.choose_spec
          (Classical.choose_spec exists_derivedPullbackComposition))) s))
    let t := Classical.choose (exists_isomorphic_single_tensor_counit_transport p e)
    ∀ M : X.Modules,
      let K := (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M
      (a e.hom).unit.app ((derivedPullback p).obj K) ≫
          (schemeDerivedDirectImage e.hom).map
            ((c e.hom p).hom.app K ≫ pinnedSingleTensorCounit (e.hom ≫ p) 0 M) ≫
          t.hom.app M = pinnedSingleTensorCounit p 0 M
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.IsomorphicSingleTensorCounitEquation
```

The imported module publicly declares exactly the signature above and contains
exactly its existing complete proof. The Sheaf compatibility module introduces
no duplicate declarations or local reducibility changes.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.IsomorphicSingleTensorCounitEquation | Q7 | Restored as a re-export of the identical proved API. |
| WeilConjectures.AlgebraicGeometry.IsomorphicSingleTensorCounit | unclaimed | Continues to use the same upstream equation declaration; no edit or adaptation. |

Source searches in both `lean/` and `quarantine/` find no direct importer of the
Sheaf module. The existing upstream consumer already imports the adopted equation
module. No consumer adaptation or target review is required: the declarations,
definitions, selected comparisons, and theorem statement are the same.

## Status

landed 20261020T150703-L-2573627 2026-10-20 (merge of deliver/Q7/Sheaf.AlgebraicGeometry.IsomorphicSingleTensorCounitEquation)
