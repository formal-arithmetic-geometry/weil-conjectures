# CategoryTheory.TowerLimitTransposeNormalization.tower_limit_transpose_normalization

## Reason

The proof adds private helpers with local section-variable contexts. They prove the generic
localization and conjugation identities needed to establish the original theorem.
All existing public declarations, attributes, universe binders, public imports, and definition
bodies are preserved. All removed imports are private proof imports. No public declaration is
added. This record documents the proof contexts for the delivery interface checker.

## Old

```lean
theorem tower_limit_transpose_normalization
    [IsNoetherianRing A] (_I : Ideal A) :
    ∃ a : (towerLimit (Modules K A)).rightDerivedFunctor ⋙
        d.moduleDirect.rightDerivedFunctor ≅
      (towerDirect d).rightDerivedFunctor ⋙ (towerLimit (Modules J A)).rightDerivedFunctor,
      (∀ H : CochainComplex (ℕᵒᵖ ⥤ Modules K A) ℤ,
        UnboundedExactTower.cochainUnit d.moduleDirect
            (((towerLimit (Modules K A)).mapHomologicalComplex (.up ℤ)).obj H) ≫
          d.moduleDirect.rightDerivedFunctor.map
            (UnboundedExactTower.cochainUnit (towerLimit (Modules K A)) H) ≫
          a.hom.app (DerivedCategory.Q.obj H) =
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
            (preservesLimitNatIso d.moduleDirect (J := ℕᵒᵖ)).hom (.up ℤ)).app H) ≫
          UnboundedExactTower.cochainUnit (towerLimit (Modules J A))
            (((towerDirect d).mapHomologicalComplex (.up ℤ)).obj H) ≫
          (towerLimit (Modules J A)).rightDerivedFunctor.map
            (UnboundedExactTower.cochainUnit (towerDirect d) H)) ∧
      IsIso (limitAdjunction (Modules J A)).unit ∧
      IsIso (limitAdjunction (Modules K A)).unit ∧
      ConstantUnitNormalization (Modules J A) ∧
      ConstantUnitNormalization (Modules K A) ∧
      (∀ (M : DerivedCategory.{w} (Modules J A))
          (V : DerivedCategory.{w} (ℕᵒᵖ ⥤ Modules K A))
          (c : M ⟶ (towerLimit (Modules J A)).rightDerivedFunctor.obj
            ((towerDirect d).rightDerivedFunctor.obj V)),
        (limitAdjunction (Modules K A)).homEquiv
            (d.moduleFunctor.mapDerivedCategory.obj M) V
            ((UnboundedExactTower.constantInterchange d.moduleFunctor).inv.app M ≫
              ((towerAdjunction d).homEquiv
                ((Functor.const ℕᵒᵖ : Modules J A ⥤ _).mapDerivedCategory.obj M) V).symm
                (((limitAdjunction (Modules J A)).homEquiv M
                  ((towerDirect d).rightDerivedFunctor.obj V)).symm c)) =
          ((moduleAdjunction d).homEquiv M
            ((towerLimit (Modules K A)).rightDerivedFunctor.obj V)).symm (c ≫ a.inv.app V)) ∧
      (∀ (M : DerivedCategory.{w} (Modules J A))
          (Z : DerivedCategory.{w} (ℕᵒᵖ ⥤ Modules J A))
          (V : DerivedCategory.{w} (ℕᵒᵖ ⥤ Modules K A))
          (b : (towerInverse d).mapDerivedCategory.obj Z ⟶ V)
          (j : (Functor.const ℕᵒᵖ : Modules J A ⥤ _).mapDerivedCategory.obj M ⟶ Z),
        (moduleAdjunction d).homEquiv M
            ((towerLimit (Modules K A)).rightDerivedFunctor.obj V)
            ((limitAdjunction (Modules K A)).homEquiv
              (d.moduleFunctor.mapDerivedCategory.obj M) V
              ((UnboundedExactTower.constantInterchange d.moduleFunctor).inv.app M ≫
                (towerInverse d).mapDerivedCategory.map j ≫ b)) =
          (limitAdjunction (Modules J A)).unit.app M ≫
            (towerLimit (Modules J A)).rightDerivedFunctor.map j ≫
            (towerLimit (Modules J A)).rightDerivedFunctor.map
              ((towerAdjunction d).homEquiv Z V b) ≫ a.inv.app V)
```

## New

```lean
theorem tower_limit_transpose_normalization
    [IsNoetherianRing A] (_I : Ideal A) :
    ∃ a : (towerLimit (Modules K A)).rightDerivedFunctor ⋙
        d.moduleDirect.rightDerivedFunctor ≅
      (towerDirect d).rightDerivedFunctor ⋙ (towerLimit (Modules J A)).rightDerivedFunctor,
      (∀ H : CochainComplex (ℕᵒᵖ ⥤ Modules K A) ℤ,
        UnboundedExactTower.cochainUnit d.moduleDirect
            (((towerLimit (Modules K A)).mapHomologicalComplex (.up ℤ)).obj H) ≫
          d.moduleDirect.rightDerivedFunctor.map
            (UnboundedExactTower.cochainUnit (towerLimit (Modules K A)) H) ≫
          a.hom.app (DerivedCategory.Q.obj H) =
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
            (preservesLimitNatIso d.moduleDirect (J := ℕᵒᵖ)).hom (.up ℤ)).app H) ≫
          UnboundedExactTower.cochainUnit (towerLimit (Modules J A))
            (((towerDirect d).mapHomologicalComplex (.up ℤ)).obj H) ≫
          (towerLimit (Modules J A)).rightDerivedFunctor.map
            (UnboundedExactTower.cochainUnit (towerDirect d) H)) ∧
      IsIso (limitAdjunction (Modules J A)).unit ∧
      IsIso (limitAdjunction (Modules K A)).unit ∧
      ConstantUnitNormalization (Modules J A) ∧
      ConstantUnitNormalization (Modules K A) ∧
      (∀ (M : DerivedCategory.{w} (Modules J A))
          (V : DerivedCategory.{w} (ℕᵒᵖ ⥤ Modules K A))
          (c : M ⟶ (towerLimit (Modules J A)).rightDerivedFunctor.obj
            ((towerDirect d).rightDerivedFunctor.obj V)),
        (limitAdjunction (Modules K A)).homEquiv
            (d.moduleFunctor.mapDerivedCategory.obj M) V
            ((UnboundedExactTower.constantInterchange d.moduleFunctor).inv.app M ≫
              ((towerAdjunction d).homEquiv
                ((Functor.const ℕᵒᵖ : Modules J A ⥤ _).mapDerivedCategory.obj M) V).symm
                (((limitAdjunction (Modules J A)).homEquiv M
                  ((towerDirect d).rightDerivedFunctor.obj V)).symm c)) =
          ((moduleAdjunction d).homEquiv M
            ((towerLimit (Modules K A)).rightDerivedFunctor.obj V)).symm (c ≫ a.inv.app V)) ∧
      (∀ (M : DerivedCategory.{w} (Modules J A))
          (Z : DerivedCategory.{w} (ℕᵒᵖ ⥤ Modules J A))
          (V : DerivedCategory.{w} (ℕᵒᵖ ⥤ Modules K A))
          (b : (towerInverse d).mapDerivedCategory.obj Z ⟶ V)
          (j : (Functor.const ℕᵒᵖ : Modules J A ⥤ _).mapDerivedCategory.obj M ⟶ Z),
        (moduleAdjunction d).homEquiv M
            ((towerLimit (Modules K A)).rightDerivedFunctor.obj V)
            ((limitAdjunction (Modules K A)).homEquiv
              (d.moduleFunctor.mapDerivedCategory.obj M) V
              ((UnboundedExactTower.constantInterchange d.moduleFunctor).inv.app M ≫
                (towerInverse d).mapDerivedCategory.map j ≫ b)) =
          (limitAdjunction (Modules J A)).unit.app M ≫
            (towerLimit (Modules J A)).rightDerivedFunctor.map j ≫
            (towerLimit (Modules J A)).rightDerivedFunctor.map
              ((towerAdjunction d).homEquiv Z V b) ≫ a.inv.app V)
```

The theorem has a complete proof. The new `Representatives` section contains private generic
unit/counit lemmas and the private composite factorization isomorphism; its variables end with
that section. The additional K-injective-resolution variable in `Limits` applies only to the
private proof of invertibility and ends at `end Limits`. The `GenericNormalization` section proves the comparison and both transpose identities
for an arbitrary exact left adjoint between abelian categories. The coefficient section
specializes that proved result to the supplied module adjunction. All added declarations
are private; these contexts do not affect any existing signature.

## Users

`python3 tools/downstream.py Sheaf.CategoryTheory.TowerLimitTransposeNormalization`
reported zero downstream Lean modules. The assigned module is held by E5. No consumer
adaptation is needed, including DAG parents whose proofs are still unfinished.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.TowerLimitTransposeNormalization | E5 | Proof completed; public interface identical. |

## Status

landed 20261021T172358-L-3360874 2026-10-21 (merge of deliver/E5/Sheaf.CategoryTheory.TowerLimitTransposeNormalization)
