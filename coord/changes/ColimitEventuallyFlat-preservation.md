# RingTheory.exists_flat_stage

## Reason

The source uses algebraic directed ring colimits. Categorical colimits in an independently smaller ring universe do not guarantee underlying representatives or eventual equality. Propagate the explicit preservation condition, restore/retain the complete original proof, and adapt all actual callers. The module is unclaimed in the current checkout and may be corrected like the item under the brief's explicit unclaimed-module rule. No signature of a module held by another group is changed.

Source checked: [Stacks 00R6](https://stacks.math.columbia.edu/tag/00R6), with the systems of [00QX](https://stacks.math.columbia.edu/tag/00QX).

## Old

```lean
theorem exists_flat_stage
    {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)] [Nonempty Λ]
    (A : Λ ⥤ CommRingCat.{v}) (B : Λ ⥤ CommRingCat.{w})
    (N : Λ ⥤ AddCommGrpCat.{z}) [HasColimit A] [HasColimit B] [HasColimit N]
    [∀ i, IsLocalRing (A.obj i)] [∀ i, IsLocalRing (B.obj i)]
    [∀ i, IsNoetherianRing (A.obj i)] [∀ i, IsNoetherianRing (B.obj i)]
    [∀ i, Module (B.obj i) (N.obj i)] [∀ i, Module.Finite (B.obj i) (N.obj i)]
    (φ : ∀ i, A.obj i →+* B.obj i)
    (hφ : ∀ i, IsLocalHom (φ i))
    (hA : ∀ (i j : Λ) (f : i ⟶ j), IsLocalHom (A.map f).hom)
    (hB : ∀ (i j : Λ) (f : i ⟶ j), IsLocalHom (B.map f).hom)
    (hcomm : ∀ (i j : Λ) (f : i ⟶ j),
      (B.map f).hom.comp (φ i) = (φ j).comp (A.map f).hom)
    (hscalar : ∀ (i j : Λ) (f : i ⟶ j) (b : B.obj i) (x : N.obj i),
      (N.map f).hom (b • x) = (B.map f).hom b • (N.map f).hom x)
    (ψ : (colimit A : CommRingCat.{v}) →+* (colimit B : CommRingCat.{w}))
    (hψ : ∀ i, ψ.comp (colimit.ι A i).hom = (colimit.ι B i).hom.comp (φ i))
    [Module (colimit B : CommRingCat.{w}) (colimit N : AddCommGrpCat.{z})]
    (hlimitScalar : ∀ (i : Λ) (b : B.obj i) (x : N.obj i),
      (colimit.ι N i).hom (b • x) = (colimit.ι B i).hom b • (colimit.ι N i).hom x)
    (hloc : ∀ (i j : Λ) (f : i ⟶ j),
      letI := (φ i).toAlgebra
      letI := (A.map f).hom.toAlgebra
      ∃ (q : B.obj i ⊗[A.obj i] A.obj j →+* B.obj j)
        (W : Submonoid (B.obj i ⊗[A.obj i] A.obj j)),
        (∀ (b : B.obj i) (a : A.obj j),
          q (TensorProduct.tmul (A.obj i) b a) = (B.map f).hom b * φ j a) ∧
        (letI := q.toAlgebra; IsLocalization W (B.obj j)))
    (hbase : ∀ (i j : Λ) (f : i ⟶ j),
      letI := (B.map f).hom.toAlgebra
      ∃ e : (B.obj j ⊗[B.obj i] N.obj i) ≃ₗ[B.obj j] N.obj j,
        ∀ (b : B.obj j) (x : N.obj i),
          e (TensorProduct.tmul (B.obj i) b x) = b • (N.map f).hom x)
    (hflat : letI := Module.compHom (colimit N : AddCommGrpCat.{z}) ψ
      Module.Flat (colimit A : CommRingCat.{v}) (colimit N : AddCommGrpCat.{z})) :
    ∃ i : Λ, letI := Module.compHom (N.obj i) (φ i)
      Module.Flat (A.obj i) (N.obj i)
```

## New

```lean
theorem exists_flat_stage
    {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)] [Nonempty Λ]
    (A : Λ ⥤ CommRingCat.{v}) (B : Λ ⥤ CommRingCat.{w})
    (N : Λ ⥤ AddCommGrpCat.{z}) [HasColimit A] [HasColimit B] [HasColimit N]
    [PreservesColimit A (forget CommRingCat.{v})]
    [∀ i, IsLocalRing (A.obj i)] [∀ i, IsLocalRing (B.obj i)]
    [∀ i, IsNoetherianRing (A.obj i)] [∀ i, IsNoetherianRing (B.obj i)]
    [∀ i, Module (B.obj i) (N.obj i)] [∀ i, Module.Finite (B.obj i) (N.obj i)]
    (φ : ∀ i, A.obj i →+* B.obj i)
    (hφ : ∀ i, IsLocalHom (φ i))
    (hA : ∀ (i j : Λ) (f : i ⟶ j), IsLocalHom (A.map f).hom)
    (hB : ∀ (i j : Λ) (f : i ⟶ j), IsLocalHom (B.map f).hom)
    (hcomm : ∀ (i j : Λ) (f : i ⟶ j),
      (B.map f).hom.comp (φ i) = (φ j).comp (A.map f).hom)
    (hscalar : ∀ (i j : Λ) (f : i ⟶ j) (b : B.obj i) (x : N.obj i),
      (N.map f).hom (b • x) = (B.map f).hom b • (N.map f).hom x)
    (ψ : (colimit A : CommRingCat.{v}) →+* (colimit B : CommRingCat.{w}))
    (hψ : ∀ i, ψ.comp (colimit.ι A i).hom = (colimit.ι B i).hom.comp (φ i))
    [Module (colimit B : CommRingCat.{w}) (colimit N : AddCommGrpCat.{z})]
    (hlimitScalar : ∀ (i : Λ) (b : B.obj i) (x : N.obj i),
      (colimit.ι N i).hom (b • x) = (colimit.ι B i).hom b • (colimit.ι N i).hom x)
    (hloc : ∀ (i j : Λ) (f : i ⟶ j),
      letI := (φ i).toAlgebra
      letI := (A.map f).hom.toAlgebra
      ∃ (q : B.obj i ⊗[A.obj i] A.obj j →+* B.obj j)
        (W : Submonoid (B.obj i ⊗[A.obj i] A.obj j)),
        (∀ (b : B.obj i) (a : A.obj j),
          q (TensorProduct.tmul (A.obj i) b a) = (B.map f).hom b * φ j a) ∧
        (letI := q.toAlgebra; IsLocalization W (B.obj j)))
    (hbase : ∀ (i j : Λ) (f : i ⟶ j),
      letI := (B.map f).hom.toAlgebra
      ∃ e : (B.obj j ⊗[B.obj i] N.obj i) ≃ₗ[B.obj j] N.obj j,
        ∀ (b : B.obj j) (x : N.obj i),
          e (TensorProduct.tmul (B.obj i) b x) = b • (N.map f).hom x)
    (hflat : letI := Module.compHom (colimit N : AddCommGrpCat.{z}) ψ
      Module.Flat (colimit A : CommRingCat.{v}) (colimit N : AddCommGrpCat.{z})) :
    ∃ i : Λ, letI := Module.compHom (N.obj i) (φ i)
      Module.Flat (A.obj i) (N.obj i)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.ColimitEventuallyFlat | unclaimed | Interface correction, public preservation import, complete proof. |
| Sheaf.RingTheory.FiniteTypeApproximationFlatPoint | unclaimed | Same original signature. Proof-only ring filtered-colimit import provides preservation. |
| Sheaf.RingTheory.IntegerApproximationFlatPointStage | unclaimed | Same original signature. Proof-only ring filtered-colimit import provides preservation. |
| Sheaf.RingTheory.NoetherianLocalModelTowerBaseFlatStage | unclaimed | Unchanged: already imports filtered ring colimits and compiles against the corrected interface. |
| Sheaf.RingTheory.NoetherianLocalModelTowerFiberFlatStage | unclaimed | Same original signature. Proof-only ring filtered-colimit import provides preservation. |

All callers were found by tools/downstream.py --uses and a source-wide rg scan. Transitive importers keep their signatures and do not require changes.

## Status

landed 20261014T123028-L-2779298 2026-10-14 (merge of deliver/XReedb48d351b955d4/Sheaf.RingTheory.ColimitFlatRelationDescent)
