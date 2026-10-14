# RingTheory.exists_stage_finite_ideal_kernel_vanishes

## Reason

The source uses algebraic directed ring colimits. Categorical colimits in an independently smaller ring universe do not guarantee underlying representatives or eventual equality. Propagate the explicit preservation condition, restore/retain the complete original proof, and adapt all actual callers. The module is unclaimed in the current checkout and may be corrected like the item under the brief's explicit unclaimed-module rule. No signature of a module held by another group is changed.

Source checked: [Stacks 00R6](https://stacks.math.columbia.edu/tag/00R6), with the systems of [00QX](https://stacks.math.columbia.edu/tag/00QX).

## Old

```lean
theorem exists_stage_finite_ideal_kernel_vanishes
    {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)] [Nonempty Λ]
    (A : Λ ⥤ CommRingCat.{v}) (B : Λ ⥤ CommRingCat.{w})
    (N : Λ ⥤ AddCommGrpCat.{z}) [HasColimit A] [HasColimit B] [HasColimit N]
    [∀ i, Module (B.obj i) (N.obj i)]
    (φ : ∀ i, A.obj i →+* B.obj i)
    (hcomm : ∀ (i j : Λ) (f : i ⟶ j),
      (B.map f).hom.comp (φ i) = (φ j).comp (A.map f).hom)
    (hscalar : ∀ (i j : Λ) (f : i ⟶ j) (b : B.obj i) (x : N.obj i),
      (N.map f).hom (b • x) = (B.map f).hom b • (N.map f).hom x)
    (ψ : (colimit A : CommRingCat.{v}) →+* (colimit B : CommRingCat.{w}))
    (hψ : ∀ i, ψ.comp (colimit.ι A i).hom = (colimit.ι B i).hom.comp (φ i))
    [Module (colimit B : CommRingCat.{w}) (colimit N : AddCommGrpCat.{z})]
    (hlimitScalar : ∀ (i : Λ) (b : B.obj i) (x : N.obj i),
      (colimit.ι N i).hom (b • x) = (colimit.ι B i).hom b • (colimit.ι N i).hom x)
    (hflat : letI := Module.compHom (colimit N : AddCommGrpCat.{z}) ψ
      Module.Flat (colimit A : CommRingCat.{v}) (colimit N : AddCommGrpCat.{z}))
    (i : Λ) (I : Ideal (A.obj i)) :
    letI := Module.compHom (N.obj i) (φ i)
    ∀ (s : Finset (I ⊗[A.obj i] N.obj i)),
      (∀ k ∈ s,
        TensorProduct.lift ((LinearMap.lsmul (A.obj i) (N.obj i)).comp I.subtype) k = 0) →
    ∃ (j : Λ) (f : i ⟶ j),
      letI := Module.compHom (N.obj i) (φ i)
      letI := Module.compHom (N.obj j) (φ j)
      ∃ θ : I ⊗[A.obj i] N.obj i →+
          (I.map (A.map f).hom) ⊗[A.obj j] N.obj j,
        (∀ (a : I) (x : N.obj i), θ (a ⊗ₜ[A.obj i] x) =
          (⟨(A.map f).hom a, Ideal.mem_map_of_mem (A.map f).hom a.property⟩ :
            I.map (A.map f).hom) ⊗ₜ[A.obj j] (N.map f).hom x) ∧
        (∀ k ∈ s, θ k = 0)
```

## New

```lean
theorem exists_stage_finite_ideal_kernel_vanishes
    {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)] [Nonempty Λ]
    (A : Λ ⥤ CommRingCat.{v}) (B : Λ ⥤ CommRingCat.{w})
    (N : Λ ⥤ AddCommGrpCat.{z}) [HasColimit A] [HasColimit B] [HasColimit N]
    [PreservesColimit A (forget CommRingCat.{v})]
    [∀ i, Module (B.obj i) (N.obj i)]
    (φ : ∀ i, A.obj i →+* B.obj i)
    (hcomm : ∀ (i j : Λ) (f : i ⟶ j),
      (B.map f).hom.comp (φ i) = (φ j).comp (A.map f).hom)
    (hscalar : ∀ (i j : Λ) (f : i ⟶ j) (b : B.obj i) (x : N.obj i),
      (N.map f).hom (b • x) = (B.map f).hom b • (N.map f).hom x)
    (ψ : (colimit A : CommRingCat.{v}) →+* (colimit B : CommRingCat.{w}))
    (hψ : ∀ i, ψ.comp (colimit.ι A i).hom = (colimit.ι B i).hom.comp (φ i))
    [Module (colimit B : CommRingCat.{w}) (colimit N : AddCommGrpCat.{z})]
    (hlimitScalar : ∀ (i : Λ) (b : B.obj i) (x : N.obj i),
      (colimit.ι N i).hom (b • x) = (colimit.ι B i).hom b • (colimit.ι N i).hom x)
    (hflat : letI := Module.compHom (colimit N : AddCommGrpCat.{z}) ψ
      Module.Flat (colimit A : CommRingCat.{v}) (colimit N : AddCommGrpCat.{z}))
    (i : Λ) (I : Ideal (A.obj i)) :
    letI := Module.compHom (N.obj i) (φ i)
    ∀ (s : Finset (I ⊗[A.obj i] N.obj i)),
      (∀ k ∈ s,
        TensorProduct.lift ((LinearMap.lsmul (A.obj i) (N.obj i)).comp I.subtype) k = 0) →
    ∃ (j : Λ) (f : i ⟶ j),
      letI := Module.compHom (N.obj i) (φ i)
      letI := Module.compHom (N.obj j) (φ j)
      ∃ θ : I ⊗[A.obj i] N.obj i →+
          (I.map (A.map f).hom) ⊗[A.obj j] N.obj j,
        (∀ (a : I) (x : N.obj i), θ (a ⊗ₜ[A.obj i] x) =
          (⟨(A.map f).hom a, Ideal.mem_map_of_mem (A.map f).hom a.property⟩ :
            I.map (A.map f).hom) ⊗ₜ[A.obj j] (N.map f).hom x) ∧
        (∀ k ∈ s, θ k = 0)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.FiniteIdealKernelDescent | unclaimed | Interface correction, public preservation import, complete proof. |
| Sheaf.RingTheory.ColimitMaximalKernelDescent | unclaimed | Correct the unclaimed interface with the same preservation binder; retain its proof. |

All callers were found by tools/downstream.py --uses and a source-wide rg scan. Transitive importers keep their signatures and do not require changes.

## Status

landed 20261014T100433-L-1021718 2026-10-14 (merge of deliver/N1/Sheaf.RingTheory.ColimitFlatRelationDescent)
