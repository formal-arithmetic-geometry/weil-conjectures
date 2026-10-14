# RingTheory.exists_stage_ideal_kernel_element_vanishes

## Reason

Launcher instruction (2026-10-14) corrects the false independent-universe
interface by placing the indexing type, `A`, `B`, and `N` in the common universe
`Type u`. This makes Mathlib's filtered-colimit algebraic preservation instance
available and permits the original tensor proof to apply.

## Old

```lean
theorem exists_stage_ideal_kernel_element_vanishes
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
    ∀ (k : I ⊗[A.obj i] N.obj i),
      TensorProduct.lift ((LinearMap.lsmul (A.obj i) (N.obj i)).comp I.subtype) k = 0 →
    ∃ (j : Λ) (f : i ⟶ j),
      letI := Module.compHom (N.obj i) (φ i)
      letI := Module.compHom (N.obj j) (φ j)
      ∃ θ : I ⊗[A.obj i] N.obj i →+
          (I.map (A.map f).hom) ⊗[A.obj j] N.obj j,
        (∀ (a : I) (x : N.obj i), θ (a ⊗ₜ[A.obj i] x) =
          (⟨(A.map f).hom a, Ideal.mem_map_of_mem (A.map f).hom a.property⟩ :
            I.map (A.map f).hom) ⊗ₜ[A.obj j] (N.map f).hom x) ∧
        θ k = 0
```

## New

```lean
theorem exists_stage_ideal_kernel_element_vanishes
    {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)] [Nonempty Λ]
    (A : Λ ⥤ CommRingCat.{u}) (B : Λ ⥤ CommRingCat.{u})
    (N : Λ ⥤ AddCommGrpCat.{u}) [HasColimit A] [HasColimit B] [HasColimit N]
    [∀ i, Module (B.obj i) (N.obj i)]
    (φ : ∀ i, A.obj i →+* B.obj i)
    (hcomm : ∀ (i j : Λ) (f : i ⟶ j),
      (B.map f).hom.comp (φ i) = (φ j).comp (A.map f).hom)
    (hscalar : ∀ (i j : Λ) (f : i ⟶ j) (b : B.obj i) (x : N.obj i),
      (N.map f).hom (b • x) = (B.map f).hom b • (N.map f).hom x)
    (ψ : (colimit A : CommRingCat.{u}) →+* (colimit B : CommRingCat.{u}))
    (hψ : ∀ i, ψ.comp (colimit.ι A i).hom = (colimit.ι B i).hom.comp (φ i))
    [Module (colimit B : CommRingCat.{u}) (colimit N : AddCommGrpCat.{u})]
    (hlimitScalar : ∀ (i : Λ) (b : B.obj i) (x : N.obj i),
      (colimit.ι N i).hom (b • x) = (colimit.ι B i).hom b • (colimit.ι N i).hom x)
    (hflat : letI := Module.compHom (colimit N : AddCommGrpCat.{u}) ψ
      Module.Flat (colimit A : CommRingCat.{u}) (colimit N : AddCommGrpCat.{u}))
    (i : Λ) (I : Ideal (A.obj i)) :
    letI := Module.compHom (N.obj i) (φ i)
    ∀ (k : I ⊗[A.obj i] N.obj i),
      TensorProduct.lift ((LinearMap.lsmul (A.obj i) (N.obj i)).comp I.subtype) k = 0 →
    ∃ (j : Λ) (f : i ⟶ j),
      letI := Module.compHom (N.obj i) (φ i)
      letI := Module.compHom (N.obj j) (φ j)
      ∃ θ : I ⊗[A.obj i] N.obj i →+
          (I.map (A.map f).hom) ⊗[A.obj j] N.obj j,
        (∀ (a : I) (x : N.obj i), θ (a ⊗ₜ[A.obj i] x) =
          (⟨(A.map f).hom a, Ideal.mem_map_of_mem (A.map f).hom a.property⟩ :
            I.map (A.map f).hom) ⊗ₜ[A.obj j] (N.map f).hom x) ∧
        θ k = 0
```

## Compiler evidence

Against the corrected colimit-relation theorem, the old caller failed at its
finite-relation application with:

```
failed to synthesize instance of type class
  PreservesColimit A (forget CommRingCat)
```

After the common-universe correction, the original
proof compiles and has no `sorryAx`.

## Holder

P1 holds both `Sheaf.RingTheory.ColimitFlatRelationDescent` and this caller in
this repair delivery, as instructed by the launcher update.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.IdealKernelElementDescent | P1 | Common-universe correction with original proof. |
| Sheaf.RingTheory.FiniteIdealKernelDescent | unclaimed | Its independent-universe interface requires a subsequent correction. |

## Status

landed 20261014T045611-L-1573613 2026-10-14 (merge of deliver/P1/Sheaf.RingTheory.ColimitFlatRelationDescent)
