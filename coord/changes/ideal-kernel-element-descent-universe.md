# RingTheory.exists_stage_ideal_kernel_element_vanishes

## Reason

The launcher authorized restricting this statement to a common universe for the
index and diagram carriers, matching the intended elementwise colimit descent.
The previous independent-universe interface does not follow from categorical
colimits alone. This repair includes the caller that the earlier delivery missed.

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

The private `exists_ideal_tensor_map` helper previously quantified
`{R : Type v} {S : Type w} {M : Type z} {P : Type u}`.

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

The item's private helper now quantifies
`{R : Type u} {S : Type u} {M : Type u} {P : Type u}`.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.IdealKernelElementDescent | P1 | Authorized common-universe interface; tensor proof retained. |
| Sheaf.RingTheory.FiniteIdealKernelDescent | unclaimed | Forced proof adaptation; public signature and visibility unchanged. Replace the ill-typed single-element application with its finite-relation/tensor argument at the original carrier universes. |

These are both declaration users reported by `tools/downstream.py --uses
RingTheory.exists_stage_ideal_kernel_element_vanishes`; the first is the declaration
itself. Transitive importers see no changed public signature in the adapted caller.

### Necessary caller changes

The original caller fails at line 112 against the delivered dependency:

```text
Application type mismatch: The argument
  hs (↑k) k.property
has type
  Eq.{z + 1} (...) 0
but is expected to have type
  Eq.{u + 1} (...) 0
```

The proof-only import changes from `Sheaf.RingTheory.IdealKernelElementDescent`
to `Sheaf.RingTheory.ColimitFlatRelationDescent`. The `hpoint` proof is replaced:
expand the tensor, obtain the relation factorization, use the already present
private tensor-map helper and scalar-compatibility lemma, and cancel the finite
sums by balancing. The common-stage proof after `hpoint` is unchanged. The
proof docstring follows this necessary replacement; no declaration signature or
visibility changes. Both modules compile together with `lcompile.py --all`.

The existing independent-universe relation-factorization dependency is itself
marked `STATEMENT-DISPUTED`. The caller now carries the same explicit warning.
This repair preserves its public signature as required by the return; it does
not resolve that signature's mathematical defect. Correcting the independent-
universe caller and the relation dependency requires separate interface work;
no new assumption, theorem, or hole is added here.

## Status

landed 20261014T052440-L-1914123 2026-10-14 (merge of deliver/P1/Sheaf.RingTheory.IdealKernelElementDescent)
