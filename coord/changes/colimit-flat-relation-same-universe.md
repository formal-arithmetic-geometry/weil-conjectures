# RingTheory.exists_stage_flat_relation_factorization

## Reason

The launcher instruction of 2026-10-14 explicitly authorizes the common-universe
correction and the sole caller adaptation in this same delivery. Independent
universes permit non-algebraic ring colimits and make the old statements false.
No preservation binder, target change, or new definition is used. The launcher claimed the caller for P1.

## Old

```lean
theorem exists_stage_flat_relation_factorization
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
    (i : Λ) {ι : Type t} [Fintype ι] (a : ι → A.obj i) (x : ι → N.obj i)
    (hx : ∑ p, (φ i) (a p) • x p = 0) :
    ∃ (j : Λ) (f : i ⟶ j) (m : ℕ)
      (c : ι → Fin m → A.obj j) (y : Fin m → N.obj j),
      (∀ p, (N.map f).hom (x p) = ∑ q, (φ j) (c p q) • y q) ∧
      (∀ q, ∑ p, (A.map f).hom (a p) * c p q = 0)
```

## New

```lean
theorem exists_stage_flat_relation_factorization
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
    (i : Λ) {ι : Type t} [Fintype ι] (a : ι → A.obj i) (x : ι → N.obj i)
    (hx : ∑ p, (φ i) (a p) • x p = 0) :
    ∃ (j : Λ) (f : i ⟶ j) (m : ℕ)
      (c : ι → Fin m → A.obj j) (y : Fin m → N.obj j),
      (∀ p, (N.map f).hom (x p) = ∑ q, (φ j) (c p q) • y q) ∧
      (∀ q, ∑ p, (A.map f).hom (a p) * c p q = 0)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.ColimitFlatRelationDescent | P1 | Same-universe correction; inferred preservation and proved elementwise argument. |
| Sheaf.RingTheory.IdealKernelElementDescent | P1 | Owned statement correction; original complete tensor proof restored. |
| Sheaf.RingTheory.FiniteIdealKernelDescent | unclaimed | Independent-universe downstream caller fails at its tensor-kernel application; its statement needs its own correction outside this two-module delivery. |

Only diagram-universe annotations change in the caller; its private helper,
conclusion, visibility and original proof are retained. This is an expressly
authorized statement correction, not an unchanged-signature adaptation.

## Status

landed 20261014T045611-L-1573613 2026-10-14 (merge of deliver/P1/Sheaf.RingTheory.ColimitFlatRelationDescent)
