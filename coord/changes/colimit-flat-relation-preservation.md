# RingTheory.exists_stage_flat_relation_factorization

## Reason

The original independent-universe categorical colimit statement was already disputed
and is false in the large-index/small-ring valuation-domain example recorded by V2.
The source uses algebraic directed colimits, whose representatives and equality
relations are preserved on underlying sets. Make that condition explicit and reuse
the already fully proved elementwise theorem directly. The landing return identified
the previous wrapper as a duplicate statement; withdrawing it removes that duplicate.
The five target signatures and all
existing definitions remain unchanged. This is a statement repair, not a proof of
the false original statement.

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

Withdraw `lean/Sheaf/RingTheory/ColimitFlatRelationDescent.lean` through `deleted.txt`.
The landing leaves an empty module. The false original theorem is retired, and no
replacement wrapper or alias is introduced. Both callers directly import
`Sheaf.RingTheory.ColimitFlatRelationDescentElementwise` and apply the already proved
`RingTheory.exists_stage_flat_relation_factorization_of_preserves`. The original
node's Lean attachment points to this existing declaration, whose signature is:

```lean
theorem exists_stage_flat_relation_factorization_of_preserves
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
| Sheaf.RingTheory.ColimitFlatRelationDescent | N1 | Withdrawn: remove the false original and rejected duplicate wrapper; reuse the existing theorem directly. |
| Sheaf.RingTheory.IdealKernelElementDescent | unclaimed | Same original signature; replace the proof import and theorem application by the existing elementwise version, and add the filtered-colimit preservation instance import. |
| Sheaf.RingTheory.FiniteIdealKernelDescent | unclaimed | Add preservation under the unclaimed-module rule; retain the complete tensor proof and import/apply the existing elementwise theorem directly. No sorry. |

The complete caller scan is `tools/downstream.py --uses exists_stage_flat_relation_factorization`.
Both original callers import the retired module and apply the retired theorem.
They now import and apply the existing elementwise theorem instead. This theorem
requires `PreservesColimit A (forget CommRingCat)`, which the old independent-universe
interface did not supply.
The common-universe single-element caller needs only its filtered-colimit instance.
The independent-universe finite-kernel caller requires the same interface correction;
its node, signature, proof route and statement-change record are in this delivery.
The correction is propagated through the unclaimed maximal-kernel and eventual-flatness
interfaces. All four callers of eventual flatness have sufficient ring universes and
keep their original signatures. Separate change records describe those corrections.
This packet uses the explicit permission to correct unclaimed modules, rather than
the signature-preserving forced-adaptation exception for another group's held module.
No target signature or definition changes, no false statement is retained, and no
proof is retracted to sorry.

## Status

landed 20261014T100433-L-1021718 2026-10-14 (merge of deliver/N1/Sheaf.RingTheory.ColimitFlatRelationDescent)
