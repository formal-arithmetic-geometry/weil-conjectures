# AlgebraicGeometry.refine_geometric_generic_cover_model_data

## Reason

Reviewer X-c640f (returned head c640f97a9) confirmed this statement is false.
Over Spec k, take X = S = T = Spec k, the maps to be identities, I = Bool,
and both A_i = univ. Set C_false = empty and C_true = univ. All hypotheses
hold, but the empty C_false has an empty geometric fibre, which is not
IsIrreducible. The asserted intersection conclusion also fails.
The hypotheses never identify generic traces of C_i with A_i, and the
conclusion does not permit shrinking the arbitrary model.

## Old

```lean
theorem refine_geometric_generic_cover_model_data {X S : Scheme.{u}}
    [IrreducibleSpace S] (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f]
    {L : Type u} [Field L]
    (yη : Spec (CommRingCat.of L) ⟶
      Spec (CommRingCat.of (S.residueField (genericPoint S))))
    [IsFinite yη] [Etale yη] {I : Type u} [Finite I]
    (A : I → Set ↥(pullback (f.fiberToSpecResidueField (genericPoint S)) yη))
    (hclosed : ∀ i, IsClosed (A i)) (hcover : (⋃ i, A i) = Set.univ)
    (hgeom : ∀ i, ∀ (E : Type u) (_ : Field E)
      (z : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of L)),
      IsIrreducible ((pullback.fst
        (pullback.snd (f.fiberToSpecResidueField (genericPoint S)) yη) z) ⁻¹' A i))
    {T : Scheme.{u}} {g : T ⟶ S} {η : T}
    {C : I → Set ↥(pullback f g)}
    (hg : Etale g) (hη : IsGenericPoint η Set.univ)
    (hgη : g η = genericPoint S) (hCclosed : ∀ i, IsClosed (C i))
    (hCcover : (⋃ i, C i) = Set.univ) :
    (∀ i t, ∀ (E : Type u) (_ : Field E)
      (z : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of (T.residueField t))),
      IsIrreducible ((pullback.fst
        ((pullback.snd f g).fiberToSpecResidueField t) z ≫
        (pullback.snd f g).fiberι t) ⁻¹' C i)) ∧
      ∀ i j, (A i ∩ A j).Nonempty →
        (C i ∩ C j ∩ (pullback.snd f g) ⁻¹' {η}).Nonempty
```

The old proof of exists_geometric_generic_cover_model first obtained model data,
then applied the false refinement to that arbitrary closed cover.

## New

Remove refine_geometric_generic_cover_model_data entirely. Restore the whole
proof of exists_geometric_generic_cover_model to `:= by sorry`, preserving
its signature and complete proof docstring verbatim. Retain the proved
exists_geometric_generic_cover_model_data unchanged.

Clear the main node's invalid combining proof and proof_deps. Retain the
refinement node as historical, set lean to null (no Lean record), and clear
its invalid proof and proof_deps. Record withdrawal in both proof_origin fields.
No DAG statement or target signature changes.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.GeometricGenericCoverModel | W4 | Sole Lean user: exists_geometric_generic_cover_model; replace the invalid combining proof by a whole named theorem sorry. |

Repository-wide rg and tools/downstream.py --uses find no other Lean user.
All downstream statements retain their signatures; no other module needs adaptation.

## Status

landed 20261013T025312-L-3426067 2026-10-13 (merge of deliver/W4/Sheaf.AlgebraicGeometry.GeometricGenericCoverModel)
