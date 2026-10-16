# AlgebraicGeometry.ProEtale.exists_etale_cech_cocycle_lift

## Reason

Restore the module and DAG node assigned to E2 at the start of this session. They
were present in the initial read-only snapshot, but a shared refresh removed
them. The required dry run confirms that the fetched delivery base has neither:
it classifies the item as a new module and requests this interface record.

The assigned theorem is now proved with exactly its original signature. There is
no mathematical statement change and no existing definition or target is changed.
The original node title, statement, source and blueprint provenance are preserved.
Because the node is absent from the delivery base, its created/lean.by metadata
must identify this restoring delivery as E2. The initial node was created by D3
from AffineComparisonInjectiveVanishingAux; this historical fact is preserved here.

## Old

On the fetched delivery base the module and declaration are absent. In the
initially assigned snapshot, the declaration had the signature below and proof
`:= by sorry`:

```lean
theorem exists_etale_cech_cocycle_lift
    (Y : Scheme.{u}) [IsAffine Y]
    (J : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (V : Y.ProEt) (hV : proAffineEtale V.hom)
    {n : ℕ} (U : Fin n → Over V)
    (hU : ∀ (k : ℕ) (y : Fin (k + 1) → Fin n),
      proAffineEtale (Presheaf.cechNerveObj U y).left.hom)
    (hcover : Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈
      Scheme.ProEt.topology Y V) (q : ℕ)
    (c : ((Presheaf.cechComplex U).obj
      ((comparisonUpperStar AddCommGrpCat.{u + 1} Y).obj J).obj).X (q + 1))
    (hc : ((Presheaf.cechComplex U).obj
      ((comparisonUpperStar AddCommGrpCat.{u + 1} Y).obj J).obj).d (q + 1) (q + 2) c = 0) :
    ∃ (W : Y.Etale) (T : ULift.{u + 1} (Fin n) → Y.Etale)
      (f : ∀ i, T i ⟶ W),
      Sieve.ofArrows T f ∈ Y.smallEtaleTopology W ∧
      ∃ (φ : (cechComplexFunctor fun i ↦ Over.mk (f i)).obj
          ((Over.forget W).op ⋙ J.obj) ⟶
        (Presheaf.cechComplex U).obj
          ((comparisonUpperStar AddCommGrpCat.{u + 1} Y).obj J).obj)
        (c' : ((cechComplexFunctor fun i ↦ Over.mk (f i)).obj
          ((Over.forget W).op ⋙ J.obj)).X (q + 1)),
        ((cechComplexFunctor fun i ↦ Over.mk (f i)).obj
          ((Over.forget W).op ⋙ J.obj)).d (q + 1) (q + 2) c' = 0 ∧
          φ.f (q + 1) c' = c
```

## New

Restore the same signature with a complete proof and six fully proved helper
modules. No sorry or additional axiom is introduced:

```lean
theorem exists_etale_cech_cocycle_lift
    (Y : Scheme.{u}) [IsAffine Y]
    (J : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (V : Y.ProEt) (hV : proAffineEtale V.hom)
    {n : ℕ} (U : Fin n → Over V)
    (hU : ∀ (k : ℕ) (y : Fin (k + 1) → Fin n),
      proAffineEtale (Presheaf.cechNerveObj U y).left.hom)
    (hcover : Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈
      Scheme.ProEt.topology Y V) (q : ℕ)
    (c : ((Presheaf.cechComplex U).obj
      ((comparisonUpperStar AddCommGrpCat.{u + 1} Y).obj J).obj).X (q + 1))
    (hc : ((Presheaf.cechComplex U).obj
      ((comparisonUpperStar AddCommGrpCat.{u + 1} Y).obj J).obj).d (q + 1) (q + 2) c = 0) :
    ∃ (W : Y.Etale) (T : ULift.{u + 1} (Fin n) → Y.Etale)
      (f : ∀ i, T i ⟶ W),
      Sieve.ofArrows T f ∈ Y.smallEtaleTopology W ∧
      ∃ (φ : (cechComplexFunctor fun i ↦ Over.mk (f i)).obj
          ((Over.forget W).op ⋙ J.obj) ⟶
        (Presheaf.cechComplex U).obj
          ((comparisonUpperStar AddCommGrpCat.{u + 1} Y).obj J).obj)
        (c' : ((cechComplexFunctor fun i ↦ Over.mk (f i)).obj
          ((Over.forget W).op ⋙ J.obj)).X (q + 1)),
        ((cechComplexFunctor fun i ↦ Over.mk (f i)).obj
          ((Over.forget W).op ⋙ J.obj)).d (q + 1) (q + 2) c' = 0 ∧
          φ.f (q + 1) c' = c
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineComparisonCechCocycleDescent | E2 | Restored assigned module; unchanged assigned signature, complete proof. |

There are no importers in the fetched base: the item module is absent there.
The originally assigned parent AffineComparisonInjectiveVanishingAux was also
refreshed to a version without this import; this delivery does not adapt that
parent or change its signature. The six new supporting modules have no existing
importers. No forced adaptation is needed.

## Status

landed 20261016T030335-L-1617670 2026-10-16 (merge of deliver/E2/Sheaf.AlgebraicGeometry.AffineComparisonCechCocycleDescent)
