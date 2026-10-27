# CategoryTheory.AmbientCompletedTensor.quotientTotalTensorTowerComparison

## Reason

Complete the existing, unclaimed dependency of the assigned ambient adjunction.
The scalar comparison used for the finite successor also proves this strict tower
comparison. Keeping its proof in this existing module prevents the assigned item
from exceeding the per-file compile limit. This is a proof-only change: the
statement, visibility, public imports and existing attributes are unchanged.
Private helpers describe the actual finite functor and its generators.

## Old

```lean
theorem quotientTotalTensorTowerComparison
    (τ : ∀ n : ℕ, (((change (projection J A I (n + 1))).mapHomologicalComplex (.up ℤ)).prod
        ((change (projection J A I (n + 1))).mapHomologicalComplex (.up ℤ)) ⋙
      coefficientTotalTensor.{u, u, u} J (finite J A I (n + 1)) ⋙
        (res (projection J A I (n + 1))).mapHomologicalComplex (.up ℤ)) ⟶
      (((change (projection J A I n)).mapHomologicalComplex (.up ℤ)).prod
        ((change (projection J A I n)).mapHomologicalComplex (.up ℤ)) ⋙
      coefficientTotalTensor.{u, u, u} J (finite J A I n) ⋙
        (res (projection J A I n)).mapHomologicalComplex (.up ℤ)))
    (hτ : ∀ (n : ℕ) (P Q : Cx (completed J A I))
      (p q k : ℤ) (h : p + q = k) (U : Cᵒᵖ)
      (a b : (finite J A I (n + 1)).obj.obj U)
      (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
      (((τ n).app (P, Q)).f k).val.app U
        (coefficientTensorGenerator.{u, u, u} J (finite J A I (n + 1))
          (((change (projection J A I (n + 1))).mapHomologicalComplex (.up ℤ)).obj P)
          (((change (projection J A I (n + 1))).mapHomologicalComplex (.up ℤ)).obj Q)
          p q k h U
          (tensorSection (projection J A I (n + 1)) (P.X p) U a x)
            (tensorSection (projection J A I (n + 1)) (Q.X q) U b y)) =
        coefficientTensorGenerator.{u, u, u} J (finite J A I n)
          (((change (projection J A I n)).mapHomologicalComplex (.up ℤ)).obj P)
          (((change (projection J A I n)).mapHomologicalComplex (.up ℤ)).obj Q)
          p q k h U
          (tensorSection (projection J A I n) (P.X p) U ((transition J A I n).hom.app U a) x)
            (tensorSection (projection J A I n) (Q.X q) U ((transition J A I n).hom.app U b) y))
    (P Q : Cx (completed J A I)) :
    ∃ (V : CochainComplex (ℕᵒᵖ ⥤ Mod (completed J A I)) ℤ)
      (b : reductionComplex J A I true
        ((coefficientTotalTensor.{u, u, u} J (completed J A I)).obj (P, Q)) ≅ V)
      (κ : V.asFunctor ≅
      (Functor.ofOpSequence (X := fun n : ℕ ↦
        (((change (projection J A I n)).mapHomologicalComplex (.up ℤ)).prod
        ((change (projection J A I n)).mapHomologicalComplex (.up ℤ)) ⋙
      coefficientTotalTensor.{u, u, u} J (finite J A I n) ⋙
        (res (projection J A I n)).mapHomologicalComplex (.up ℤ))) τ).flip.obj (P, Q)),
      ∀ (n : ℕ) (p q k : ℤ) (h : p + q = k) (U : Cᵒᵖ)
        (c : (finite J A I n).obj.obj U)
        (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
        ((κ.hom.app (op n)).f k).val.app U
          (((b.hom.f k).app (op n)).val.app U
            (tensorSection (projection J A I n)
            (((coefficientTotalTensor.{u, u, u} J (completed J A I)).obj (P, Q)).X k) U c
            (coefficientTensorGenerator.{u, u, u} J (completed J A I)
              P Q p q k h U x y))) =
          coefficientTensorGenerator.{u, u, u} J (finite J A I n)
          (((change (projection J A I n)).mapHomologicalComplex (.up ℤ)).obj P)
          (((change (projection J A I n)).mapHomologicalComplex (.up ℤ)).obj Q)
          p q k h U
          (tensorSection (projection J A I n) (P.X p) U 1 x)
            (tensorSection (projection J A I n) (Q.X q) U c y)
```

The theorem body was `by sorry`.

## New

```lean
theorem quotientTotalTensorTowerComparison
    (τ : ∀ n : ℕ, (((change (projection J A I (n + 1))).mapHomologicalComplex (.up ℤ)).prod
        ((change (projection J A I (n + 1))).mapHomologicalComplex (.up ℤ)) ⋙
      coefficientTotalTensor.{u, u, u} J (finite J A I (n + 1)) ⋙
        (res (projection J A I (n + 1))).mapHomologicalComplex (.up ℤ)) ⟶
      (((change (projection J A I n)).mapHomologicalComplex (.up ℤ)).prod
        ((change (projection J A I n)).mapHomologicalComplex (.up ℤ)) ⋙
      coefficientTotalTensor.{u, u, u} J (finite J A I n) ⋙
        (res (projection J A I n)).mapHomologicalComplex (.up ℤ)))
    (hτ : ∀ (n : ℕ) (P Q : Cx (completed J A I))
      (p q k : ℤ) (h : p + q = k) (U : Cᵒᵖ)
      (a b : (finite J A I (n + 1)).obj.obj U)
      (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
      (((τ n).app (P, Q)).f k).val.app U
        (coefficientTensorGenerator.{u, u, u} J (finite J A I (n + 1))
          (((change (projection J A I (n + 1))).mapHomologicalComplex (.up ℤ)).obj P)
          (((change (projection J A I (n + 1))).mapHomologicalComplex (.up ℤ)).obj Q)
          p q k h U
          (tensorSection (projection J A I (n + 1)) (P.X p) U a x)
            (tensorSection (projection J A I (n + 1)) (Q.X q) U b y)) =
        coefficientTensorGenerator.{u, u, u} J (finite J A I n)
          (((change (projection J A I n)).mapHomologicalComplex (.up ℤ)).obj P)
          (((change (projection J A I n)).mapHomologicalComplex (.up ℤ)).obj Q)
          p q k h U
          (tensorSection (projection J A I n) (P.X p) U ((transition J A I n).hom.app U a) x)
            (tensorSection (projection J A I n) (Q.X q) U ((transition J A I n).hom.app U b) y))
    (P Q : Cx (completed J A I)) :
    ∃ (V : CochainComplex (ℕᵒᵖ ⥤ Mod (completed J A I)) ℤ)
      (b : reductionComplex J A I true
        ((coefficientTotalTensor.{u, u, u} J (completed J A I)).obj (P, Q)) ≅ V)
      (κ : V.asFunctor ≅
      (Functor.ofOpSequence (X := fun n : ℕ ↦
        (((change (projection J A I n)).mapHomologicalComplex (.up ℤ)).prod
        ((change (projection J A I n)).mapHomologicalComplex (.up ℤ)) ⋙
      coefficientTotalTensor.{u, u, u} J (finite J A I n) ⋙
        (res (projection J A I n)).mapHomologicalComplex (.up ℤ))) τ).flip.obj (P, Q)),
      ∀ (n : ℕ) (p q k : ℤ) (h : p + q = k) (U : Cᵒᵖ)
        (c : (finite J A I n).obj.obj U)
        (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
        ((κ.hom.app (op n)).f k).val.app U
          (((b.hom.f k).app (op n)).val.app U
            (tensorSection (projection J A I n)
            (((coefficientTotalTensor.{u, u, u} J (completed J A I)).obj (P, Q)).X k) U c
            (coefficientTensorGenerator.{u, u, u} J (completed J A I)
              P Q p q k h U x y))) =
          coefficientTensorGenerator.{u, u, u} J (finite J A I n)
          (((change (projection J A I n)).mapHomologicalComplex (.up ℤ)).obj P)
          (((change (projection J A I n)).mapHomologicalComplex (.up ℤ)).obj Q)
          p q k h U
          (tensorSection (projection J A I n) (P.X p) U 1 x)
            (tensorSection (projection J A I n) (Q.X q) U c y)
```

The body is a complete proof. The normalized finite scalar comparisons commute
with successors by the given generator formula and total-extension
extensionality. `NatTrans.ofOpSequence` assembles them into the required strict
isomorphism; the reduction complex and identity give V and b.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.QuotientTotalTensorTowerComparison | unclaimed | Sole hole proved; public interface unchanged. |
| Sheaf.Paper.AmbientCompletedTensorAdjunction | G2 | Existing dependency now proved; original application retained. |

The only original direct importer is the assigned module, currently preserved in
its quarantine archive. It is compiled with this delivery. No signatures or
instances seen by importers change, and no forced adaptations are needed.

## Status

landed 20261027T065850-L-2483130 2026-10-27 (merge of deliver/G2/Sheaf.Paper.AmbientCompletedTensorAdjunction)
