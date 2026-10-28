# WeilConjectures.podReindexingTensorRoosNormalization_model_iff_canonical

## Reason

STATEMENT-DISPUTED: the former theorem inferred both Model and global Canonical
from conditions that mention only T.tower. The field T.tensor is independently
supplied, with no relation to that tower in either hypothesis. Keeping the tower
and replacing the tensor comparison by a nontrivial scalar automorphism preserves
both hypotheses and changes the claimed conclusion on any nonzero tensor object.
Moreover, without naturality of T.tensor, representative equations cannot determine
its values on arbitrary isomorphic presentations. The repair states precisely the
valid representative equivalence, and the parent supplies its existing Canonical
hypothesis. No target statement or definition changes.

## Old

```lean
theorem podReindexingTensorRoosNormalization_model_iff_canonical
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (hgen : PodCompletedTensorReindex.Generators l E g D T)
    (hnat : PodCompletedTensorReindex.TowerNaturality l E g D T) :
    PodCompletedTensorReindex.Model l E g D T ∧
      PodCompletedTensorReindex.Canonical l E g D T
```

## New

```lean
theorem podReindexingTensorRoosNormalization_model_iff_canonical
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (hgen : PodCompletedTensorReindex.Generators l E g D T) :
    PodCompletedTensorReindex.Model l E g D T ↔
      ∀ (P Q : (integralOperationsGoodComplex l E Y).FullSubcategory)
        (hP : sfIntegralConstructible l E Y (DerivedCategory.Q.obj P.obj))
        (hQ : sfIntegralConstructible l E Y (DerivedCategory.Q.obj Q.obj)),
        (podOrdinaryToCompleted l E g D).app
            ((integralCompletedTensor l E Y).obj
              (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj)) ≫
            ((canonicalIntegralPullbackTensor l E g ⟨_,hP⟩ ⟨_,hQ⟩).hom).hom =
          (T.tensor ⟨_,hP⟩ ⟨_,hQ⟩).hom ≫
            (integralCompletedTensor l E X).map
              (Prod.mkHom
                ((podOrdinaryToCompleted l E g D).app (DerivedCategory.Q.obj P.obj))
                ((podOrdinaryToCompleted l E g D).app (DerivedCategory.Q.obj Q.obj)))
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.PodReindexingTensorRoosNormalization | unclaimed on server at inspection | Old call returns a conjunction and fails against the repaired equivalence. Pass its unchanged Canonical hypothesis pointwise to the reverse implication. |

The source search found this as the only direct importer and the only caller.
The parent's own node is updated to describe the actual argument, with no statement
change. The item node has a statement_change record naming its sole DAG citer.
The unit sk-def-weil has no realized statement or steps bypassed by this repair.

## Status

landed 20261028T055757-L-808146 2026-10-28 (merge of deliver/S7/Sheaf.Paper.PodReindexingTensorRoosStrict)
