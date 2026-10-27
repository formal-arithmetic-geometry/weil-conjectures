# WeilConjectures.commonStageDerivedInternalHom_existsUnique

## Reason

The original final theorem exceeds the fixed 60-second elaboration budget. Its
three `ofHom` applications infer a large stage family through the `StageHom`
abbreviation. Spell out the existing `StageSystem.PairCategory.mkHom` constructor,
its family, system, endpoints and universes instead. The definition of `ofHom` in
`GeneralAlgebraicallyClosedCoefficients.lean:532` is exactly this constructor.
The explicit stage projections and universes similarly elaborate the same terms.
No binder, hypothesis, conclusion, coefficient stage or representative map changes.
The complete module with these annotations compiled in 54.1 seconds.

Local transparency attributes keep chosen functors from unfolding while checking
these types; they do not export changes to importers. The four new proofs use the
published integral comparison and scalar-associator interfaces. All public
definition bodies remain verbatim.

## Old

```lean
theorem commonStageDerivedInternalHom_existsUnique (W : Scheme.{u}) :
    ∃! F : (commonStageHomPairs l Ω W).FullSubcategory ⥤
        generalAlgebraicallyClosedConstructibleCategory l Ω W,
      (∀ P, F.obj P = commonStageHomObject l Ω W P) ∧
      (∀ (P Q : (commonStageHomPairs l Ω W).FullSubcategory)
        (L : Index l Ω)
        (h : (commonStageHomObject l Ω W P).stage ≤ L)
        (h' : (commonStageHomObject l Ω W Q).stage ≤ L)
        (a : (commonStageHomPairAtStage l Ω W Q L h').obj.1.unop ⟶
          (commonStageHomPairAtStage l Ω W P L h).obj.1.unop)
        (b : (commonStageHomPairAtStage l Ω W P L h).obj.2 ⟶
          (commonStageHomPairAtStage l Ω W Q L h').obj.2),
        HEq (F.map (X := P) (Y := Q)
          (ObjectProperty.homMk (X := P) (Y := Q) (Prod.mkHom
            (ofHom Q.obj.1.unop P.obj.1.unop L
              (((Padic.finiteCoefficientFields_properties l Ω).1
                Q.obj.1.unop.stage Q.obj.2.stage).1.trans h')
              (((Padic.finiteCoefficientFields_properties l Ω).1
                P.obj.1.unop.stage P.obj.2.stage).1.trans h) a).op
            (ofHom P.obj.2 Q.obj.2 L
              (((Padic.finiteCoefficientFields_properties l Ω).1
                P.obj.1.unop.stage P.obj.2.stage).2.trans h)
              (((Padic.finiteCoefficientFields_properties l Ω).1
                Q.obj.1.unop.stage Q.obj.2.stage).2.trans h') b))))
          (ofHom (commonStageHomObject l Ω W P)
            (commonStageHomObject l Ω W Q) L h h'
            ((commonStageHomComparison l Ω W P L h).hom ≫
              (rationalDerivedInternalHom l (Coefficient.{u} l Ω L) W).map
                (X := commonStageHomPairAtStage l Ω W P L h)
                (Y := commonStageHomPairAtStage l Ω W Q L h')
                (ObjectProperty.homMk
                  (X := commonStageHomPairAtStage l Ω W P L h)
                  (Y := commonStageHomPairAtStage l Ω W Q L h')
                  (Prod.mkHom a.op b)) ≫
              (commonStageHomComparison l Ω W Q L h').inv)))
```

## New

```lean
theorem commonStageDerivedInternalHom_existsUnique (W : Scheme.{u}) :
    ∃! F : (commonStageHomPairs.{u, v} l Ω W).FullSubcategory ⥤
        generalAlgebraicallyClosedConstructibleCategory l Ω W,
      (∀ P, F.obj P = commonStageHomObject.{u, v} l Ω W P) ∧
      (∀ (P Q : (commonStageHomPairs.{u, v} l Ω W).FullSubcategory)
        (L : Index l Ω)
        (h : (StageSystem.PairCategory.stage.{v, u+2, u+2}
          (commonStageHomObject.{u, v} l Ω W P)) ≤ L)
        (h' : (StageSystem.PairCategory.stage.{v, u+2, u+2}
          (commonStageHomObject.{u, v} l Ω W Q)) ≤ L)
        (a : (commonStageHomPairAtStage.{u, v} l Ω W Q L h').obj.1.unop ⟶
          (commonStageHomPairAtStage.{u, v} l Ω W P L h).obj.1.unop)
        (b : (commonStageHomPairAtStage.{u, v} l Ω W P L h).obj.2 ⟶
          (commonStageHomPairAtStage.{u, v} l Ω W Q L h').obj.2),
        HEq (F.map (X := P) (Y := Q)
          (ObjectProperty.homMk (X := P) (Y := Q) (Prod.mkHom
            (StageSystem.PairCategory.mkHom.{v, u+2, u+2}
              (C := GeneralAlgebraicallyClosedCoefficients.Stage l Ω W)
              (S := stageSystem l Ω W) (X := Q.obj.1.unop) (Y := P.obj.1.unop) L
              (((Padic.finiteCoefficientFields_properties l Ω).1
                (StageSystem.PairCategory.stage.{v, u+2, u+2} Q.obj.1.unop)
                (StageSystem.PairCategory.stage.{v, u+2, u+2} Q.obj.2)).1.trans h')
              (((Padic.finiteCoefficientFields_properties l Ω).1
                (StageSystem.PairCategory.stage.{v, u+2, u+2} P.obj.1.unop)
                (StageSystem.PairCategory.stage.{v, u+2, u+2} P.obj.2)).1.trans h) a).op
            (StageSystem.PairCategory.mkHom.{v, u+2, u+2}
              (C := GeneralAlgebraicallyClosedCoefficients.Stage l Ω W)
              (S := stageSystem l Ω W) (X := P.obj.2) (Y := Q.obj.2) L
              (((Padic.finiteCoefficientFields_properties l Ω).1
                (StageSystem.PairCategory.stage.{v, u+2, u+2} P.obj.1.unop)
                (StageSystem.PairCategory.stage.{v, u+2, u+2} P.obj.2)).2.trans h)
              (((Padic.finiteCoefficientFields_properties l Ω).1
                (StageSystem.PairCategory.stage.{v, u+2, u+2} Q.obj.1.unop)
                (StageSystem.PairCategory.stage.{v, u+2, u+2} Q.obj.2)).2.trans h') b))))
          (StageSystem.PairCategory.mkHom.{v, u+2, u+2}
              (C := GeneralAlgebraicallyClosedCoefficients.Stage l Ω W)
              (S := stageSystem l Ω W)
              (X := commonStageHomObject.{u, v} l Ω W P)
              (Y := commonStageHomObject.{u, v} l Ω W Q) L h h'
            ((commonStageHomComparison.{u, v} l Ω W P L h).hom ≫
              (rationalDerivedInternalHom l (Coefficient.{u} l Ω L) W).map
                (X := commonStageHomPairAtStage.{u, v} l Ω W P L h)
                (Y := commonStageHomPairAtStage.{u, v} l Ω W Q L h')
                (ObjectProperty.homMk
                  (X := commonStageHomPairAtStage.{u, v} l Ω W P L h)
                  (Y := commonStageHomPairAtStage.{u, v} l Ω W Q L h')
                  (Prod.mkHom a.op b)) ≫
              (commonStageHomComparison.{u, v} l Ω W Q L h').inv)))
```

## Users

`tools/downstream.py Sheaf.Paper.DerivedPullbackTensorHom --uses
WeilConjectures.commonStageDerivedInternalHom_existsUnique` finds these five
modules. The other 1608 downstream modules do not mention this declaration.
The four external consumers only use its prescribed-object equality (`.1`) or
pass the entire existence-and-uniqueness specification to a generic extractor;
these uses are unaffected by unfolding the `ofHom` abbreviation. No consumer
adaptation is necessary. The target statements and the definition bodies they
use are preserved.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicAmbientHomEvaluationComparison | unclaimed | Same object equality; no adaptation. |
| Sheaf.Paper.AdmissibleHomSubstitution | unclaimed | Same object equality; no adaptation. |
| Sheaf.Paper.BasicOperationsCoefficientReduction | F7 | Same existence specification; no adaptation. |
| Sheaf.Paper.DerivedPullbackTensorHom | Z9 | Explicit parameters avoid expensive inference. |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | unclaimed | Same object equality; no adaptation. |

## Status

landed 20261024T204723-L-3823920 2026-10-24 (merge of deliver/Z9/Sheaf.Paper.DerivedPullbackTensorHom)
