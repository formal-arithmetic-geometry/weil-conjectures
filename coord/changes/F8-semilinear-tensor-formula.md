# AlgebraicGeometry.ProEtale.HasSpSemilinearKFlatTowerModel

## Reason

The original specialized pure-tensor clause spends approximately 45–49 seconds in
kernel checking the definition alone. Adding the actual proof exceeds the single-file
limit. The scalar-action expression forces repeated conversion through evaluated
complexes and restricted module structures. Factor exactly that sectionwise equation
into the data-only definition `SheafOfModules.systemTensorSectionFormula`, on generic
ring sheaves and modules. Its application retains the exact same `Qn`, `beta` and `q`.
The helper's scalar multiplication is definitionally the application of
`ModuleCat.smul` used in the original clause. The explicit `@id` in the original
expression only fixes the codomain and has no mathematical content.

A separate server-compiled probe proves equivalence with the old
`ModuleCat.smul ... (@id ... q(x))` expression by `rfl` (3.1 seconds).

No hypotheses, quantifiers, coefficients, transitions, localizations or conclusions
change. In particular equal indices, zero modules and nonflat coefficient maps retain
the same formula. The target theorem signature stays verbatim. Definitions used by
targets require the usual independent statement review again.

## Old

```lean
def HasSpSemilinearKFlatTowerModel (D : SpCoefficientTowersAbelian l E T)
    (C : @DerivedCategory (spCoefficientTowers l E T) _ _ D.hasDerived) : Prop :=
  letI : HasSheafify (Scheme.ProEt.topology T) AddCommGrpCat.{max u (t + 1)} :=
    surjectiveTower_hasSheafify.{t, u} T
  letI : (Scheme.ProEt.topology T).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} := surjectiveTower_wEqualsLocallyBijective.{t, u} T
  letI := D.hasDerived
  letI := D.equivalenceAdditive
  letI := D.evaluationLimits
  letI := D.evaluationColimits
  letI : ∀ n : ℕ, (spCoefficientEvaluation l E T D.equivalence n).Additive :=
    fun n ↦ Functor.additive_of_preserves_binary_products
      (spCoefficientEvaluation l E T D.equivalence n)
  letI : EssentiallySmall.{max u (t + 1)} T.ProEt := essentiallySmallSelf.{u} _
  let B := spCoefficientCommRings l E T
  let Ev := spCoefficientEvaluation l E T D.equivalence
  ∃ (P : CochainComplex (spCoefficientTowers l E T) ℤ)
    (a : DerivedCategory.Q.obj P ≅ C),
    let Qn := fun n : ℕ ↦ ((Ev n).mapHomologicalComplex (.up ℤ)).obj P
    let e := spSemilinearEvaluationIso l E T D C P a
    let beta := fun {m n : ℕ} (h : m ≤ n) ↦
      (NatTrans.mapHomologicalComplex (D.ordinaryReduction h) (.up ℤ)).app P
    let q := fun {m n : ℕ} (h : m ≤ n) ↦ spSemilinearChainTransition l E T D P h
    (∀ n : ℕ, systemLevelKFlat.{t + 1, t, max u (t + 1)} B n (Qn n)) ∧
    (∀ {m n : ℕ} (h : m ≤ n),
      DerivedCategory.Q.map (q h) ≫
          (systemRestriction B h).mapDerivedCategoryFactors.inv.app (Qn m) ≫
          (systemRestriction B h).mapDerivedCategory.map (e m).hom =
        (e n).hom ≫ ((systemDerivedTensorAdj D.scalar B h).homEquiv _ _)
          ((D.reduction h).app C)) ∧
    (∀ {m n : ℕ} (h : m ≤ n) (i : ℤ) (V : T.ProEtᵒᵖ)
      (c : (B.obj (op m)).obj.obj V) (x : ((Qn n).X i).val.obj V),
      ((beta h).f i).val.app V
          (systemModelTmul (D.scalar (B.map (homOfLE h).op)).model
            ((Qn n).X i) V c x) =
        (ModuleCat.smul (((Qn m).X i).val.obj V) c).hom
          (@id (((Qn m).X i).val.obj V) (((q h).f i).val.app V x))) ∧
    (∀ {m n : ℕ} (h : m ≤ n),
      IsIso ((D.scalar (B.map (homOfLE h).op)).model.ε.app (Qn n)) ∧
      (systemDerivedTensor D.scalar B h).map (e n).hom ≫ (D.reduction h).app C =
        (D.scalar (B.map (homOfLE h).op)).model.ε.app (Qn n) ≫
          DerivedCategory.Q.map (beta h) ≫ (e m).hom) ∧
    HasSpSemilinearCompletedLift l E T D C P a
```

## New

```lean
def HasSpSemilinearKFlatTowerModel (D : SpCoefficientTowersAbelian l E T)
    (C : @DerivedCategory (spCoefficientTowers l E T) _ _ D.hasDerived) : Prop :=
  letI : HasSheafify (Scheme.ProEt.topology T) AddCommGrpCat.{max u (t + 1)} :=
    surjectiveTower_hasSheafify.{t, u} T
  letI : (Scheme.ProEt.topology T).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} := surjectiveTower_wEqualsLocallyBijective.{t, u} T
  letI := D.hasDerived
  letI := D.equivalenceAdditive
  letI := D.evaluationLimits
  letI := D.evaluationColimits
  letI : ∀ n : ℕ, (spCoefficientEvaluation l E T D.equivalence n).Additive :=
    fun n ↦ Functor.additive_of_preserves_binary_products
      (spCoefficientEvaluation l E T D.equivalence n)
  letI : EssentiallySmall.{max u (t + 1)} T.ProEt := essentiallySmallSelf.{u} _
  let B := spCoefficientCommRings l E T
  let Ev := spCoefficientEvaluation l E T D.equivalence
  ∃ (P : CochainComplex (spCoefficientTowers l E T) ℤ)
    (a : DerivedCategory.Q.obj P ≅ C),
    let Qn := fun n : ℕ ↦ ((Ev n).mapHomologicalComplex (.up ℤ)).obj P
    let e := spSemilinearEvaluationIso l E T D C P a
    let beta := fun {m n : ℕ} (h : m ≤ n) ↦
      (NatTrans.mapHomologicalComplex (D.ordinaryReduction h) (.up ℤ)).app P
    let q := fun {m n : ℕ} (h : m ≤ n) ↦ spSemilinearChainTransition l E T D P h
    (∀ n : ℕ, systemLevelKFlat.{t + 1, t, max u (t + 1)} B n (Qn n)) ∧
    (∀ {m n : ℕ} (h : m ≤ n),
      DerivedCategory.Q.map (q h) ≫
          (systemRestriction B h).mapDerivedCategoryFactors.inv.app (Qn m) ≫
          (systemRestriction B h).mapDerivedCategory.map (e m).hom =
        (e n).hom ≫ ((systemDerivedTensorAdj D.scalar B h).homEquiv _ _)
          ((D.reduction h).app C)) ∧
    (∀ {m n : ℕ} (h : m ≤ n) (i : ℤ),
      systemTensorSectionFormula.{t + 1, t, max u (t + 1)}
        (J := Scheme.ProEt.topology T) (D.scalar (B.map (homOfLE h).op))
        ((Qn n).X i) ((Qn m).X i) ((beta h).f i) ((q h).f i)) ∧
    (∀ {m n : ℕ} (h : m ≤ n),
      IsIso ((D.scalar (B.map (homOfLE h).op)).model.ε.app (Qn n)) ∧
      (systemDerivedTensor D.scalar B h).map (e n).hom ≫ (D.reduction h).app C =
        (D.scalar (B.map (homOfLE h).op)).model.ε.app (Qn n) ≫
          DerivedCategory.Q.map (beta h) ≫ (e m).hom) ∧
    HasSpSemilinearCompletedLift l E T D C P a
```

The added generic definition is data-only, has no choice or proof dependency, and
is attached to the same model node. Its body is the universal sectionwise equality
`f(c tensor x) = c • q(x)`.

## Users

`tools/downstream.py Sheaf.Paper.SemilinearKFlatTowerModel --uses
AlgebraicGeometry.ProEtale.HasSpSemilinearKFlatTowerModel` reports zero downstream
modules and only the two occurrences in this item. A whole-library textual search
agrees. Parents in the mathematical DAG continue to need the same model node;
none is withdrawn or bypassed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.SemilinearKFlatTowerModel | F8 | Definition factored; theorem proved against it. |

## Status

landed 20261021T193238-L-1025363 2026-10-21 (merge of deliver/F8/Sheaf.Paper.SemilinearKFlatTowerModel)
