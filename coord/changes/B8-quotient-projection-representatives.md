# SheafOfModules.QuotientDiagramProjection.TensorReduction

## Reason

Move the existing presentation interfaces to `Sheaf.Paper.QuotientDiagramProjectionData`
so that genuine constituent results can depend on them without importing the theorem
that combines those results. The original module publicly re-exports the data module.
The declarations retain their namespaces, universes, signatures and bodies except for
one additional proof-valued field of `TensorReduction`, shown below.

The existing exact tensor-evaluation model's `derived` equation requires flat terms as
well as K-flatness. `TensorReduction.kflat` supplied only K-flatness of ordinary reductions,
so it did not suffice to apply that equation to the specified representatives. Record
preservation of flat terms alongside it. This property holds for ordinary extension of
scalars: a flat R-module extends to a flat B-module, including nonflat quotient maps R→B.
The construction obligation must establish it; it is not a hypothesis added to the main
existence theorem. Thus the existential conclusion is strengthened rather than weakened.
All computation, unit, summand and representative normalizations remain.

The module is moved to break a logical import dependency, not to evade a compile limit.
The entire tensor normalization is proved in one module, and every compile uses the
project's unchanged limit. No source-library module is changed.

## Old

```lean
structure TensorReduction {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{max c v r}}
    {B : ℕ → Sheaf J CommRingCat.{max c v r}} {τ : ∀ n : ℕ, B (n + 1) ⟶ B n}
    {q : ∀ n : ℕ, R ⟶ B n} (s : Reduction.{c, v, r} J R B τ q) (a : SemilinearSections.Data.{c, v,
      r} J B τ) where
  ambient : SemilinearSections.Closed.{c, v, r} J R
  ambientModels : SemilinearSections.Models.{c, v, r} J R ambient
  balance : ambient.tensor ⋙ s.functor ≅ (s.functor.prod s.functor) ⋙ a.closed.tensor
  finiteBalance : ∀ n : ℕ,
    ambient.tensor ⋙ (s.levels n).T ≅
      ((s.levels n).T.prod (s.levels n).T) ⋙ (a.levelClosed n).tensor
  finiteModel : ∀ n : ℕ, SemilinearSections.ScalarTensorComparisonModel.{c, v, r} J R (B n) (q n)
    (s.levels n) ambient (a.levelClosed n) ambientModels (a.levelTensorModels n)
      (finiteBalance n)
  ordinary : ∀ M N : SemilinearSections.Mod.{c, v, max c v r} J R,
    s.ordinary.obj (SemilinearSections.ordinaryTensor.{c, v, r} J R M N) ≅
      SemilinearSections.ordinaryTensor.{c, v, r} (coefficientSequenceTopology J)
      (SemilinearSections.systemRing.{c, v, max c v r} J B τ)
        (s.ordinary.obj M) (s.ordinary.obj N)
  ordinary_evaluation : ∀ (n : ℕ) (M N : SemilinearSections.Mod.{c, v, max c v r} J R),
    (s.ordinaryEvaluation n).hom.app (SemilinearSections.ordinaryTensor.{c, v, r} J R M N) ≫
        ((finiteModel n).ordinary M N).hom =
      (SemilinearSections.evaluation.{c, v, max c v r} J B τ n).map (ordinary M N).hom ≫
        (SemilinearSections.ordinaryEvaluationTensor.{c, v, r} J B τ n (s.ordinary.obj M)
        (s.ordinary.obj N)).hom ≫
        SemilinearSections.ordinaryTensorHom.{c, v, r} J (B n) ((s.ordinaryEvaluation n).hom.app M)
          ((s.ordinaryEvaluation n).hom.app N)
  chain : ∀ P Q : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ,
    (SemilinearSections.totalTensor.{c, v, r} (coefficientSequenceTopology J)
      (SemilinearSections.systemRing.{c, v, max c v r} J B τ)).obj
        ((s.ordinary.mapHomologicalComplex (.up ℤ)).obj P,
          (s.ordinary.mapHomologicalComplex (.up ℤ)).obj Q) ⟶
      (s.ordinary.mapHomologicalComplex (.up ℤ)).obj ((SemilinearSections.totalTensor.{c, v, r} J
      R).obj (P, Q))
  summand : ∀ (P Q : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ) (i j k : ℤ)
      (h : i + j = k),
    SemilinearSections.tensorSummand.{c, v, r} (coefficientSequenceTopology J)
      (SemilinearSections.systemRing.{c, v, max c v r} J B τ)
        ((s.ordinary.mapHomologicalComplex (.up ℤ)).obj P)
        ((s.ordinary.mapHomologicalComplex (.up ℤ)).obj Q) i j k h ≫ (chain P Q).f k =
      (ordinary (P.X i) (Q.X j)).inv ≫ s.ordinary.map (SemilinearSections.tensorSummand.{c, v, r}
      J R P Q i j k h)
  kflat : ∀ P : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (R := R) P → SemilinearSections.flatTerms.{c, v,
      r} J R P →
    CochainComplex.IsKFlatIndependentCoefficients (R := SemilinearSections.systemRing.{c, v, max c
      v r} J B τ)
      ((s.ordinary.mapHomologicalComplex (.up ℤ)).obj P)
  representative : ∀ (P Q : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients (R := R) Q)
    (fP : SemilinearSections.flatTerms.{c, v, r} J R P) (fQ : SemilinearSections.flatTerms.{c, v,
      r} J R Q)
    (_hPQ : CochainComplex.IsKFlatIndependentCoefficients (R := R)
      ((SemilinearSections.totalTensor.{c, v, r} J R).obj (P, Q))),
    (SemilinearSections.tensorModelIso.{c, v, r} (coefficientSequenceTopology J)
      (SemilinearSections.systemRing.{c, v, max c v r} J B τ)
      a.closed a.tensorModels ((s.ordinary.mapHomologicalComplex (.up ℤ)).obj P)
        ((s.ordinary.mapHomologicalComplex (.up ℤ)).obj Q)
        (kflat P hP fP) (kflat Q hQ fQ)).hom ≫
      a.closed.tensor.map (Prod.mkHom
        (@asIso _ _ _ _ (s.epsilon.app P) (s.computes P hP)).inv
        (@asIso _ _ _ _ (s.epsilon.app Q) (s.computes Q hQ)).inv) ≫
      balance.inv.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      s.functor.map (SemilinearSections.tensorModelIso.{c, v, r} J R ambient ambientModels P Q hP
      hQ).inv ≫
      s.epsilon.app ((SemilinearSections.totalTensor.{c, v, r} J R).obj (P, Q)) =
      DerivedCategory.Q.map (chain P Q)
```

## New

```lean
structure TensorReduction {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{max c v r}}
    {B : ℕ → Sheaf J CommRingCat.{max c v r}} {τ : ∀ n : ℕ, B (n + 1) ⟶ B n}
    {q : ∀ n : ℕ, R ⟶ B n} (s : Reduction.{c, v, r} J R B τ q) (a : SemilinearSections.Data.{c, v,
      r} J B τ) where
  ambient : SemilinearSections.Closed.{c, v, r} J R
  ambientModels : SemilinearSections.Models.{c, v, r} J R ambient
  balance : ambient.tensor ⋙ s.functor ≅ (s.functor.prod s.functor) ⋙ a.closed.tensor
  finiteBalance : ∀ n : ℕ,
    ambient.tensor ⋙ (s.levels n).T ≅
      ((s.levels n).T.prod (s.levels n).T) ⋙ (a.levelClosed n).tensor
  finiteModel : ∀ n : ℕ, SemilinearSections.ScalarTensorComparisonModel.{c, v, r} J R (B n) (q n)
    (s.levels n) ambient (a.levelClosed n) ambientModels (a.levelTensorModels n)
      (finiteBalance n)
  ordinary : ∀ M N : SemilinearSections.Mod.{c, v, max c v r} J R,
    s.ordinary.obj (SemilinearSections.ordinaryTensor.{c, v, r} J R M N) ≅
      SemilinearSections.ordinaryTensor.{c, v, r} (coefficientSequenceTopology J)
      (SemilinearSections.systemRing.{c, v, max c v r} J B τ)
        (s.ordinary.obj M) (s.ordinary.obj N)
  ordinary_evaluation : ∀ (n : ℕ) (M N : SemilinearSections.Mod.{c, v, max c v r} J R),
    (s.ordinaryEvaluation n).hom.app (SemilinearSections.ordinaryTensor.{c, v, r} J R M N) ≫
        ((finiteModel n).ordinary M N).hom =
      (SemilinearSections.evaluation.{c, v, max c v r} J B τ n).map (ordinary M N).hom ≫
        (SemilinearSections.ordinaryEvaluationTensor.{c, v, r} J B τ n (s.ordinary.obj M)
        (s.ordinary.obj N)).hom ≫
        SemilinearSections.ordinaryTensorHom.{c, v, r} J (B n) ((s.ordinaryEvaluation n).hom.app M)
          ((s.ordinaryEvaluation n).hom.app N)
  chain : ∀ P Q : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ,
    (SemilinearSections.totalTensor.{c, v, r} (coefficientSequenceTopology J)
      (SemilinearSections.systemRing.{c, v, max c v r} J B τ)).obj
        ((s.ordinary.mapHomologicalComplex (.up ℤ)).obj P,
          (s.ordinary.mapHomologicalComplex (.up ℤ)).obj Q) ⟶
      (s.ordinary.mapHomologicalComplex (.up ℤ)).obj ((SemilinearSections.totalTensor.{c, v, r} J
      R).obj (P, Q))
  summand : ∀ (P Q : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ) (i j k : ℤ)
      (h : i + j = k),
    SemilinearSections.tensorSummand.{c, v, r} (coefficientSequenceTopology J)
      (SemilinearSections.systemRing.{c, v, max c v r} J B τ)
        ((s.ordinary.mapHomologicalComplex (.up ℤ)).obj P)
        ((s.ordinary.mapHomologicalComplex (.up ℤ)).obj Q) i j k h ≫ (chain P Q).f k =
      (ordinary (P.X i) (Q.X j)).inv ≫ s.ordinary.map (SemilinearSections.tensorSummand.{c, v, r}
      J R P Q i j k h)
  kflat : ∀ P : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (R := R) P → SemilinearSections.flatTerms.{c, v,
      r} J R P →
    CochainComplex.IsKFlatIndependentCoefficients (R := SemilinearSections.systemRing.{c, v, max c
      v r} J B τ)
      ((s.ordinary.mapHomologicalComplex (.up ℤ)).obj P)
  flatTerms : ∀ P : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ,
    SemilinearSections.flatTerms.{c, v, r} J R P →
    SemilinearSections.flatTerms.{c, v, r} (coefficientSequenceTopology J)
      (SemilinearSections.systemRing.{c, v, max c v r} J B τ)
      ((s.ordinary.mapHomologicalComplex (.up ℤ)).obj P)
  representative : ∀ (P Q : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients (R := R) Q)
    (fP : SemilinearSections.flatTerms.{c, v, r} J R P) (fQ : SemilinearSections.flatTerms.{c, v,
      r} J R Q)
    (_hPQ : CochainComplex.IsKFlatIndependentCoefficients (R := R)
      ((SemilinearSections.totalTensor.{c, v, r} J R).obj (P, Q))),
    (SemilinearSections.tensorModelIso.{c, v, r} (coefficientSequenceTopology J)
      (SemilinearSections.systemRing.{c, v, max c v r} J B τ)
      a.closed a.tensorModels ((s.ordinary.mapHomologicalComplex (.up ℤ)).obj P)
        ((s.ordinary.mapHomologicalComplex (.up ℤ)).obj Q)
        (kflat P hP fP) (kflat Q hQ fQ)).hom ≫
      a.closed.tensor.map (Prod.mkHom
        (@asIso _ _ _ _ (s.epsilon.app P) (s.computes P hP)).inv
        (@asIso _ _ _ _ (s.epsilon.app Q) (s.computes Q hQ)).inv) ≫
      balance.inv.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      s.functor.map (SemilinearSections.tensorModelIso.{c, v, r} J R ambient ambientModels P Q hP
      hQ).inv ≫
      s.epsilon.app ((SemilinearSections.totalTensor.{c, v, r} J R).obj (P, Q)) =
      DerivedCategory.Q.map (chain P Q)
```

## Users

`tools/downstream.py Sheaf.Paper.QuotientDiagramProjectionEvaluation --uses TensorReduction`
reports zero downstream modules and only the item itself as a declaration user. Source
search also finds no other Lean consumer of these namespace declarations. The new data
module is publicly re-exported by the original module, preserving its public interface.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.QuotientDiagramProjectionEvaluation | B8 | Re-exports the data; proves the laws from construction and tensor normalization. |
| Sheaf.Paper.QuotientDiagramProjectionData | new, B8 | Owns the existing data, with the additional flat-term proof field. |
| Sheaf.Paper.QuotientReductionTensorEvaluation | new, B8 | Uses the field to apply the existing tensor representative equation. |
| Sheaf.Paper.QuotientDiagramProjectionConstruction | new, B8 | Existence now also includes this true flatness property. |

No `Challenge.lean` declaration is edited. There are currently no Lean importers of the
item, hence no existing target statement changes through a Lean dependency. The new field
and the relocation should be included when the maintainer reviews the target definitions
that will use this presentation. The original DAG statement and its statement dependencies are preserved. The new
construction and tensor nodes cite the definition node owning the moved interfaces.

The DAG citers `lem-pur-perfect-quotient-exchange-normalization` and
`lem-pur-compact-support-completed-projection-coherence` still hold: both use the same
existence conclusion and projection laws, now with an extra true proof property in the
presentation. No hypothesis or projection conclusion is removed.

## Status

landed 20261024T184625-L-3081691 2026-10-24 (merge of deliver/B8/Sheaf.Paper.QuotientDiagramProjectionEvaluation)
