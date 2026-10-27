/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K5
-/
module

public import Sheaf.SecSmoothPurity.ReductionExceptionalObjects

/-! # Canonical chart equation for the exceptional coefficient transpose -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale

/-- The counit transpose of the fixed compact-support coefficient comparison has
its canonical ordered Tate reassociation on every smooth coordinate chart.
Source: blueprint latest, sec-smooth-purity, sk-lem-sp-reduction-exceptional.proof.md,
Steps 5--12 (blueprint: lem-sp-reduction-exceptional-chart).

Proof: comparison full faithfulness lifts the scalar comparison of input origins to
its unique natural etale origin isomorphism. For a common annihilator, use the finite
ring chart domain theorem and the sum/evaluation followed by affine-trace adjunction.
The chart scalar counit transport theorem identifies the inverse transpose of the
canonical ordered Tate reassociation with scalar extension of the chart counit
composed with the inverse specified compact-support comparison. The realization
counit equations transport this identity to the intrinsic categories. Open exceptional
scalar locality identifies the restriction of the given transpose with the chart
transpose. Injectivity of the chart adjunction Hom bijection gives the displayed
chart equation. All comparisons used here are the specified fixed-compactification
comparisons. This proof applies to arbitrary finite coefficient maps, including the
zero ring and the zero-dimensional chart. -/
theorem reductionExceptional_chartEquation
    (ℓ pchar : ℕ) [Fact ℓ.Prime] (hp : 0 < pchar) (hℓ : pchar ≠ ℓ)
    (k : Type u) [Field k] [CharP k pchar]
    {X Z Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] (d : ℕ) [SmoothOfRelativeDimension d f]
    (j : X ⟶ Z) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (p : Z ⟶ Y) [IsProper p] [p.IsOver (Spec (.of k))] (hf : j ≫ p = f)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0) (φ : A →+* B)
    (hFA : ∀ M : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor Y A ((reductionCompactSupport A j p).obj M.obj))
    (hFB : ∀ M : spFiniteConstructibleTorCategory X B,
      spFiniteConstructibleTor Y B ((reductionCompactSupport B j p).obj M.obj))
    (hSX : ∀ M : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor X B ((scalarExtensionFunctor φ X).obj M.obj))
    (hSY : ∀ K : spFiniteConstructibleTorCategory Y A,
      spFiniteConstructibleTor Y B ((scalarExtensionFunctor φ Y).obj K.obj))
    (GA : spFiniteConstructibleTorCategory Y A ⥤ spFiniteConstructibleTorCategory X A)
    (GB : spFiniteConstructibleTorCategory Y B ⥤ spFiniteConstructibleTorCategory X B)
    (adjA : reductionCtfCompactSupport A j p hFA ⊣ GA)
    (adjB : reductionCtfCompactSupport B j p hFB ⊣ GB)
    (RA : ReductionExceptionalRealization A j p hFA GA adjA)
    (RB : ReductionExceptionalRealization B j p hFB GB adjB)
    (c : GA ⋙ reductionCtfScalar φ X hSX ⟶ reductionCtfScalar φ Y hSY ⋙ GB)
    (hb : ∀ K : spFiniteConstructibleTorCategory Y A,
      IsIso ((reductionDirectImageComparison φ j p).app (GA.obj K).obj))
    (hc : ∀ K : spFiniteConstructibleTorCategory Y A,
      (reductionCompactSupport B j p).map (c.app K).hom ≫
          (adjB.counit.app ((reductionCtfScalar φ Y hSY).obj K)).hom =
        @inv _ _ _ _ ((reductionDirectImageComparison φ j p).app (GA.obj K).obj)
            (hb K) ≫
          (scalarExtensionFunctor φ Y).map (adjA.counit.app K).hom) :
    ReductionExceptionalChartEquation ℓ φ j p d hFA hFB hSX hSY GA GB adjA adjB RA RB c := by
  sorry

end AlgebraicGeometry.ProEtale
