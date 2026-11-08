/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.Algebra.Homology.Coefficient.CoefficientEvaluationOrdinaryCoherence
public import Submission.WeilConjectures.Algebra.Homology.Coefficient.CoefficientEvaluationDerivedCore
public import Submission.WeilConjectures.Algebra.Homology.Coefficient.CoefficientScalarDerivedAdjunction
public import Submission.WeilConjectures.CategoryTheory.Adjunction.SmoothPurity.CompositeMate
import Submission.WeilConjectures.CategoryTheory.Normalized.NormalizedAdjunctionComposition

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Derived extension and coherence relative to a strict evaluation adjunction

Source: Zheng, Construction 4.1, p. 21; Stacks Project, Tags 06XN, 0FND and 09T5.
(blueprint: lem-pur-coefficient-evaluation-derived-extension-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w d
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [HasWeakSheafify J CommRingCat.{w}] [EssentiallySmall.{w} C]
  {O : Type w} [CommRing O] {ell : O}
  [∀ n : ℕ, HasDerivedCategory.{d} (coefficientLevelModules (J := J) O ell n)]
  [HasDerivedCategory.{d} (CoefficientSystem (J := J) O ell)]

local notation "ev" => coefficientEvaluation (J := J) (O := O) (ell := ell)
local notation "tensor" => coefficientTensor (J := J) (O := O) (ell := ell)
local notation "tensorAdj" => coefficientTensorAdj (J := J) (O := O) (ell := ell)

/-- The truncation map is constructed as the mate of the derived system transition.
Source: Zheng, Construction 4.1, p. 21
(blueprint: lem-pur-coefficient-evaluation-derived-extension-coherence). -/
def coefficientEvaluationSigma
    {ordinary : CoefficientOrdinaryEvaluationData (J := J) (O := O) (ell := ell)}
    [∀ n, (ordinary.extension n).Additive]
    (scalar : CoefficientScalarDerivedAssignment (J := J) (O := O) (ell := ell))
    (core : CoefficientEvaluationDerivedCoreData ordinary)
    (transition : ∀ {m n : ℕ} (h : n ≤ m),
      core.evaluation m ⟶ core.evaluation n ⋙ (scalar h).restriction)
    {m n : ℕ} (h : n ≤ m) : (scalar h).derived ⋙ core.derivedExtension n ⟶
      core.derivedExtension m :=
  CategoryTheory.Adjunction.compositeMate
    (core.derivedAdj n) (core.derivedAdj m) (scalar h).derivedAdj (transition h)

attribute [local irreducible] coefficientEvaluationSigma

/-- Index coherence for fixed strict, scalar-derived and evaluation-derived adjunctions.
All adjunctions, their universal comparisons and their normalized representative
transposes have already been constructed.
Source: Zheng, Construction 4.1, p. 21; Stacks 06XN and 09T5
(blueprint: lem-pur-coefficient-evaluation-derived-extension-coherence). -/
structure CoefficientEvaluationDerivedCoherenceData
    (ordinary : CoefficientOrdinaryEvaluationData (J := J) (O := O) (ell := ell))
    [∀ n, (ordinary.extension n).Additive]
    (scalar : CoefficientScalarDerivedAssignment (J := J) (O := O) (ell := ell))
    (core : CoefficientEvaluationDerivedCoreData ordinary)
    (transition : ∀ {m n : ℕ} (h : n ≤ m),
      core.evaluation m ⟶ core.evaluation n ⋙ (scalar h).restriction)
    (strict : CoefficientEvaluationOrdinaryCoherenceData ordinary)
    (unit : ∀ n, (scalar (Nat.le_refl n)).derived ≅ 𝟭 _) where
  sigma_rep : ∀ {m n} (h : n ≤ m) P,
    (CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientQuotientSheaf (J := J) O ell m)) P →
    (∀ i, (IsFlatOnSite (R := coefficientQuotientSheaf (J := J) O ell m)) (P.X i)) →
    (coefficientEvaluationSigma scalar core transition h).app (DerivedCategory.Q.obj P) ≫
      (core.counit m).app P =
      (core.derivedExtension n).map ((scalar h).counit.app P) ≫
        (core.counit n).app (((tensor h).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
        DerivedCategory.Q.map (strict.strictSigmaComplex h P)
  derivedAssoc : ∀ {l m n} (h₁ : m ≤ l) (h₂ : n ≤ m),
    (scalar h₁).derived ⋙ (scalar h₂).derived ≅ (scalar (h₂.trans h₁)).derived
  derivedAssoc_rep : ∀ {l m n} (h₁ : m ≤ l) (h₂ : n ≤ m) P,
    (CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientQuotientSheaf (J := J) O ell l)) P →
    (∀ i, (IsFlatOnSite (R := coefficientQuotientSheaf (J := J) O ell l)) (P.X i)) →
    (derivedAssoc h₁ h₂).hom.app (DerivedCategory.Q.obj P) ≫
      (scalar (h₂.trans h₁)).counit.app P =
    (scalar h₂).derived.map ((scalar h₁).counit.app P) ≫
      (scalar h₂).counit.app
        (((tensor h₁).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) ≫
      DerivedCategory.Q.map (strict.tensorAssocComplex h₁ h₂ P).hom
  sigma_id : ∀ n N, (coefficientEvaluationSigma scalar core transition (Nat.le_refl n)).app N =
    (core.derivedExtension n).map ((unit n).hom.app N)
  sigma_comp : ∀ {l m n} (h₁ : m ≤ l) (h₂ : n ≤ m) N,
    (coefficientEvaluationSigma scalar core transition h₂).app ((scalar h₁).derived.obj N) ≫
      (coefficientEvaluationSigma scalar core transition h₁).app N =
      (core.derivedExtension n).map ((derivedAssoc h₁ h₂).hom.app N) ≫
        (coefficientEvaluationSigma scalar core transition (h₂.trans h₁)).app N

end SheafOfModules
