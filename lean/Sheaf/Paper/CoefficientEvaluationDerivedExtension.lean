/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R6
-/
module

public import Sheaf.Paper.CoefficientEvaluationOrdinaryCoherence
public import Sheaf.Paper.CoefficientEvaluationDerivedCore
public import Sheaf.Paper.CoefficientScalarDerivedAdjunction
public import Sheaf.CategoryTheory.Adjunction.CompositeMate

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

/-- Derived compatibility of the strict truncation inclusions, with identity and
composition laws for their adjunction mates.
Source: Zheng, Construction 4.1, p. 21; Stacks Tags 06XN, 0FND and 09T5
(blueprint: lem-pur-coefficient-evaluation-derived-extension-coherence).
Proof: scalar extension takes flat-term K-flat complexes to flat-term K-flat complexes.
For such a complex P, transpose the proposed sigma representative equation first under
the normalized evaluation adjunction and then under the normalized scalar adjunction.
Their representative formulas and the transition's localization equation reduce both
sides to the ordinary extension Hom formula and the strict truncation's transpose.
Injectivity of the two Hom bijections proves the sigma comparison.
On a flat-term K-flat P define the derived associator by the composite of the second
derived tensor applied to the first counit, the second counit at the first tensor of P,
the localization of the ordinary associator, and the inverse direct tensor counit.
All these maps are isomorphisms: the first and direct counits compute on P, and the
second computes because scalar extension preserves the resolving class. Naturality of
these counits and of the ordinary associator gives naturality on resolving complexes.
Pass to their homotopy classes. Every homotopy object admits a resolving complex, and
the calculus of quasi-isomorphism fractions gives common resolving refinements. Thus
the same formula is independent of the chosen resolution and descends naturally to
the derived categories. The inverse formula, using the inverse ordinary associator,
gives its inverse. Its defining equation is exactly derivedAssoc_rep. Any other
comparison with that equation agrees after canceling the invertible direct counit on
each resolving complex, hence agrees on every derived object.
For the identity index, the ordinary tensor unit normalization and strict Hom formula
identify the strict truncation with extension applied to the ordinary tensor unit.
For three indices, evaluate the two successive strict truncations at q. Below the
smallest index, transpose by the three scalar Hom bijections. Tensor unit normalization
reduces both values to the same product of scalar factors; above it the source is zero.
The faithful component evaluations therefore give the strict composition identity.
Apply the sigma representative comparison to these ordinary identities and insert the
derived unit and associator comparison equations. On a flat-term K-flat resolution all
universal counits in these equations are invertible, including those after a scalar
extension, so cancellation gives sigma_id and sigma_comp on its localized object.
Every derived object is isomorphic to one of these objects. Naturality along that
isomorphism proves both laws on every derived object. No flatness of quotient maps is
assumed. -/
theorem coefficientEvaluationDerivedCoherence
    (ordinary : CoefficientOrdinaryEvaluationData (J := J) (O := O) (ell := ell))
    [∀ n, (ordinary.extension n).Additive]
    (scalar : CoefficientScalarDerivedAssignment (J := J) (O := O) (ell := ell))
    (core : CoefficientEvaluationDerivedCoreData ordinary)
    (transition : ∀ {m n : ℕ} (h : n ≤ m),
      core.evaluation m ⟶ core.evaluation n ⋙ (scalar h).restriction)
    (strict : CoefficientEvaluationOrdinaryCoherenceData ordinary)
    (unit : ∀ n, (scalar (Nat.le_refl n)).derived ≅ 𝟭 _)
    (unit_rep : ∀ n P,
      (unit n).hom.app (DerivedCategory.Q.obj P) =
        (scalar (Nat.le_refl n)).counit.app P ≫
          DerivedCategory.Q.map (strict.tensorUnitComplex n P).hom)
    (transition_rep : ∀ {m n} (h : n ≤ m) K,
    (transition h).app (DerivedCategory.Q.obj K) ≫
      (scalar h).restriction.map ((core.evaluationFactors n).hom.app K) ≫
      (scalar h).restrictionFactors.hom.app
        (((ev n).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) =
      (core.evaluationFactors m).hom.app K ≫
        DerivedCategory.Q.map
          (((ordinary.strictTransition h).mapHomologicalComplex (ComplexShape.up ℤ)).app K)) :
    Nonempty
      (CoefficientEvaluationDerivedCoherenceData ordinary scalar core transition strict unit) := by
  sorry

end SheafOfModules
