/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Coefficient.FiniteCoefficientHomChange
import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomNormalizedQuotientFunctorLaws

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option linter.unusedVariables false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

/-- Quotient tensor associativity normalization, the third component of the coherence.
Source: current blueprint, sec-six-functors/sk-thm-sf-compatibility, fix-prop-coherence.proof.md.
The quotient tensorator is normalized on pure triples and hence respects the derived associator.
(blueprint: lem-sf-coefficient-tensor-normalization-quotient). -/
theorem coefficientTensor_normalization_quotient
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p) :
    ∀ (n m : ℕ) (h : m ≤ n),
      let SA := finiteIntrinsicClosed l E X n
      let SB := finiteIntrinsicClosed l E X m
      let F := coefficientFiniteQuotientDerived l E X h
      let μ := (coefficientDerivedSystemEvaluationCalculus l E X).choose.quotientCalculus.tensor h
      ∀ K M N : normalizedDVRDerived l E X n,
    μ.hom.app (SA.tensor.obj (K, M), N) ≫
        SB.tensor.map (Prod.mkHom (μ.hom.app (K, M)) (𝟙 (F.obj N))) ≫
        (SB.monoidal.associator (F.obj K) (F.obj M) (F.obj N)).hom =
      F.map (SA.monoidal.associator K M N).hom ≫
        μ.hom.app (K, SA.tensor.obj (M, N)) ≫
        SB.tensor.map (Prod.mkHom (𝟙 (F.obj K)) (μ.hom.app (M, N))) := by
  classical
  let S := (coefficientDerivedSystemEvaluationCalculus l E X).choose
  have hc (j : ℕ) :
      ∃ β : @SymmetricCategory (normalizedDVRDerived l E X j) _
          (finiteIntrinsicClosed l E X j).monoidal,
        Nonempty (RingedDerivedTensorCoherence (ProEt.topology X)
          (integralCoefficientCommRingSheaf l E X j) (finiteIntrinsicClosed l E X j)
          (finiteIntrinsicTensorModels l E X j) β) := by
    exact S.finite_tensor_coherence j
  choose β hβ using hc
  intro n m h
  dsimp only
  intro K M N
  obtain ⟨⟨s, hsμ⟩, _⟩ :=
    finiteHomNormalizedQuotientFunctorLaws l E X β hβ n m h
  let := (finiteIntrinsicClosed l E X n).monoidal
  let := (finiteIntrinsicClosed l E X m).monoidal
  have hi (P Q : normalizedDVRDerived l E X n) :
      (s.μIso P Q).inv = (S.quotientCalculus.tensor h).hom.app (P, Q) := by
    exact congrArg Iso.inv (hsμ P Q)
  have ha := s.toOplaxMonoidal.oplax_associativity K M N
  dsimp [S] at hi ha ⊢
  simp only [CoefficientClosedStructure.tensor, MonoidalCategory.tensor_obj,
    MonoidalCategory.tensor_map]
  erw [MonoidalCategory.id_tensorHom, MonoidalCategory.tensorHom_id]
  simp only [Functor.CoreMonoidal.toOplaxMonoidal_δ, hi] at ha
  change
    (S.quotientCalculus.tensor h).hom.app
        ((finiteIntrinsicClosed l E X n).tensor.obj (K, M), N) ≫
        MonoidalCategoryStruct.whiskerRight
          ((S.quotientCalculus.tensor h).hom.app (K, M))
          ((coefficientFiniteQuotientDerived l E X h).obj N) ≫
        ((finiteIntrinsicClosed l E X m).monoidal.associator
          ((coefficientFiniteQuotientDerived l E X h).obj K)
          ((coefficientFiniteQuotientDerived l E X h).obj M)
          ((coefficientFiniteQuotientDerived l E X h).obj N)).hom =
      (coefficientFiniteQuotientDerived l E X h).map
          ((finiteIntrinsicClosed l E X n).monoidal.associator K M N).hom ≫
        (S.quotientCalculus.tensor h).hom.app
          (K, (finiteIntrinsicClosed l E X n).tensor.obj (M, N)) ≫
        MonoidalCategoryStruct.whiskerLeft
          ((coefficientFiniteQuotientDerived l E X h).obj K)
          ((S.quotientCalculus.tensor h).hom.app (M, N))
  exact ha

end WeilConjectures
