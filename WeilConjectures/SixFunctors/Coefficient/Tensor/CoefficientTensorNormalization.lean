/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Coefficient.FiniteCoefficientHomChange
public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisons
import WeilConjectures.SixFunctors.Coefficient.Tensor.CoefficientTensorNormalizationUnit
import WeilConjectures.SixFunctors.Coefficient.Tensor.CoefficientTensorNormalizationTower
import WeilConjectures.SixFunctors.Coefficient.Tensor.CoefficientTensorNormalizationQuotient
import WeilConjectures.SixFunctors.Coefficient.Tensor.CoefficientTensorNormalizationFinite
import WeilConjectures.SixFunctors.Coefficient.Tensor.CoefficientTensorNormalizationScalar

/-! # Normalization of the canonical coefficient tensor comparisons

Source: current blueprint, sec-six-functors/sk-thm-sf-compatibility,
fix-prop-coherence.proof.md, tensor reassociation and evaluation sentence.
(blueprint: lem-sf-coefficient-tensor-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedVariables false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

/-- The specified tensorators respect the actual restriction-adjoint mates and associators.
This assertion involves only tensor products, not internal-Hom comparisons.

Source: current blueprint fix-prop-coherence.proof.md, tensor reassociation sentence;
lem-sf-general-hom-comparison-cocycles, proof steps 1--3 and 6; Stacks 07A4, 0D6D.
(blueprint: lem-sf-coefficient-tensor-normalization).

Proof:
1. Represent every input by a flat-term K-flat complex. The fixed tensor models and
finite scalar counits compute tensor and scalar change on these representatives.
The normalized ordinary scalar unit sends x to 1 tensor x, so the mate of identity
restriction sends x tensor b to bx. Its tensor equation is the first displayed law.
2. For integral reduction followed by quotient reduction, both scalar association
maps send (x tensor b) tensor c to x tensor bc. The normalized derived adjunctions
identify this association with leftAdjointCompIso for normalizedDVRResCompletedComp.
The pure-tensor normalizations of finiteTensor and quotientCalculus.tensor give the
second square, including its prescribed mate rather than an arbitrary associator.
3. On three tensor factors, both routes multiply the same coefficients and retain
x tensor (y tensor z); totalization's associator preserves the signed differential.
This proves the last three squares for quotient, integral-to-finite and ordinary
finite-field scalar change. In the last case use scalarClosedTensor's defining
representative square. No flatness of a quotient ring map is used.
4. Tensor, coefficient change, units and mates are natural on resolutions. Their
universal localization comparisons are invertible on the chosen K-flat objects.
Cancel them to descend all five equations to arbitrary ambient derived inputs.
The identity, first positive exponent, zero inputs and zero ranks are included. -/
theorem coefficientTensor_normalization
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p) :
    (∀ n : ℕ,
      let S := finiteIntrinsicClosed l E X n
      let F := coefficientFiniteQuotientDerived l E X (Nat.le_refl n)
      let μ := (coefficientDerivedSystemEvaluationCalculus l E X).choose.quotientCalculus.tensor
        (Nat.le_refl n)
      let e := Adjunction.leftAdjointIdIso
        ((coefficientDerivedSystemEvaluationCalculus l E X).choose.quotientCalculus.adjunction
          (Nat.le_refl n)) (normalizedDVRResUnit l E X n)
      ∀ K M : normalizedDVRDerived l E X n,
        S.tensor.map (Prod.mkHom (e.inv.app K) (e.inv.app M)) =
          e.inv.app (S.tensor.obj (K, M)) ≫ μ.hom.app (K, M)) ∧
    (∀ (n m : ℕ) (h : m ≤ n),
      let SA := scalarIntegralClosed l E X
      let SB := finiteIntrinsicClosed l E X n
      let SC := finiteIntrinsicClosed l E X m
      let F := coefficientFiniteDerivedExtension l E X n
      let G := coefficientFiniteQuotientDerived l E X h
      let μ := (coefficientDerivedSystemEvaluationCalculus l E X).choose.finiteTensor n
      let ν := (coefficientDerivedSystemEvaluationCalculus l E X).choose.quotientCalculus.tensor h
      let ξ := (coefficientDerivedSystemEvaluationCalculus l E X).choose.finiteTensor m
      let α := Adjunction.leftAdjointCompIso (coefficientFiniteAdjunction l E X n)
        ((coefficientDerivedSystemEvaluationCalculus l E X).choose.quotientCalculus.adjunction h)
        (coefficientFiniteAdjunction l E X m) (normalizedDVRResCompletedComp l E X D hl h)
      ∀ K M : DerivedCategory (scalarReductionSource l E X),
        G.map (μ.hom.app (K, M)) ≫ ν.hom.app (F.obj K, F.obj M) ≫
            SC.tensor.map (Prod.mkHom (α.hom.app K) (α.hom.app M)) =
          α.hom.app (SA.tensor.obj (K, M)) ≫ ξ.hom.app (K, M)) ∧
    (∀ (n m : ℕ) (h : m ≤ n),
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
        SB.tensor.map (Prod.mkHom (𝟙 (F.obj K)) (μ.hom.app (M, N)))) ∧
    (∀ n : ℕ,
      let SA := scalarIntegralClosed l E X
      let SB := finiteIntrinsicClosed l E X n
      let F := coefficientFiniteDerivedExtension l E X n
      let μ := (coefficientDerivedSystemEvaluationCalculus l E X).choose.finiteTensor n
      ∀ K M N : DerivedCategory (scalarReductionSource l E X),
    μ.hom.app (SA.tensor.obj (K, M), N) ≫
        SB.tensor.map (Prod.mkHom (μ.hom.app (K, M)) (𝟙 (F.obj N))) ≫
        (SB.monoidal.associator (F.obj K) (F.obj M) (F.obj N)).hom =
      F.map (SA.monoidal.associator K M N).hom ≫
        μ.hom.app (K, SA.tensor.obj (M, N)) ≫
        SB.tensor.map (Prod.mkHom (𝟙 (F.obj K)) (μ.hom.app (M, N)))) ∧
    ∀ (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
      (ι : E →ₐ[Padic l] L),
      let SA := scalarIntegralClosed l E X
      let SB := scalarIntegralClosed l L X
      let F := integralOrdinaryDerivedScalar l E L ι X
      let μ := scalarClosedTensor l E L ι X
      ∀ K M N : DerivedCategory (scalarReductionSource l E X),
    μ.hom.app (SA.tensor.obj (K, M), N) ≫
        SB.tensor.map (Prod.mkHom (μ.hom.app (K, M)) (𝟙 (F.obj N))) ≫
        (SB.monoidal.associator (F.obj K) (F.obj M) (F.obj N)).hom =
      F.map (SA.monoidal.associator K M N).hom ≫
        μ.hom.app (K, SA.tensor.obj (M, N)) ≫
        SB.tensor.map (Prod.mkHom (𝟙 (F.obj K)) (μ.hom.app (M, N))) := by
  refine ⟨coefficientTensor_normalization_unit l E X D hl,
    coefficientTensor_normalization_tower l E X D hl,
    coefficientTensor_normalization_quotient l E X D hl,
    coefficientTensor_normalization_finite l E X D hl,
    coefficientTensor_normalization_scalar l E X D hl⟩

end WeilConjectures
