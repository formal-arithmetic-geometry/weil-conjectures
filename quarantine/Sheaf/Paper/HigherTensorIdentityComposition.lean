/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T7
-/
module

public import Sheaf.Paper.CommonProjectionPullbackTensorCompatibility
public import Sheaf.Paper.ConstructibleProjectionMates

/-! # Composition of the higher tensor comparisons at identity

Source: composition clause of lem-pur-derived-pullback-tensor-iso, transported
through the recorded operation normalizations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.GeneralAlgebraicallyClosedCoefficients
namespace WeilConjectures

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}

/-- The twice-identity composition squares for the three higher tensor comparisons,
expressed in the supplied operation coordinates. These equations involve the
compositor and two tensor comparisons; they assert no compatibility of an
identity unit with tensor.

Source: composition clause of lem-pur-derived-pullback-tensor-iso; identity
paragraph of prop-sf-pf-coherence.proof.md.
(blueprint: lem-sf-higher-tensor-identity-composition).

Proof: the prime-to-characteristic coefficient convention makes the coefficient
prime invertible on X. In the integral square use integralPullback and
integralTensorNormalization
to identify functors, and integralTensorPullbackNormalization to identify the
comparison. Expand projectionTransportTensorComparison by substitution of the
recorded functor equalities; the HEq normalization then compares arrows with
these same endpoints, including their equality transports. The reduction
comparison of integralNormalization is the prescribed
projection-adjoint map by pullProjection. Its pullComposition equation, together
with finitePullCompositionNormalization, therefore identifies the supplied
compositor with the canonical completed pullback compositor after every coherent
finite reduction. The coherent reduction functor on complete constructible
objects is faithful. Hence the canonical integral tensor/composition equation
from derivedPullbackTensorIso gives the displayed equation. This calculation is
on whole coherent quotient systems and retains the completion counit, rather
than inferring equality merely from separate reductions. For the rational
square apply rationalization.pullComposition and its fixed object and morphism
normalizations: localization carries the integral compositor and tensor square
to the rational one. For the common-stage square choose one coefficient field
containing both objects and the two composites. The pullComposition equation of
commonStageComparison identifies the common compositor with the rational one,
and commonProjectionPullbackTensorCompatibility identifies the tensor/pullback
comparisons. Apply ofHom at that field to the rational square; transition
naturality makes this independent of the field. In all three squares cancel the
displayed equality transports for identity composition. No identity unit or
projection counit is used. Zero objects and empty schemes require no exception. -/
theorem higherTensor_identityComposition (S : SixFunctorOperationDatum D C E n hn) :
    (∀ X : SixFunctorSpace D,
      letI : IsProper (𝟙 X : X ⟶ X).hom.left := by
        change IsProper (𝟙 X.obj.left)
        infer_instance
      let U := S.higher.integral.pull (𝟙 X)
      let T := Functor.uncurry.obj (S.higher.integralTensor X)
      let μ := fun M L ↦
        ((projectionPullbackTensor (S.higher.integralExchange
          (compactSupportProperSquare (𝟙 X : X ⟶ X)))).hom.app M).app L
      let c : ∀ M, U.obj M ≅ U.obj (U.obj M) := fun M ↦
        eqToIso (congrArg (fun f ↦ (S.higher.integral.pull f).obj M)
          (Category.id_comp (𝟙 X)).symm) ≪≫
          (S.higher.integral.pullComposition (𝟙 X) (𝟙 X)).app M
      ∀ M L, μ M L ≫ T.map (Prod.mkHom (c M).hom (c L).hom) =
        (c (T.obj (M, L))).hom ≫ U.map (μ M L) ≫ μ (U.obj M) (U.obj L)) ∧
    (∀ X : SixFunctorSpace D,
      letI : IsProper (𝟙 X : X ⟶ X).hom.left := by
        change IsProper (𝟙 X.obj.left)
        infer_instance
      let U := S.higher.rational.pull (𝟙 X)
      let T := Functor.uncurry.obj (S.higher.rationalTensor X)
      let μ := fun M L ↦
        ((projectionPullbackTensor (S.higher.rationalExchange
          (compactSupportProperSquare (𝟙 X : X ⟶ X)))).hom.app M).app L
      let c : ∀ M, U.obj M ≅ U.obj (U.obj M) := fun M ↦
        eqToIso (congrArg (fun f ↦ (S.higher.rational.pull f).obj M)
          (Category.id_comp (𝟙 X)).symm) ≪≫
          (S.higher.rational.pullComposition (𝟙 X) (𝟙 X)).app M
      ∀ M L, μ M L ≫ T.map (Prod.mkHom (c M).hom (c L).hom) =
        (c (T.obj (M, L))).hom ≫ U.map (μ M L) ≫ μ (U.obj M) (U.obj L)) ∧
    (∀ X : SixFunctorSpace D,
      letI : IsProper (𝟙 X : X ⟶ X).hom.left := by
        change IsProper (𝟙 X.obj.left)
        infer_instance
      let U := S.closure.commonStage.pull (𝟙 X)
      let T := Functor.uncurry.obj (S.closure.commonStageTensor X)
      let μ := fun M L ↦
        ((projectionPullbackTensor (S.closure.commonStageExchange
          (compactSupportProperSquare (𝟙 X : X ⟶ X)))).hom.app M).app L
      let c : ∀ M, U.obj M ≅ U.obj (U.obj M) := fun M ↦
        eqToIso (congrArg (fun f ↦ (S.closure.commonStage.pull f).obj M)
          (Category.id_comp (𝟙 X)).symm) ≪≫
          (S.closure.commonStage.pullComposition (𝟙 X) (𝟙 X)).app M
      ∀ M L, μ M L ≫ T.map (Prod.mkHom (c M).hom (c L).hom) =
        (c (T.obj (M, L))).hom ≫ U.map (μ M L) ≫ μ (U.obj M) (U.obj L)) := by sorry

end WeilConjectures
