module

public import Sheaf.Paper.FrameworkPbcRawComparisonData
public import Sheaf.Paper.IntegralPullbackComparisonRealization

/-! # Framework and PBC pullback scalar coherence

Source: purity-transport coefficient-change proof
(blueprint: def-pur-framework-pbc-comparison-system).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genCtorIdx false
set_option genSizeOfSpec false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FrameworkPbc

/-- One simultaneous system of comparisons, for all fields, morphisms and scalar
inclusions. Every comparison is normalized in the fields above; coherence is a
conclusion, not a hypothesis on arbitrary functors.
Source: purity-transport coefficient-change proof; Stacks 099N, 07A4, 0D6D
(blueprint: def-pur-framework-pbc-comparison-system). -/
structure System (l : ℕ) [Fact l.Prime] where
  realization : IntegralComparisonSystem.{u} l
  realization_coherent : ∀ (A B : Type u) [Field A] [Algebra ℚ_[l] A]
    [FiniteDimensional ℚ_[l] A] [Field B] [Algebra ℚ_[l] B]
    [FiniteDimensional ℚ_[l] B] (i : A →ₐ[ℚ_[l]] B),
    IntegralComparisonRealizationCoherence l A B i realization
  pullback : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
    [Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
    [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
    [Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))],
    (h : X ⟶ Y) → Pullback l A h
  coefficient : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A]
    [FiniteDimensional ℚ_[l] A] (W : Scheme.{u}) [IsNoetherian W]
    [Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]
    [Fact (∀ w : W, IsUnit (l : W.presheaf.stalk w))], Coefficient l A W
  scalar : ∀ (A B : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
    [Field B] [Algebra ℚ_[l] B] [FiniteDimensional ℚ_[l] B]
    (i : A →ₐ[ℚ_[l]] B) (W : Scheme.{u}) [IsNoetherian W]
    [Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]
    [Fact (∀ w : W, IsUnit (l : W.presheaf.stalk w))], Scalar l A B i W
  tensor : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
    (W : Scheme.{u}) [IsNoetherian W]
    [Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]
    [Fact (∀ w : W, IsUnit (l : W.presheaf.stalk w))], Tensor l A W
  scalarTensor : ∀ (A B : Type u) [Field A] [Algebra ℚ_[l] A]
    [FiniteDimensional ℚ_[l] A] [Field B] [Algebra ℚ_[l] B]
    [FiniteDimensional ℚ_[l] B] (i : A →ₐ[ℚ_[l]] B) (W : Scheme.{u})
    [IsNoetherian W] [Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]
    [Fact (∀ w : W, IsUnit (l : W.presheaf.stalk w))],
    ScalarTensor l A B i W
  unit : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
    (W : Scheme.{u}) [IsNoetherian W]
    [Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]
    [Fact (∀ w : W, IsUnit (l : W.presheaf.stalk w))]
    (K : sfIntegralConstructibleCategory l A W),
    (pullback A (𝟙 W)).pi.hom.app K ≫
      (pbcActualCompletedPullIdIso (pbcIntegralDatum l A) W).hom.app
        ⟨(integralDetailedTransport W l A).obj K.obj,
          (purDetailedTransport_complete_iff l A W K.obj).mp K.property.1⟩ =
      (integralDetailedTransport W l A).map
        (integralComparisonUnit l A realization W K).hom
  composition : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A]
    [FiniteDimensional ℚ_[l] A] (X Y Z : Scheme.{u})
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
    [Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
    [Fact (∃ n : ℕ, topologicalKrullDim Z ≤ n)]
    [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
    [Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]
    [Fact (∀ z : Z, IsUnit (l : Z.presheaf.stalk z))]
    (h : X ⟶ Y) (g : Y ⟶ Z) (K : sfIntegralConstructibleCategory l A Z),
    (pullback A (h ≫ g)).pi.hom.app K ≫
      (pbcActualCompletedPullCompIso h g (pbcIntegralDatum l A)).inv.app
        ⟨(integralDetailedTransport Z l A).obj K.obj,
          (purDetailedTransport_complete_iff l A Z K.obj).mp K.property.1⟩ =
    (integralDetailedTransport X l A).map
        (integralComparisonComposition l A realization h g K).hom ≫
      (pullback A h).pi.hom.app ((constructibleIntegralPullback l A g).obj K) ≫
      (pbcActualCompletedPull h (pbcIntegralDatum l A)).map
        ((pullback A g).pi.hom.app K)
  scalar_square : ∀ (A B : Type u) [Field A] [Algebra ℚ_[l] A]
    [FiniteDimensional ℚ_[l] A] [Field B] [Algebra ℚ_[l] B]
    [FiniteDimensional ℚ_[l] B] (i : A →ₐ[ℚ_[l]] B)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
    [Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
    [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
    [Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]
    (h : X ⟶ Y) (K : sfIntegralConstructibleCategory l A Y),
    (integralDetailedTransport X l B).map
        (integralPullbackScalarComparison l A B i h K).hom.hom ≫
      (pullback B h).pi.hom.app ((integralComparisonConstructibleScalar l A B i Y).obj K) ≫
      (pbcActualCompletedPull h (pbcIntegralDatum l B)).map
        (scalarComponent l A B i Y K).hom =
    (scalarComponent l A B i X ((constructibleIntegralPullback l A h).obj K)).hom ≫
      (pbcEmbeddingAmbientTensor l A B i X).map ((pullback A h).pi.hom.app K) ≫
      (pbcScalarCompletedPullIso l A B i h).inv.app
        ((integralDetailedTransport Y l A).obj K.obj)
  tensor_square : ∀ (A B : Type u) [Field A] [Algebra ℚ_[l] A]
    [FiniteDimensional ℚ_[l] A] [Field B] [Algebra ℚ_[l] B]
    [FiniteDimensional ℚ_[l] B] (i : A →ₐ[ℚ_[l]] B)
    (W : Scheme.{u}) [IsNoetherian W]
    [Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]
    [Fact (∀ w : W, IsUnit (l : W.presheaf.stalk w))]
    (M N : sfIntegralConstructibleCategory l A W),
    (pbcEmbeddingAmbientTensor l A B i W).map ((tensor A W).tau.inv.app (M.obj, N.obj)) ≫
      (scalarComponent l A B i W ((constructibleIntegralTensor l A W).obj (M, N))).inv ≫
      (integralDetailedTransport W l B).map
        (integralTensorScalarComparison l A B i W M N).hom.hom ≫
      (tensor B W).tau.hom.app
        (((integralComparisonConstructibleScalar l A B i W).obj M).obj,
          ((integralComparisonConstructibleScalar l A B i W).obj N).obj) ≫
      (FrameworkPbc.tensor l B W).map
        (Prod.mkHom (scalarComponent l A B i W M).hom
          (scalarComponent l A B i W N).hom) =
    ((scalarTensor A B i W).completed l A B i).hom.app
      ((integralDetailedTransport W l A).obj M.obj,
        (integralDetailedTransport W l A).obj N.obj)

  scalar_unit : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A]
    [FiniteDimensional ℚ_[l] A] (W : Scheme.{u}) [IsNoetherian W]
    [Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]
    [Fact (∀ w : W, IsUnit (l : W.presheaf.stalk w))]
    (K : sfIntegralConstructibleCategory l A W),
    (scalarComponent l A A (AlgHom.id ℚ_[l] A) W K).hom ≫
      (pbcEmbeddingAmbientUnit l A W).hom.app
        ((integralDetailedTransport W l A).obj K.obj) =
    (integralDetailedTransport W l A).map (integralComparisonScalarUnit l A W K).hom
  scalar_tower : ∀ (A B C : Type u) [Field A] [Algebra ℚ_[l] A]
    [FiniteDimensional ℚ_[l] A] [Field B] [Algebra ℚ_[l] B]
    [FiniteDimensional ℚ_[l] B] [Field C] [Algebra ℚ_[l] C]
    [FiniteDimensional ℚ_[l] C] (i : A →ₐ[ℚ_[l]] B) (j : B →ₐ[ℚ_[l]] C)
    (W : Scheme.{u}) [IsNoetherian W]
    [Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]
    [Fact (∀ w : W, IsUnit (l : W.presheaf.stalk w))]
    (K : sfIntegralConstructibleCategory l A W),
    (scalarComponent l B C j W ((integralComparisonConstructibleScalar l A B i W).obj K)).hom ≫
      (pbcEmbeddingAmbientTensor l B C j W).map (scalarComponent l A B i W K).hom ≫
      (pbcAmbientScalarComp l A B C i j W).hom.app
        ((integralDetailedTransport W l A).obj K.obj) =
    (integralDetailedTransport W l C).map
        (integralComparisonScalarAssociator l A B i C j W K).hom ≫
      (scalarComponent l A C (j.comp i) W K).hom
  pullback_shifts : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A]
    [FiniteDimensional ℚ_[l] A] {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
    [Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
    [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
    [Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))] (h : X ⟶ Y),
    ∃ c : (integralOperationsPullbackComplexFunctor l A h).CommShift ℤ,
    ∃ d : (integralDerivedPullback l A h).CommShift ℤ,
      IntegralCompletedComparison.ShiftCoordinates l A h c ∧
      IntegralCompletedComparison.ShiftDescent l A h c d ∧
      ∀ (K : sfIntegralConstructibleCategory l A Y) (r : ℤ),
      ∃ hKr : sfIntegralConstructible l A Y (K.obj⟦r⟧),
      HEq ((integralDetailedTransport X l A).map
          ((Functor.commShiftIso (integralDerivedPullback l A h) (self := d) r).hom.app
            K.obj) ≫
        ((fdCoefficientTransport l A X).mapDerivedCategory.commShiftIso r).hom.app
          ((integralDerivedPullback l A h).obj K.obj) ≫
        ((pullback A h).pi.hom.app K)⟦r⟧')
        ((pullback A h).pi.hom.app ⟨K.obj⟦r⟧, hKr⟩ ≫
          (pbcActualCompletedPull h (pbcIntegralDatum l A)).map
            (((fdCoefficientTransport l A Y).mapDerivedCategory.commShiftIso r).hom.app
              K.obj) ≫
          ((pbcActualCompletedPull h (pbcIntegralDatum l A)).commShiftIso r).hom.app
            ((integralDetailedTransport Y l A).obj K.obj))
  scalar_shifts : ∀ (A B : Type u) [Field A] [Algebra ℚ_[l] A]
    [FiniteDimensional ℚ_[l] A] [Field B] [Algebra ℚ_[l] B]
    [FiniteDimensional ℚ_[l] B] (i : A →ₐ[ℚ_[l]] B) (W : Scheme.{u})
    [IsNoetherian W] [Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]
    [Fact (∀ w : W, IsUnit (l : W.presheaf.stalk w))],
    ∃ (c : (integralScalarComplexFunctor l A B i W).CommShift ℤ)
      (o : (completedDerivedScalarExtension l A B i W).CommShift ℤ)
      (d : (integralScalarExtension l A B i W).CommShift ℤ),
      completedScalarShiftRepresentativeProperty i W c o d ∧
      ∀ (K : sfIntegralConstructibleCategory l A W) (r : ℤ),
      ∃ hKr : sfIntegralConstructible l A W (K.obj⟦r⟧),
      HEq ((integralDetailedTransport W l B).map
          ((Functor.commShiftIso (integralScalarExtension l A B i W) (self := d) r).hom.app
            K.obj) ≫
        ((fdCoefficientTransport l B W).mapDerivedCategory.commShiftIso r).hom.app
          ((integralScalarExtension l A B i W).obj K.obj) ≫
        (scalarComponent l A B i W K).hom⟦r⟧')
        ((scalarComponent l A B i W ⟨K.obj⟦r⟧, hKr⟩).hom ≫
          (pbcEmbeddingAmbientTensor l A B i W).map
            (((fdCoefficientTransport l A W).mapDerivedCategory.commShiftIso r).hom.app
              K.obj) ≫
          ((pbcEmbeddingAmbientTensor l A B i W).commShiftIso r).hom.app
            ((integralDetailedTransport W l A).obj K.obj))

  raw_pullback : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A]
    [FiniteDimensional ℚ_[l] A] {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
    [Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
    [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
    [Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))] (h : X ⟶ Y),
    RawPullback l A h (coefficient A X) (coefficient A Y) (pullback A h)
  raw_scalar : ∀ (A B : Type u) [Field A] [Algebra ℚ_[l] A]
    [FiniteDimensional ℚ_[l] A] [Field B] [Algebra ℚ_[l] B]
    [FiniteDimensional ℚ_[l] B] (i : A →ₐ[ℚ_[l]] B) (W : Scheme.{u})
    [IsNoetherian W] [hdim : Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]
    [hinv : Fact (∀ w : W, IsUnit (l : W.presheaf.stalk w))],
    RawScalar l A B i W hdim.out hinv.out (coefficient A W) (coefficient B W)
  raw_tensor : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A]
    [FiniteDimensional ℚ_[l] A] (W : Scheme.{u}) [IsNoetherian W]
    [Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]
    [Fact (∀ w : W, IsUnit (l : W.presheaf.stalk w))],
    RawTensor l A W (coefficient A W) (tensor A W)
  raw_scalar_square : ∀ (A B : Type u) [Field A] [Algebra ℚ_[l] A]
    [FiniteDimensional ℚ_[l] A] [Field B] [Algebra ℚ_[l] B]
    [FiniteDimensional ℚ_[l] B] (i : A →ₐ[ℚ_[l]] B)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    [dx : Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
    [dy : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
    [ix : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
    [iy : Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]
    (h : X ⟶ Y),
    ∃ p : pbcRationalScalarExtension l A B i Y dy.out iy.out ⋙
        pbcConditionalRational (pbcIntegralDatum l B)
          (pbcActualCompletedPull h (pbcIntegralDatum l B))
          (raw_pullback B h).preserves (pbcUniformizer l B) ≅
      pbcConditionalRational (pbcIntegralDatum l A)
        (pbcActualCompletedPull h (pbcIntegralDatum l A))
        (raw_pullback A h).preserves (pbcUniformizer l A) ⋙
          pbcRationalScalarExtension l A B i X dx.out ix.out,
    (∀ K : PbcBoundedConstructibleComplete Y (pbcIntegralDatum l A),
      ∃ f : (pbcConditionalIntegral (pbcIntegralDatum l A)
          (pbcActualCompletedPull h (pbcIntegralDatum l A))
          (raw_pullback A h).preserves ⋙
            pbcEmbeddingIntegralTensor l A B i X dx.out ix.out).obj K ⟶
        (pbcEmbeddingIntegralTensor l A B i Y dy.out iy.out ⋙
          pbcConditionalIntegral (pbcIntegralDatum l B)
            (pbcActualCompletedPull h (pbcIntegralDatum l B))
            (raw_pullback B h).preserves).obj K,
      HEq f.hom ((pbcScalarCompletedPullIso l A B i h).inv.app K.obj) ∧
      HEq (p.inv.app ((pbcRationalization Y (pbcIntegralDatum l A)
        (pbcUniformizer l A)).obj K))
        ((pbcRationalization X (pbcIntegralDatum l B) (pbcUniformizer l B)).map f)) ∧
    ∀ K : sfRationalConstructibleCategory l A Y,
    (coefficient B X).rational.functor.map
        ((rationalPullbackScalarComparison l A B i h).hom.app K) ≫
      (raw_pullback B h).rational.hom.app
        ((sfRationalScalarExtension l A Y 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) B i).obj K) ≫
      (pbcConditionalRational (pbcIntegralDatum l B)
        (pbcActualCompletedPull h (pbcIntegralDatum l B))
        (raw_pullback B h).preserves (pbcUniformizer l B)).map
          ((raw_scalar A B i Y).rational.hom.app K) =
    (raw_scalar A B i X).rational.hom.app ((rationalDerivedPullback l A h).obj K) ≫
      (pbcRationalScalarExtension l A B i X dx.out ix.out).map
        ((raw_pullback A h).rational.hom.app K) ≫
      p.inv.app ((coefficient A Y).rational.functor.obj K)

  raw_tensor_square : ∀ (A B : Type u) [Field A] [Algebra ℚ_[l] A]
    [FiniteDimensional ℚ_[l] A] [Field B] [Algebra ℚ_[l] B]
    [FiniteDimensional ℚ_[l] B] (i : A →ₐ[ℚ_[l]] B) (W : Scheme.{u})
    [IsNoetherian W] [dw : Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]
    [iw : Fact (∀ w : W, IsUnit (l : W.presheaf.stalk w))],
    ∃ v : (raw_tensor A W).integral ⋙
        pbcEmbeddingIntegralTensor l A B i W dw.out iw.out ≅
      ((pbcEmbeddingIntegralTensor l A B i W dw.out iw.out).prod
        (pbcEmbeddingIntegralTensor l A B i W dw.out iw.out)) ⋙
          (raw_tensor B W).integral,
    ∃ q : (raw_tensor A W).rational ⋙
        pbcRationalScalarExtension l A B i W dw.out iw.out ≅
      ((pbcRationalScalarExtension l A B i W dw.out iw.out).prod
        (pbcRationalScalarExtension l A B i W dw.out iw.out)) ⋙
          (raw_tensor B W).rational,
    (∀ M N, HEq (v.hom.app (M, N)).hom
      (((scalarTensor A B i W).completed l A B i).hom.app (M.obj, N.obj))) ∧
    (∀ M N, HEq (q.hom.app
      ((pbcRationalization W (pbcIntegralDatum l A) (pbcUniformizer l A)).obj M,
        (pbcRationalization W (pbcIntegralDatum l A) (pbcUniformizer l A)).obj N))
      ((pbcRationalization W (pbcIntegralDatum l B) (pbcUniformizer l B)).map
        (v.hom.app (M, N)))) ∧
    ∀ M N : sfRationalConstructibleCategory l A W,
    (pbcRationalScalarExtension l A B i W dw.out iw.out).map
        ((raw_tensor A W).rational_tau.inv.app (M, N)) ≫
      (raw_scalar A B i W).rational.inv.app ((rationalDerivedTensor l A W).obj (M, N)) ≫
      (coefficient B W).rational.functor.map
        ((rationalTensorScalarComparison l A B i W).hom.app (M, N)) ≫
      (raw_tensor B W).rational_tau.hom.app
        ((sfRationalScalarExtension l A W 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) B i).obj M,
          (sfRationalScalarExtension l A W 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) B i).obj N) ≫
      (raw_tensor B W).rational.map
        (Prod.mkHom ((raw_scalar A B i W).rational.hom.app M)
          ((raw_scalar A B i W).rational.hom.app N)) =
    q.hom.app ((coefficient A W).rational.functor.obj M,
      (coefficient A W).rational.functor.obj N)

end WeilConjectures.FrameworkPbc
