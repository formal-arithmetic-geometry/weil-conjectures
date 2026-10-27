/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.Paper.FrameworkPbcComparisonSystem

/-! # Raw localization of fixed integral comparison laws

Source: current blueprint, purity-transport coefficient-change argument.
(blueprint: lem-pur-framework-pbc-raw-comparison-laws).
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FrameworkPbc

/-- Raw coefficient localization of fixed normalized integral comparisons.
The two pullback compositors are independently localized from their specified
integral maps; this theorem also retains the scalar and tensor squares.
Source: current blueprint, smooth-purity/purity-transport coefficient-change argument,
Step 8 of lem-pur-framework-pbc-pullback-scalar-bridge; Stacks 099N and 0D6D
(blueprint: lem-pur-framework-pbc-raw-comparison-laws).

Proof: Restrict the completed coefficient-presentation equivalence to the two full
constructible categories, using its predicate identification. Its inverse gives
preservation of the PBC pullback and tensor from their framework comparisons.
Restrict pi and tau, and the fixed inverse-chi scalarComponent, along this equivalence;
their ambient component identities give the integral fields of RawPullback,
RawScalar and RawTensor. Ordinary PBC scalar extension is the finite-free one.
Relabel the coefficient action through the specified uniformizer localization
isomorphisms. Extend the restricted equivalence and each functor to pure tensors
by a tensor f mapping to a tensor F(f). Extend each comparison component and its
inverse by tensoring with one. Integral naturality tensored with a proves
naturality on a pure tensor; additivity proves it on every finite sum. The inverse
equations remain identities after localization. This constructs exactly the raw
object and arrow formulas in the conclusion, without a Karoubi envelope.
Apply the same extension to the fixed integral scalar and tensor squares. The
inverse completed balancing map gives p.inv, and the fixed completed scalar tensor
map gives v and q. Localized functoriality preserves their compositions and the
equations on every object, hence gives the raw scalar and tensor squares.
Finally restrict the specified integral pullback unit and compositor, and localize
them separately on both sides to obtain su, pu, sc and pc. Their components are
precisely the localized integral components displayed below. Localizing the given
integral unit and composition equations, and the component normalization of pi,
gives the last two commuting equations. Objects of raw localization are unchanged,
so these equations hold on every rational object. The construction also applies
to the identity morphism, empty schemes, identity coefficient maps, and ramified
extensions; no quotient-map flatness is used. -/
theorem frameworkPbcRawComparisonLaws
    (l : ℕ) [Fact l.Prime] (realization : IntegralComparisonSystem.{u} l)
    (pullback : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
      {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
      [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
      [Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
      [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
      [Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))],
      (h : X ⟶ Y) → Pullback l A h)
    (tensor : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
      (W : Scheme.{u}) [IsNoetherian W]
      [Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]
      [Fact (∀ w : W, IsUnit (l : W.presheaf.stalk w))], Tensor l A W)
    (scalarTensor : ∀ (A B : Type u) [Field A] [Algebra ℚ_[l] A]
      [FiniteDimensional ℚ_[l] A] [Field B] [Algebra ℚ_[l] B]
      [FiniteDimensional ℚ_[l] B] (i : A →ₐ[ℚ_[l]] B) (W : Scheme.{u})
      [IsNoetherian W] [Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]
      [Fact (∀ w : W, IsUnit (l : W.presheaf.stalk w))],
      ScalarTensor l A B i W)
    (h_unit : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
      (W : Scheme.{u}) [IsNoetherian W]
      [Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]
      [Fact (∀ w : W, IsUnit (l : W.presheaf.stalk w))]
      (K : sfIntegralConstructibleCategory l A W),
      (pullback A (𝟙 W)).pi.hom.app K ≫
        (pbcActualCompletedPullIdIso (pbcIntegralDatum l A) W).hom.app
          ⟨(integralDetailedTransport W l A).obj K.obj,
            (purDetailedTransport_complete_iff l A W K.obj).mp K.property.1⟩ =
        (integralDetailedTransport W l A).map
          (integralComparisonUnit l A realization W K).hom)
    (h_composition : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A]
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
          ((pullback A g).pi.hom.app K))
    (h_scalar_square : ∀ (A B : Type u) [Field A] [Algebra ℚ_[l] A]
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
          ((integralDetailedTransport Y l A).obj K.obj))
    (h_tensor_square : ∀ (A B : Type u) [Field A] [Algebra ℚ_[l] A]
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
          (integralDetailedTransport W l A).obj N.obj))
 :
    ∃ coefficient : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A]
      [FiniteDimensional ℚ_[l] A] (W : Scheme.{u}) [IsNoetherian W]
      [Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]
      [Fact (∀ w : W, IsUnit (l : W.presheaf.stalk w))], Coefficient l A W,
    ∃ raw_pullback : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A]
      [FiniteDimensional ℚ_[l] A] {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
      [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
      [Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
      [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
      [Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))] (h : X ⟶ Y),
      RawPullback l A h (coefficient A X) (coefficient A Y) (pullback A h),
    ∃ raw_scalar : ∀ (A B : Type u) [Field A] [Algebra ℚ_[l] A]
      [FiniteDimensional ℚ_[l] A] [Field B] [Algebra ℚ_[l] B]
      [FiniteDimensional ℚ_[l] B] (i : A →ₐ[ℚ_[l]] B) (W : Scheme.{u})
      [IsNoetherian W] [hdim : Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]
      [hinv : Fact (∀ w : W, IsUnit (l : W.presheaf.stalk w))],
      RawScalar l A B i W hdim.out hinv.out (coefficient A W) (coefficient B W),
    ∃ raw_tensor : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A]
      [FiniteDimensional ℚ_[l] A] (W : Scheme.{u}) [IsNoetherian W]
      [Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]
      [Fact (∀ w : W, IsUnit (l : W.presheaf.stalk w))],
      RawTensor l A W (coefficient A W) (tensor A W),
    (∀ (A B : Type u) [Field A] [Algebra ℚ_[l] A]
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
        p.inv.app ((coefficient A Y).rational.functor.obj K)) ∧
    (∀ (A B : Type u) [Field A] [Algebra ℚ_[l] A]
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
        (coefficient A W).rational.functor.obj N)) ∧
    (∀ (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
      (W : Scheme.{u}) [IsNoetherian W]
      [Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]
      [Fact (∀ w : W, IsUnit (l : W.presheaf.stalk w))],
      ∃ su : rationalDerivedPullback l A (𝟙 W) ≅ 𝟭 _,
      ∃ pu : pbcConditionalRational (pbcIntegralDatum l A)
          (pbcActualCompletedPull (𝟙 W) (pbcIntegralDatum l A))
          (raw_pullback A (𝟙 W)).preserves (pbcUniformizer l A) ≅ 𝟭 _,
        (∀ K : sfIntegralConstructibleCategory l A W,
          HEq (su.hom.app ((sfRationalConstructibleLocalization l A W).obj K))
            ((sfRationalConstructibleLocalization l A W).map
              (ObjectProperty.homMk
                (X := (constructibleIntegralPullback l A (𝟙 W)).obj K) (Y := K)
                (integralComparisonUnit l A realization W K).hom))) ∧
        (∀ K : PbcBoundedConstructibleComplete W (pbcIntegralDatum l A),
          HEq (pu.hom.app ((pbcRationalization W (pbcIntegralDatum l A)
              (pbcUniformizer l A)).obj K))
            ((pbcRationalization W (pbcIntegralDatum l A) (pbcUniformizer l A)).map
              (ObjectProperty.homMk
                (X := (pbcConditionalIntegral (pbcIntegralDatum l A)
                  (pbcActualCompletedPull (𝟙 W) (pbcIntegralDatum l A))
                  (raw_pullback A (𝟙 W)).preserves).obj K) (Y := K)
                ((pbcActualCompletedPullIdIso
                (pbcIntegralDatum l A) W).hom.app ⟨K.obj, K.property.1⟩)))) ∧
        ∀ K : sfRationalConstructibleCategory l A W,
          (raw_pullback A (𝟙 W)).rational.hom.app K ≫
            pu.hom.app ((coefficient A W).rational.functor.obj K) =
          (coefficient A W).rational.functor.map (su.hom.app K)) ∧
    (∀ (A : Type u) [Field A] [Algebra ℚ_[l] A]
      [FiniteDimensional ℚ_[l] A] (X Y Z : Scheme.{u})
      [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
      [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
      [Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
      [Fact (∃ n : ℕ, topologicalKrullDim Z ≤ n)]
      [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
      [Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]
      [Fact (∀ z : Z, IsUnit (l : Z.presheaf.stalk z))]
      (h : X ⟶ Y) (g : Y ⟶ Z),
      ∃ sc : rationalDerivedPullback l A (h ≫ g) ≅
          rationalDerivedPullback l A g ⋙ rationalDerivedPullback l A h,
      ∃ pc : pbcConditionalRational (pbcIntegralDatum l A)
          (pbcActualCompletedPull (h ≫ g) (pbcIntegralDatum l A))
          (raw_pullback A (h ≫ g)).preserves (pbcUniformizer l A) ≅
        pbcConditionalRational (pbcIntegralDatum l A)
          (pbcActualCompletedPull g (pbcIntegralDatum l A))
          (raw_pullback A g).preserves (pbcUniformizer l A) ⋙
        pbcConditionalRational (pbcIntegralDatum l A)
          (pbcActualCompletedPull h (pbcIntegralDatum l A))
          (raw_pullback A h).preserves (pbcUniformizer l A),
        (∀ K : sfIntegralConstructibleCategory l A Z,
          HEq (sc.hom.app ((sfRationalConstructibleLocalization l A Z).obj K))
            ((sfRationalConstructibleLocalization l A X).map
              (ObjectProperty.homMk
                (X := (constructibleIntegralPullback l A (h ≫ g)).obj K)
                (Y := (constructibleIntegralPullback l A h).obj
                  ((constructibleIntegralPullback l A g).obj K))
                (integralComparisonComposition l A realization h g K).hom))) ∧
        (∀ K : PbcBoundedConstructibleComplete Z (pbcIntegralDatum l A),
          HEq (pc.hom.app ((pbcRationalization Z (pbcIntegralDatum l A)
              (pbcUniformizer l A)).obj K))
            ((pbcRationalization X (pbcIntegralDatum l A) (pbcUniformizer l A)).map
              (ObjectProperty.homMk
                (X := (pbcConditionalIntegral (pbcIntegralDatum l A)
                  (pbcActualCompletedPull (h ≫ g) (pbcIntegralDatum l A))
                  (raw_pullback A (h ≫ g)).preserves).obj K)
                (Y := (pbcConditionalIntegral (pbcIntegralDatum l A)
                  (pbcActualCompletedPull h (pbcIntegralDatum l A))
                  (raw_pullback A h).preserves).obj
                    ((pbcConditionalIntegral (pbcIntegralDatum l A)
                      (pbcActualCompletedPull g (pbcIntegralDatum l A))
                      (raw_pullback A g).preserves).obj K))
                ((pbcActualCompletedPullCompIso h g
                (pbcIntegralDatum l A)).inv.app ⟨K.obj, K.property.1⟩)))) ∧
        ∀ K : sfRationalConstructibleCategory l A Z,
          (raw_pullback A (h ≫ g)).rational.hom.app K ≫
            pc.hom.app ((coefficient A Z).rational.functor.obj K) =
          (coefficient A X).rational.functor.map (sc.hom.app K) ≫
            (raw_pullback A h).rational.hom.app ((rationalDerivedPullback l A g).obj K) ≫
            (pbcConditionalRational (pbcIntegralDatum l A)
              (pbcActualCompletedPull h (pbcIntegralDatum l A))
              (raw_pullback A h).preserves (pbcUniformizer l A)).map
                ((raw_pullback A g).rational.hom.app K)) := by sorry

end WeilConjectures.FrameworkPbc
