/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FrameworkPbcPullbackComparisonData
public import WeilConjectures.AlgebraicGeometry.CompletedCoefficientPresentationTransport
public import WeilConjectures.AlgebraicGeometry.ProjectionTensorCoefficientComparison
public import WeilConjectures.AlgebraicGeometry.CompletedScalarShift

/-! # Framework and PBC pullback and scalar comparison

Source: smooth-purity, purity-transport coefficient-change proof; Stacks 099N,
0941, 07A4 and 0D6D (blueprint: def-pur-framework-pbc-comparison-data).
The comparisons retain the strict quotient tower, its augmentation, the ordinary
balanced tensor maps, the canonical completion units and raw rationalization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genCtorIdx false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FrameworkPbc

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The PBC tensor is ordinary derived tensor followed by the specified completion.
Source: Stacks 07A4 and 099N
(blueprint: def-pur-framework-pbc-comparison-data). -/
def tensor (W : Scheme.{u}) :
    PbcCompletedDerived W (pbcIntegralDatum l E) ×
      PbcCompletedDerived W (pbcIntegralDatum l E) ⥤
        PbcCompletedDerived W (pbcIntegralDatum l E) :=
  wfOrdinaryDerivedTensor W (pbcIntegralDatum l E) ⋙
    pbcActualCompletion (pbcIntegralDatum l E) W

variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- The actual j component: inverse chi, then the normalized scalar-presentation map.
All round trips are the units and counits of the recorded coefficient equivalence.
Source: Stacks 099N; Bhatt--Scholze 6.8.2(1)
(blueprint: def-pur-framework-pbc-comparison-data). -/
def scalarComponent (W : Scheme.{u}) (K : sfIntegralConstructibleCategory l E W) :
    (integralDetailedTransport W l L).obj
        ((integralScalarExtension l E L ι W).obj K.obj) ≅
      (pbcEmbeddingAmbientTensor l E L ι W).obj
        ((integralDetailedTransport W l E).obj K.obj) :=
  (integralDetailedTransport W l L).mapIso
      (scalarCompletionIso l E L ι W K.obj K.property.1).symm ≪≫
    (integralDetailedTransport W l L).mapIso
      ((integralOrdinaryDerivedScalar l E L ι W).mapIso
        ((purCoefficientModel l E W).counitIso.app K.obj).symm) ≪≫
    (integralDetailedTransport W l L).mapIso
      ((purScalarModel l E L ι W).symm.app
        ((integralDetailedTransport W l E).obj K.obj)) ≪≫
    ((purCoefficientModel l L W).unitIso.app
      ((pbcEmbeddingAmbientTensor l E L ι W).obj
        ((integralDetailedTransport W l E).obj K.obj))).symm

/-- The ordinary coefficient comparison preserves the chosen scalar-completion map chi.
Source: Stacks 099N, Bhatt--Scholze 6.8.2(1)
(blueprint: def-pur-framework-pbc-comparison-data). -/
structure Scalar (W : Scheme.{u}) where
  naturality : ∀ (K H : sfIntegralConstructibleCategory l E W) (f : K ⟶ H),
    (integralDetailedTransport W l L).map
        ((integralScalarExtension l E L ι W).map f.hom) ≫
      (scalarComponent l E L ι W H).hom =
    (scalarComponent l E L ι W K).hom ≫
      (pbcEmbeddingAmbientTensor l E L ι W).map
        ((integralDetailedTransport W l E).map f.hom)

  ordinary : completedDerivedScalarExtension l E L ι W ≅
    integralOrdinaryDerivedScalar l E L ι W
  chi : ∀ K : DerivedCategory (integralTowerModules l E W),
    (completedScalarComparison l E L ι W).app K =
      ordinary.hom.app K ≫ (scalarCompletion l E L ι W).app K

/-- Coefficient relabeling of completed tensors, normalized before completion by
signed total tensor and the actual quotient-unit chain map in `presentation`.
Source: Stacks 07A4, 099N
(blueprint: def-pur-framework-pbc-comparison-data). -/
structure Tensor (W : Scheme.{u}) where
  presentation : OpenFactorCoherence.Tensor l E W
  tau : integralCompletedTensor l E W ⋙ integralDetailedTransport W l E ≅
    ((integralDetailedTransport W l E).prod (integralDetailedTransport W l E)) ⋙
      tensor l E W
  normalization : ∀ M N : DerivedCategory (integralTowerModules l E W),
    (integralDetailedTransport W l E).map ((presentation.chi l E).app (M, N)) ≫
        tau.hom.app (M, N) =
      (ProjectionTensorCoefficient.ordinaryComparison l E W presentation.ordinary).hom.app
          (M, N) ≫
        (pbcActualCompletionUnit (pbcIntegralDatum l E) W).app
          ((wfOrdinaryDerivedTensor W (pbcIntegralDatum l E)).obj
            ((integralDetailedTransport W l E).obj M,
              (integralDetailedTransport W l E).obj N))

/-- Ordinary and derived balancing for PBC scalar tensor. The chain formula is
`s tensor (x tensor y)` mapped to `(s tensor x) tensor (1 tensor y)` in every
homogeneous summand; the derived comparison retains the universal counits.
Source: Stacks 03EL, 07A4
(blueprint: def-pur-framework-pbc-comparison-data). -/
structure ScalarTensor (W : Scheme.{u}) where
  chain : coefficientTotalTensor.{u, u+1, u} (ProEt.topology W)
      (pbcAdicCompletion W (pbcIntegralDatum l E)) ⋙
        (pbcExtend (pbcScalarCoefficientMap l E L ι W)).mapHomologicalComplex (.up ℤ) ≅
    ((pbcExtend (pbcScalarCoefficientMap l E L ι W)).mapHomologicalComplex (.up ℤ)).prod
      ((pbcExtend (pbcScalarCoefficientMap l E L ι W)).mapHomologicalComplex (.up ℤ)) ⋙
        coefficientTotalTensor.{u, u+1, u} (ProEt.topology W)
          (pbcAdicCompletion W (pbcIntegralDatum l L))
  formula : ∀ (P Q : CochainComplex
      (pbcModules W (pbcAdicCompletion W (pbcIntegralDatum l E))) ℤ)
    (p q : ℤ) (V : W.ProEtᵒᵖ)
    (s : (pbcAdicCompletion W (pbcIntegralDatum l L)).obj.obj V)
    (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V),
    ((chain.hom.app (P, Q)).f (p + q)).val.app V
      (pbcTensorSection (pbcScalarCoefficientMap l E L ι W)
        (((coefficientTotalTensor.{u, u+1, u} (ProEt.topology W)
          (pbcAdicCompletion W (pbcIntegralDatum l E))).obj (P, Q)).X (p + q)) V s
        (coefficientTensorGenerator.{u, u+1, u} (ProEt.topology W)
          (pbcAdicCompletion W (pbcIntegralDatum l E)) P Q p q (p + q) rfl V x y)) =
      coefficientTensorGenerator.{u, u+1, u} (ProEt.topology W)
        (pbcAdicCompletion W (pbcIntegralDatum l L))
        (((pbcExtend (pbcScalarCoefficientMap l E L ι W)).mapHomologicalComplex
          (.up ℤ)).obj P)
        (((pbcExtend (pbcScalarCoefficientMap l E L ι W)).mapHomologicalComplex
          (.up ℤ)).obj Q) p q (p + q) rfl V
        (pbcTensorSection (pbcScalarCoefficientMap l E L ι W) (P.X p) V s x)
        (pbcTensorSection (pbcScalarCoefficientMap l E L ι W) (Q.X q) V 1 y)
  good : ∀ P : (proEtaleFlatRepresentatives W
      (pbcAdicCompletion W (pbcIntegralDatum l E))).FullSubcategory,
    proEtaleFlatRepresentatives W (pbcAdicCompletion W (pbcIntegralDatum l L))
      (((pbcExtend (pbcScalarCoefficientMap l E L ι W)).mapHomologicalComplex
        (.up ℤ)).obj P.obj)
  ordinary : wfOrdinaryDerivedTensor W (pbcIntegralDatum l E) ⋙
      pbcEmbeddingAmbientTensor l E L ι W ≅
    ((pbcEmbeddingAmbientTensor l E L ι W).prod
      (pbcEmbeddingAmbientTensor l E L ι W)) ⋙
        wfOrdinaryDerivedTensor W (pbcIntegralDatum l L)
  representatives : ∀ P Q : (proEtaleFlatRepresentatives W
      (pbcAdicCompletion W (pbcIntegralDatum l E))).FullSubcategory,
    (pbcEmbeddingAmbientTensor l E L ι W).map
        ((wfTensorModel W (pbcIntegralDatum l E)).representative.inv.app (P, Q)) ≫
      pbcComplexCounit (pbcScalarCoefficientMap l E L ι W) _ ≫
      DerivedCategory.Q.map (chain.hom.app (P.obj, Q.obj)) ≫
      (wfTensorModel W (pbcIntegralDatum l L)).representative.hom.app
        (⟨_, good P⟩, ⟨_, good Q⟩) =
    ordinary.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
      (wfOrdinaryDerivedTensor W (pbcIntegralDatum l L)).map
        (Prod.mkHom (pbcComplexCounit (pbcScalarCoefficientMap l E L ι W) P.obj)
          (pbcComplexCounit (pbcScalarCoefficientMap l E L ι W) Q.obj))

/-- The canonical completed PBC scalar tensor comparison: kappa followed by
completion of ordinary balancing, retaining their independently fixed direction.
Source: Stacks 07A4, 099N
(blueprint: def-pur-framework-pbc-comparison-data). -/
def ScalarTensor.completed {W : Scheme.{u}} (t : ScalarTensor l E L ι W) :
    tensor l E W ⋙ pbcEmbeddingAmbientTensor l E L ι W ≅
      ((pbcEmbeddingAmbientTensor l E L ι W).prod
        (pbcEmbeddingAmbientTensor l E L ι W)) ⋙ tensor l L W :=
  Functor.isoWhiskerLeft (wfOrdinaryDerivedTensor W (pbcIntegralDatum l E))
      (pbcScalarCompletionIso l E L ι W).symm ≪≫
    Functor.isoWhiskerRight t.ordinary (pbcActualCompletion (pbcIntegralDatum l L) W)

end WeilConjectures.FrameworkPbc
