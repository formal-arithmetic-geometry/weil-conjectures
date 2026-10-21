/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q59
-/
module

public import Sheaf.Paper.FiniteCoefficientSiteChainTensor

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
/-! # Finite coefficient change for internal Hom

Source: blueprint sec-six-functors/sk-prop-sf-biduality-general,
node thm-coef-finite-hom (blueprint: def-sf-finite-coefficient-site-hom-arrow).
Indices n and m below denote exponents n + 1 and m + 1; thus every positive
exponent, including the identity quotient, occurs. All comparison maps are
closed transposes of reduced evaluation, never choices of arbitrary arrows.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u a b w c d e f g
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

/-- Explicit K-flat witness type with the small pro-etale universe fixed.
Source: blueprint site-comparison proof (blueprint: def-sf-finite-coefficient-site-hom-arrow). -/
abbrev finiteHomKFlat (n : ℕ)
    (P : CochainComplex (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E (n + 1))))) ℤ) : Prop :=
  @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
    X.ProEt inferInstance (essentiallySmallSelf.{0, u, u + 1} _)
    (Scheme.ProEt.topology X) (integralCoefficientCommRingSheaf l E X n)
    ((finiteHomNuComplex l E X n).obj P)

/-- The tensor-localization equation used to normalize the inverse-image tensorator.
Source: Stacks 07A4, site-comparison paragraph
(blueprint: def-sf-finite-coefficient-site-hom-arrow). -/
def FiniteHomNuModelSquareAux
    {C : Type a} {D : Type b} {A : Type c} {B : Type d}
    [Category.{e} C] [Category.{f} D] [Category.{g} A] [Category.{w} B]
    (QA : C ⥤ A) (QB : D ⥤ B) (U : C ⥤ D) (V : A ⥤ B)
    (ρ : QA ⋙ V ≅ U ⋙ QB) (TA : C → C → C) (TB : D → D → D)
    (SA : A × A ⥤ A) (SB : B × B ⥤ B)
    (ηA : ∀ P Q : C, SA.obj (QA.obj P, QA.obj Q) ⟶ QA.obj (TA P Q))
    (μ : SA ⋙ V ≅ V.prod V ⋙ SB) (P Q : C)
    (ε : U.obj (TA P Q) ≅ TB (U.obj P) (U.obj Q))
    (ηB : SB.obj (QB.obj (U.obj P), QB.obj (U.obj Q)) ⟶
      QB.obj (TB (U.obj P) (U.obj Q))) : Prop :=
  μ.hom.app (QA.obj P, QA.obj Q) ≫
      SB.map (Prod.mkHom (ρ.hom.app P) (ρ.hom.app Q)) ≫ ηB =
    V.map (ηA P Q) ≫ ρ.hom.app (TA P Q) ≫ QB.map ε.hom

/-- The specified tensorator is characterized on every pair of explicit K-flat
representatives by the ordinary pure-tensor chain comparison and the intrinsic
localization comparison. Source: Stacks 00YV, 06YN, 07A4 (blueprint:
def-sf-finite-coefficient-site-hom-arrow). -/
def FiniteHomNuTensorNormalization (n : ℕ)
    (μ : (finiteHomEtaleClosed l E X n).tensor ⋙ finiteHomNu l E X n ≅
      (finiteHomNu l E X n).prod (finiteHomNu l E X n) ⋙
        (finiteIntrinsicClosed l E X n).tensor) : Prop :=
  ∀ (P Q : CochainComplex (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E (n + 1))))) ℤ),
    ∀ hP : finiteHomKFlat l E X n P, ∀ hQ : finiteHomKFlat l E X n Q,
    letI : EssentiallySmall.{u + 1, u, u + 1} X.ProEt :=
      essentiallySmallSelf.{0, u, u + 1} _
    letI : HasDerivedCategory.{u + 2} (normalizedDVRModules l E X n) :=
      HasDerivedCategory.standard _
    FiniteHomNuModelSquareAux
      (finiteHomEtaleQ l E X n) (finiteHomIntrinsicQ l E X n)
      (finiteHomNuComplex l E X n) (finiteHomNu l E X n)
      (finiteHomNuFactors l E X n)
      (fun P Q ↦ HomologicalComplex.tensorObj P Q)
      (fun P Q ↦ (coefficientTotalTensor.{u, u + 1, u}
        (Scheme.ProEt.topology X) (integralCoefficientCommRingSheaf l E X n)).obj (P, Q))
      (finiteHomEtaleClosed l E X n).tensor
      (finiteIntrinsicClosed l E X n).tensor
      (finiteHomEtaleTensorModel l E X n) μ P Q
      (finiteHomNuChainTensor l E X n P Q)
      ((finiteIntrinsicTensorModels l E X n).comparison.inv.app
        (⟨(finiteHomNuComplex l E X n).obj P, hP⟩,
          ⟨(finiteHomNuComplex l E X n).obj Q, hQ⟩))

/-- The inverse-image tensor comparison is uniquely fixed by the displayed
K-flat pure-tensor and localization equations. Source: blueprint site-comparison
proof (blueprint: def-sf-finite-coefficient-site-hom-arrow).
Proof: inverse image preserves the balanced pure-tensor chain map; localization
and the intrinsic tensor-model comparison identify its derived image. The
representative equation determines the natural isomorphism uniquely. -/
theorem finiteHomNuTensor_existsUnique (n : ℕ) :
    ∃! μ, FiniteHomNuTensorNormalization l E X n μ := by
  sorry

/-- The canonical normalized tensor comparison for nu_X^*.
Source: blueprint site-comparison proof (blueprint: def-sf-finite-coefficient-site-hom-arrow). -/
def finiteHomNuTensor (n : ℕ) :
    (finiteHomEtaleClosed l E X n).tensor ⋙ finiteHomNu l E X n ≅
      (finiteHomNu l E X n).prod (finiteHomNu l E X n) ⋙
        (finiteIntrinsicClosed l E X n).tensor :=
  (finiteHomNuTensor_existsUnique l E X n).choose

/-- The site internal-Hom comparison, the transpose of inverse image of evaluation.
Source: blueprint site formula (blueprint: def-sf-finite-coefficient-site-hom-arrow). -/
def finiteHomSiteHom (n : ℕ) :=
  coefficientBaseChangeHom (finiteHomEtaleClosed l E X n) (finiteIntrinsicClosed l E X n)
    (finiteHomNu l E X n) (finiteHomNuTensor l E X n)

end WeilConjectures
