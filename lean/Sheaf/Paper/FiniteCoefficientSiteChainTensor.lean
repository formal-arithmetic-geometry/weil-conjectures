/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q59
-/
module

public import Sheaf.Paper.FiniteCoefficientSiteScalarArrow
public import Sheaf.Paper.FiniteCoefficientIntrinsicChainTensor

/-! # Finite coefficient change for internal Hom

Source: blueprint sec-six-functors/sk-prop-sf-biduality-general,
node thm-coef-finite-hom (blueprint: def-sf-finite-coefficient-site-chain-tensor).
Indices n and m below denote exponents n + 1 and m + 1; thus every positive
exponent, including the identity quotient, occurs. All comparison maps are
closed transposes of reduced evaluation, never choices of arbitrary arrows.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u a b w c d e f g
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local instance] ProEtale.finiteCoefficientIntrinsicMonoidal

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

attribute [local irreducible] finiteHomEtaleData
  finiteHomEtaleClosedGeneral finiteHomEtaleClosedWitnessRing
  SheafOfModules.monoidalCategory

/-- The termwise inverse image, retaining the original small site's sizes.
Source: blueprint site formula (blueprint: def-sf-finite-coefficient-site-chain-tensor). -/
def finiteHomNuComplex (n : ℕ) :
    CochainComplex (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E (n + 1))))) ℤ ⥤
      CochainComplex (normalizedDVRModules l E X n) ℤ :=
  (finiteHomNuOrdinary l E X n).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The exact comparison's localization isomorphism, with both derived sizes fixed.
Source: blueprint nu_X^* site formula (blueprint: def-sf-finite-coefficient-site-chain-tensor). -/
def finiteHomNuFactors (n : ℕ) :
    finiteHomEtaleQ l E X n ⋙ finiteHomNu l E X n ≅
      finiteHomNuComplex l E X n ⋙ finiteHomIntrinsicQ l E X n :=
  letI : EssentiallySmall.{u + 1, u, u + 1} X.ProEt :=
    essentiallySmallSelf.{0, u, u + 1} _
  letI : HasDerivedCategory.{u + 1} (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1}
    (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))) := inferInstance
  letI : HasDerivedCategory.{u + 2} (normalizedDVRModules l E X n) :=
    HasDerivedCategory.standard _
  (finiteHomNuOrdinary l E X n).mapDerivedCategoryFactors

/-- The chain tensor comparison is fixed on every local pure tensor.
Source: Stacks 00YV, 06YN, 07A4
(blueprint: def-sf-finite-coefficient-site-chain-tensor). -/
def FiniteHomNuChainTensorNormalization (n : ℕ) :=
  letI : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  ProEtale.FiniteCoefficientChainTensorNormalization.{u} X
    (Padic.coefficientExtensionRing l E (n + 1))

/-- Ordinary inverse image has the unique pure-tensor comparison on total complexes.
Source: Stacks 00YV, 06YN, 07A4
(blueprint: def-sf-finite-coefficient-site-chain-tensor).
Proof: on module presheaves, inverse image sends a balanced pure tensor to the
same tensor of the images of its factors. Module sheafification preserves this
universal tensor map. Degreewise the maps commute with the signed total differential,
so they form a chain isomorphism. The reverse balanced tensor map is inverse.
The displayed images generate inverse-image tensors locally; restriction and gluing
therefore make the pure-tensor normalization determine the chain isomorphism uniquely. -/
theorem finiteHomNuChainTensor_existsUnique (n : ℕ)
    (P Q : CochainComplex (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))) ℤ) :
    ∃! e, FiniteHomNuChainTensorNormalization l E X n P Q e := by
  have : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  exact ProEtale.finiteCoefficientIntrinsicChainTensor_existsUnique X
    (Padic.coefficientExtensionRing l E (n + 1)) P Q

/-- The canonical chain tensor comparison, determined by its generator normalization.
Source: Stacks 00YV, 06YN, 07A4
(blueprint: def-sf-finite-coefficient-site-chain-tensor). -/
def finiteHomNuChainTensor (n : ℕ)
    (P Q : CochainComplex (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))) ℤ) :
    (finiteHomNuComplex l E X n).obj (HomologicalComplex.tensorObj P Q) ≅
      (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology X)
        (integralCoefficientCommRingSheaf l E X n)).obj
        ((finiteHomNuComplex l E X n).obj P, (finiteHomNuComplex l E X n).obj Q) :=
  (finiteHomNuChainTensor_existsUnique l E X n P Q).choose


end WeilConjectures
