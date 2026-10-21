/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q59
-/
module

public import Sheaf.Paper.FiniteCoefficientSiteScalarArrow

/-! # Finite coefficient change for internal Hom

Source: blueprint sec-six-functors/sk-prop-sf-biduality-general,
node thm-coef-finite-hom (blueprint: def-sf-finite-coefficient-site-chain-tensor).
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

/-- The termwise inverse image, retaining the original small site's sizes.
Source: blueprint site formula (blueprint: def-sf-finite-coefficient-site-chain-tensor). -/
def finiteHomNuComplex (n : ℕ) :=
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
def FiniteHomNuChainTensorNormalization (n : ℕ)
    (P Q : CochainComplex (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))) ℤ)
    (e : (finiteHomNuComplex l E X n).obj (HomologicalComplex.tensorObj P Q) ≅
      (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology X)
        (integralCoefficientCommRingSheaf l E X n)).obj
        ((finiteHomNuComplex l E X n).obj P, (finiteHomNuComplex l E X n).obj Q)) : Prop :=
  ∀ (p q k : ℤ) (h : p + q = k) (U : X.Etale)
  (x : (P.X p).obj.obj (op U)) (y : (Q.X q).obj.obj (op U)),
  ∃ (x' : (((finiteHomNuComplex l E X n).obj P).X p).val.obj (op (X.toProEt.obj U)))
    (y' : (((finiteHomNuComplex l E X n).obj Q).X q).val.obj (op (X.toProEt.obj U)))
    (z : (((finiteHomNuComplex l E X n).obj
      (HomologicalComplex.tensorObj P Q)).X k).val.obj (op (X.toProEt.obj U))),
    HEq x' (finiteHomNuSection l E X n (P.X p) U x) ∧
    HEq y' (finiteHomNuSection l E X n (Q.X q) U y) ∧
    HEq z (finiteHomNuSection l E X n ((HomologicalComplex.tensorObj P Q).X k) U
      (finiteHomEtaleTotalSection l E X n P Q p q k h U x y)) ∧
    HEq (((e.hom.f k).val.app (op (X.toProEt.obj U))) z)
      (coefficientTensorGenerator.{u, u + 1, u} (Scheme.ProEt.topology X)
        (integralCoefficientCommRingSheaf l E X n)
        ((finiteHomNuComplex l E X n).obj P) ((finiteHomNuComplex l E X n).obj Q)
        p q k h (op (X.toProEt.obj U)) x' y')

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
  sorry

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
