/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomNativeClosed
public import WeilConjectures.AlgebraicGeometry.CoefficientPairingChange.InternalAdjunctionPairingChange
import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomEtaleBraidedEvaluation
import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomScalarTensorBraid

/-! # Native evaluation equation for scalar extension
Source: blueprint thm-coef-finite-hom, evaluation paragraph
(blueprint: lem-coef-finite-hom-native-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u a b c d w z
open CategoryTheory AlgebraicGeometry CategoryTheory.MonoidalCategory Opposite
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard

-- Retain named tensor fields instead of expanding the derived bifunctor.
set_option allowUnsafeReducibility true in
attribute [local irreducible] DerivedMonoidal.tensorObjAux
  DerivedMonoidal.whiskerLeftAux DerivedMonoidal.whiskerRightAux

-- Use the coefficient and sheaf braidings fixed in the ordinary derived tensor.
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000]
  GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall

attribute [local implicit_reducible] CategoryTheory.uniformProd
  Etale.sheafMonoidalCategory Etale.sheafBraidedCategory Etale.sheafMonoidalClosed
  ModuleCat.MonoidalCategory.symmetricCategory SymmetricCategory.ofFaithful

attribute [local implicit_reducible]
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

attribute [local implicit_reducible]
  DerivedCategory.monoidalClosed_of_hasFunctorialFlatResolution

-- Keep the faithful-transfer construction atomic after exposing the symmetric parent.
attribute [local irreducible] ModuleCat.MonoidalCategory.instBraidedCategory

attribute [local irreducible] DerivedCategory.monoidalClosed

set_option maxHeartbeats 1600000 in
-- The derived-instance conversions require additional kernel heartbeats.
end WeilConjectures

namespace WeilConjectures

/-- The native right-tensor evaluation equation for ordinary scalar extension.
Source: blueprint thm-coef-finite-hom, opening evaluation paragraph
(blueprint: lem-coef-finite-hom-native-evaluation).

Proof: tensor normalization identifies the scalar tensorator, and its monoidal
braid law gives the inverse braid square. Apply the generic braided evaluation
identity and unfold the ordinary tensor-Hom adjunction. This needs no finiteness
or invertibility of the internal-Hom comparison. -/
theorem finiteHom_native_evaluation {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u}) (K M : Etale.DerivedCategoryModule A X) :
    (finiteHomNativeDerivedClosed
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))).tensor.map
        (Prod.mkHom (Etale.CoefficientPairingChange.evaluationComparison φ X K M)
          (𝟙 ((Etale.scalarExtension φ X).obj K))) ≫
      (finiteHomNativeDerivedClosed
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))).evaluation
        ((Etale.scalarExtension φ X).obj K) ((Etale.scalarExtension φ X).obj M) =
      (Etale.etaleHomTensorComparison X φ
        (((Etale.derivedHom (ModuleCat A) X).obj (op K)).obj M) K).hom ≫
        (Etale.scalarExtension φ X).map
          ((finiteHomNativeDerivedClosed
            (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))).evaluation K M) := by
  exact finiteHom_etale_braided_evaluation (ModuleCat A) (ModuleCat B) X
    (Etale.scalarExtension φ X) K M
    (fun P Q ↦ (Etale.etaleHomTensorComparison X φ P Q).hom)
    (Etale.CoefficientPairingChange.evaluationComparison φ X K M)
    (finiteHom_scalar_tensor_braid φ X K
      (((Etale.derivedHom (ModuleCat A) X).obj (op K)).obj M)) rfl

end WeilConjectures
