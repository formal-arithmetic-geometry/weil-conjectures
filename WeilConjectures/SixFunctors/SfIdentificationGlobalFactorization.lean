/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.SfIdentificationData

/-! # Normalized scalar global duality

Source: the current smooth Poincare identification proof, step 2.
This module realizes node `lem-sf-identification-global-factorization`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [local instance 10000] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.PurityTransport
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace WeilConjectures.SixFunctors

variable (ell : ℕ) [Fact ell.Prime]
  (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
  (Λ : ScalarSixRing.{u}) (c : PurityTransport.Coefficient ell)
  (e : c.bundled.{u} ell ≅ Λ)
  (X : Over (Spec (.of D.k))) [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] (d : ℕ)
  [SmoothOfRelativeDimension d X.hom] (cf : Compactification X.hom)
  (K : ConstantModelConstructibleFiniteTor Λ.X X.left)

/-- The purity-normalized pairing factors through the Verdier isomorphism and the
ordinary-sections image of `j`. This is the independent naturality calculation
following the global isomorphism (blueprint: lem-sf-identification-global-factorization).
Proof: precompose the mixed-support cup with the sections map of `j`; naturality
of tensor--Hom currying, the evaluation square `heval`, and the trace equation
`htrace` identify the resulting transpose with the displayed composite. -/
theorem sfIdentificationGlobalFactorization
    [IsAlgClosed D.k]
    (hs : (constantModelBoundedConstructible Λ.X (Spec (.of D.k)) ⊓
      DerivedCategory.finiteTorAmplitude _) (𝟙_ _))
    (R : ScalarExceptionalAdjoint Λ cf)
    (γ : (smoothTraceCoefficientLine ell Λ c e X.left d) ⟦2 * (d : ℤ)⟧ ≅
      (R.upper.obj ⟨𝟙_ _, hs⟩).obj)
    (j : (((ihom K.obj).obj (𝟙_ _) ⊗
      smoothTraceCoefficientLine ell Λ c e X.left d) ⟦2 * (d : ℤ)⟧) ≅
      (ihom K.obj).obj (R.upper.obj ⟨𝟙_ _, hs⟩).obj)
    (htrace : (rightDerivedLowerShriekOfCompactification Λ.X cf).map γ.hom ≫
        R.counit ⟨𝟙_ _, hs⟩ =
      smoothTraceUnitOfCoefficientIso ell Λ c e D hEll (pairingSmoothDatum D X d cf))
    (heval : K.obj ◁ j.hom ≫ (ihom.ev K.obj).app (R.upper.obj ⟨𝟙_ _, hs⟩).obj =
      ((tensorLeft K.obj).commShiftIso (2 * (d : ℤ))).hom.app _ ≫
        (shiftFunctor _ (2 * (d : ℤ))).map
          (pairingTwistedEvaluation Λ.X K.obj
            (smoothTraceCoefficientLine ell Λ c e X.left d)) ≫ γ.hom)
    (g : (pairingOrdinarySections Λ.X D.k X.hom).obj
        ((ihom K.obj).obj (R.upper.obj ⟨𝟙_ _, hs⟩).obj) ≅
      (ihom ((pairingCompactSections Λ.X D.k cf).obj K.obj)).obj (𝟙_ _))
    (hg : g.hom = MonoidalClosed.curry
        (identificationVerdierPairing D Λ X cf K _ (R.counit ⟨𝟙_ _, hs⟩))) :
    MonoidalClosed.curry (identificationPairing ell D hEll Λ c e X d cf K) =
        ((pairingOrdinarySections Λ.X D.k X.hom).commShiftIso
          (2 * (d : ℤ))).inv.app _ ≫
          (pairingOrdinarySections Λ.X D.k X.hom).map j.hom ≫ g.hom := by sorry


end WeilConjectures.SixFunctors
