/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.SfIdentificationData

/-! # Normalized scalar global duality

Source: the current smooth Poincare identification proof, step 2.
This module realizes node `lem-sf-identification-global-verdier-iso`.
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

/-- The normalized Verdier global-sections isomorphism exists and is the curry of
its canonical Verdier pairing. This isolates the native global-duality construction
from the subsequent purity factorization (blueprint: lem-sf-identification-global-verdier-iso).
Proof: realize the coefficient-point Verdier adjunction on the uncompleted scalar
module categories, then apply the tensor--Hom transpose to the mixed-support cup,
evaluation, and normalized exceptional counit. The resulting map is invertible by
restricted global Verdier duality. -/
theorem sfIdentificationGlobalVerdierIso
    [IsAlgClosed D.k]
    (hs : (constantModelBoundedConstructible Λ.X (Spec (.of D.k)) ⊓
      DerivedCategory.finiteTorAmplitude _) (𝟙_ _))
    (R : ScalarExceptionalAdjoint Λ cf) :
    ∃ g : (pairingOrdinarySections Λ.X D.k X.hom).obj
        ((ihom K.obj).obj (R.upper.obj ⟨𝟙_ _, hs⟩).obj) ≅
      (ihom ((pairingCompactSections Λ.X D.k cf).obj K.obj)).obj (𝟙_ _),
      g.hom = MonoidalClosed.curry
        (identificationVerdierPairing D Λ X cf K _ (R.counit ⟨𝟙_ _, hs⟩)) := by sorry

end WeilConjectures.SixFunctors
