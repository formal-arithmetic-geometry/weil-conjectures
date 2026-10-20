/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B5
-/
module

public import Sheaf.Paper.ProEtaleRealizedExchangeCompatibility

/-!
# Isomorphism detection for realized pro-etale exchange

The explicit endpoint comparisons and scalar restriction reduce this to the
canonical exchange compatibility, independently of proper base change.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

attribute [local irreducible] proEtaleAmbientRingedExchange
  proEtaleConstantSections proEtaleRealizedCoordinates proEtaleRealizedCoefficientIso

/-- The actual ringed exchange is invertible exactly when its fixed-scalar realization is.
Source: Stacks Tags 07A7 and 00YV
(blueprint: lem-weil-pbc-realized-exchange-normalization).
Proof: specialize the structural compatibility to K, obtaining an isomorphism between
the arrow mapped by the coordinates functor and the fixed-scalar exchange arrow.
The coordinates functor reflects isomorphisms. Conjugation by the two explicit
endpoint isomorphisms gives both implications. -/
theorem proEtaleRealizedExchange_isIso_iff
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)
    (R_X : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (R_Y : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (R_X' : Sheaf (ProEt.topology X') CommRingCat.{u + 1})
    (R_Y' : Sheaf (ProEt.topology Y') CommRingCat.{u + 1})
    (eX : etaleOriginRing X Λ ≅ R_X) (eY : etaleOriginRing Y Λ ≅ R_Y)
    (eX' : etaleOriginRing X' Λ ≅ R_X') (eY' : etaleOriginRing Y' Λ ≅ R_Y')
    (c_f : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R_Y ≅ R_X)
    (c_g : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R_Y ≅ R_Y')
    (c_g' : (proEtaleSheafInverseImage g' CommRingCat.{u + 1}).obj R_X ≅ R_X')
    (c_f' : (proEtaleSheafInverseImage f' CommRingCat.{u + 1}).obj R_Y' ≅ R_X')
    (hf : c_f = proEtaleRealizedCoefficientIso Λ f eY eX)
    (hg : c_g = proEtaleRealizedCoefficientIso Λ g eY eY')
    (hg' : c_g' = proEtaleRealizedCoefficientIso Λ g' eX eX')
    (hf' : c_f' = proEtaleRealizedCoefficientIso Λ f' eY' eX')
    (hcoeff : HEq (proEtaleRingCompositeCoefficients g' f R_Y R_X R_X' c_f c_g')
      (proEtaleRingCompositeCoefficients f' g R_Y R_Y' R_X' c_g c_f'))
    (K : DerivedCategory (proEtaleRingModules X R_X)) :
    IsIso ((proEtaleAmbientRingedExchange sq R_X R_Y R_X' R_Y'
      c_f c_g c_g' c_f' hcoeff).app K) ↔
    IsIso ((ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app
      ((proEtaleRealizedCoordinates Λ X R_X eX).obj K)) := by
  subst c_f c_g c_g' c_f'
  have h := congrArg (fun t ↦ t.app K)
    (proEtaleRealizedExchange_compatibility Λ sq R_X R_Y R_X' R_Y'
      eX eY eX' eY' hcoeff)
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at h
  rw [← isIso_iff_of_reflects_iso _ (proEtaleRealizedCoordinates Λ Y' R_Y' eY')]
  exact (MorphismProperty.isomorphisms _).arrow_mk_iso_iff
    (Arrow.isoMk
      ((proEtaleRealizedExchangeSourceIso Λ f g R_X R_Y R_Y' eX eY eY').app K)
      ((proEtaleRealizedExchangeTargetIso Λ g' f' R_X R_X' R_Y' eX eX' eY').app K)
      h.symm)

end AlgebraicGeometry.Scheme
