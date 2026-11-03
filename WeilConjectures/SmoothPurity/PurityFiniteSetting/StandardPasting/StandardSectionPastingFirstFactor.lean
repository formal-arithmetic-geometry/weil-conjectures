/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.StandardPasting.StandardSectionPastingData
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.DiagonalExchangeNaturality
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.DiagonalPasting.PurityDiagonalOpenRestriction

/-! # The first concrete affine section-pasting factor
(blueprint: lem-route-standard-section-pasting-base-change-first-factor).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting.StandardPasting
open DiagonalPasting

set_option maxHeartbeats 1500000 in
-- Derived pullback compositor expressions require a larger elaboration budget.
/-- The first input is compatible with the actual affine base-change mates.
Source: composition coherence Step 1, the first factor in Step 5 of the standard-pair
base-change calculation (blueprint: lem-route-standard-section-pasting-base-change-first-factor).
Proof: horizontal mate pasting in the rectangle with sides first and affine-space map
identifies the two beta composites. Pull this equality along the new total zero section.
Pullback associativity and naturality of the section compositor give the equation for
inverse first inputs. Cancel the first input isomorphisms to obtain the displayed equation.
All coordinate identities and cancellations include zero-dimensional blocks and empty bases.
-/
theorem first_factor_identity (P : PurityFiniteSetting.{u})
    [HasInvertibleExponent P.Coefficient (Spec (.of P.field.k))]
    {B B' : Scheme.{u}} [IsNoetherian B] [IsNoetherian B']
    (d e : ℕ) (b : B' ⟶ B) (aB : B ⟶ Spec (.of P.field.k)) :
    (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor.mapIso
        (firstInput P d e B aB) ≪≫ firstChange P d e b aB =
      baseChange P d b aB ≪≫ firstInput P d e B' (b ≫ aB) := by
  let := (affineGeometry d e B).2.2.2.2.1
  let := (affineGeometry d e B).2.2.2.2.2.1
  let := (affineGeometry d e B).2.2.2.2.2.2.1
  let := (affineGeometry d e B).2.2.2.2.2.2.2.1
  let := (affineGeometry d e B).2.2.2.2.2.2.2.2
  let := (affineGeometry d e B').2.2.2.2.1
  let := (affineGeometry d e B').2.2.2.2.2.1
  let := (affineGeometry d e B').2.2.2.2.2.2.1
  let := (affineGeometry d e B').2.2.2.2.2.2.2.1
  let := (affineGeometry d e B').2.2.2.2.2.2.2.2
  let bd := beta P.Coefficient P d (AffineSpace.isPullback_map b) (pr d B ≫ aB)
  let bq := beta P.Coefficient P d (geometry d e b).2.2 (pr (d+e) B ≫ aB)
  let c := beta P.Coefficient P d (affineGeometry d e B).1 (pr d B ≫ aB)
  let c' := beta P.Coefficient P d (affineGeometry d e B').1 (pr d B' ≫ b ≫ aB)
  have hb := dualizing_base_rectangle P.Coefficient (affineGeometry d e B).1
    (AffineSpace.isPullback_map (n := ULift.{u} (Fin d)) b)
    (geometry d e b).2.2 (affineGeometry d e B').1
    (geometry d e b).2.1 (AffineSpace.map_over b)
  have hb' :
      (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
        (AffineSpace.map (ULift.{u} (Fin (d+e))) b)).leftDerivedFunctor.map c.hom ≫
          bq.hom =
      (Etale.sectionCoherencePullbackIso P.Coefficient
        (AffineSpace.map (ULift.{u} (Fin (d+e))) b) (first d e B) (first d e B')
        (AffineSpace.map (ULift.{u} (Fin d)) b) (geometry d e b).2.1 _).hom ≫
      (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
        (first d e B')).leftDerivedFunctor.map bd.hom ≫ c'.hom := by
    simpa only [c, c', bq, bd, beta, asIso_hom, Etale.ordinaryFinitePullback,
      Etale.sectionCoherencePullbackIso, Iso.trans_hom, Iso.symm_hom,
      Iso.app_hom, Category.assoc] using hb
  have hx := section_composite_natural P.Coefficient b
    (zero (d+e) B) (zero (d+e) B') (zero d B) (zero d B')
    (first d e B) (first d e B') (AffineSpace.map (ULift.{u} (Fin (d+e))) b)
    (AffineSpace.map (ULift.{u} (Fin d)) b)
    (AffineSpace.zeroSection_comp_map b).symm
    (AffineSpace.zeroSection_comp_map b).symm (geometry d e b).2.1
    (affineGeometry d e B).2.1 (affineGeometry d e B').2.1
    c c' bq bd hb'
  let U := (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor
  have hc : U.map (firstInput P d e B aB).inv ≫ (baseChange P d b aB).hom =
      (firstChange P d e b aB).hom ≫ (firstInput P d e B' (b ≫ aB)).inv := by
    simpa only [firstInput, baseChange, firstChange, c, c', bq, bd, U,
      Iso.trans_inv, Iso.trans_hom, Iso.app_inv, Functor.mapIso_inv,
      Functor.mapIso_hom, Functor.map_comp, Category.assoc] using hx
  apply Iso.ext
  apply (cancel_mono (firstInput P d e B' (b ≫ aB)).inv).1
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]
  apply (cancel_epi (U.map (firstInput P d e B aB).inv)).1
  change U.map (firstInput P d e B aB).inv ≫
      U.map (firstInput P d e B aB).hom ≫ (firstChange P d e b aB).hom ≫
        (firstInput P d e B' (b ≫ aB)).inv =
    U.map (firstInput P d e B aB).inv ≫ (baseChange P d b aB).hom
  rw [← U.map_comp_assoc, Iso.inv_hom_id, U.map_id, Category.id_comp]
  exact hc.symm

end WeilConjectures.PurityFiniteSetting.StandardPasting
