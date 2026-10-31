/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateTailFactorwisePullback

/-! # Normalized coefficient comparisons for an old-coordinate list -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.ProEtale.AffineZeroPurity
open AffineSpacePurity

/-- The chosen Cartesian square for a partial old-coordinate support.
Source: ordered exterior product in the affine-space zero-section proof.
(blueprint: lem-pur-coordinate-tail-coefficient-pullback). -/
def tailPartialSquare (B : Scheme.{u}) (r : ℕ) (is : List (Fin r)) :
    ChosenCartesianSquare (successorPartialProjection B r is)
      (supportMap B (r + 1) (is.map Fin.succ)) (supportMap B r is)
      (lastProjection B r) where
  toCommSq := (successorPartial_isPullback B r is).toCommSq
  isoPullback := (successorPartial_isPullback B r is).isoPullback
  hom_fst := (successorPartial_isPullback B r is).isoPullback_hom_fst
  hom_snd := (successorPartial_isPullback B r is).isoPullback_hom_snd

/-- Exact pullback on the literal partial-support sources.
Source: ordered exterior product in the affine-space zero-section proof.
(blueprint: lem-pur-coordinate-tail-coefficient-pullback). -/
def tailPartialSourcePullback (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (r : ℕ) (is : List (Fin r)) :
    (inverseImage (setting P n).Coefficient (lastProjection B r)).obj
      (classSource P n B r is) ≅ classSource P n B (r + 1) (is.map Fin.succ) :=
  (inverseImage (setting P n).Coefficient (lastProjection B r)).mapIso
      (eqToIso (classSource_eq P n B r is)) ≪≫
    pullbackSingle (setting P n).Coefficient (lastProjection B r) _ _
      ((setting P n).functorialCupExchange true (supportMap B r is)
        (supportMap B (r + 1) (is.map Fin.succ)) (lastProjection B r)
        (successorPartialProjection B r is) (tailPartialSquare B r is)) ≪≫
    (eqToIso (classSource_eq P n B (r + 1) (is.map Fin.succ))).symm

/-- A binary ordered coordinate step with a freely supplied previous map and boundary.
Source: ordered exterior product in the affine-space zero-section proof.
(blueprint: lem-pur-coordinate-tail-coefficient-pullback). -/
def tailProductStep (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k)) (c : ℕ)
    (i : Fin c) (is : List (Fin c)) (m : ℕ)
    (α : classSource P n B c is ⟶ target P n (iteratedAffineLine B c) m)
    (β : (cupSingle (setting P n) (iteratedAffineLine B c)).obj
      ((lowerStar (ModuleCat.{u + 1} (setting P n).Coefficient) (inclusion B c i)).obj
        ((setting P n).constant (divisor B c i))) ⟶
      shiftedLine (setting P n) (iteratedAffineLine B c)) :
    classSource P n B c (i :: is) ⟶ target P n (iteratedAffineLine B c) (m + 1) :=
  coordinateProductTransport (classSource_cons P n B c i is)
    (zeroCupTensor (setting P n) (supportMap B c is) (inclusion B c i)
      ⟨_, target_plus P n _ (towerBase aB c) m⟩
      ⟨_, boundary_plus P n _⟩
      (coordinateProductStart (classSource_eq P n B c is).symm α) β)
    (target_succ P n (iteratedAffineLine B c) m)

/-- The empty product written without the fold.
Source: ordered exterior product in the affine-space zero-section proof.
(blueprint: lem-pur-coordinate-tail-coefficient-pullback). -/
def tailProductUnit (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u}) (c : ℕ) :
    classSource P n B c [] ⟶ target P n (iteratedAffineLine B c) 0 :=
  coordinateProductStart (classSource_nil P n B c)
    ((cupSingle (setting P n) (iteratedAffineLine B c)).map
      ((lowerStarId (ModuleCat.{u + 1} (setting P n).Coefficient)
        (iteratedAffineLine B c)).hom.app
          ((setting P n).constant (iteratedAffineLine B c))))

/-- Canonical inverse image preserves the empty coefficient unit and a binary
supported tensor cup, and the full-support normalization commutes with it.
Source: ordered exterior product in the affine-space zero-section proof.
(blueprint: lem-pur-coordinate-tail-coefficient-pullback).
Proof: the empty exchange preserves the restricted constant unit by its defining
normalization. For a binary cup, inverse image carries coefficient multiplication
to coefficient multiplication because both maps multiply the two restricted
constant sections on the Cartesian intersection. The restriction maps are epic,
so these maps agree. Apply the exact single and tensor comparisons, then tensor
naturality for the arbitrary maps. The target comparison is actionPullbackIso's
successor clause. For the full support, restriction normalization identifies the
support-map composite exchange with the partial exchange; apply the single
functor and its pullback comparison and transport the list length. -/
theorem coordinate_tail_coefficient_pullback (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k)) (r : ℕ) :
    ((tailPartialSourcePullback P n B r []).inv ≫
        (inverseImage (setting P n).Coefficient (lastProjection B r)).map
          (tailProductUnit P n B r) ≫
        (targetPullbackIso P n (lastProjection B r) (towerBase aB r) 0).hom =
      tailProductUnit P n B (r + 1)) ∧
    (∀ (i : Fin r) (is : List (Fin r)) (m : ℕ)
      (α : classSource P n B r is ⟶ target P n (iteratedAffineLine B r) m)
      (β : (cupSingle (setting P n) (iteratedAffineLine B r)).obj
        ((lowerStar (ModuleCat.{u + 1} (setting P n).Coefficient) (inclusion B r i)).obj
          ((setting P n).constant (divisor B r i))) ⟶
        shiftedLine (setting P n) (iteratedAffineLine B r)),
      (tailPartialSourcePullback P n B r (i :: is)).inv ≫
          (inverseImage (setting P n).Coefficient (lastProjection B r)).map
            (tailProductStep P n B aB r i is m α β) ≫
          (targetPullbackIso P n (lastProjection B r) (towerBase aB r) (m + 1)).hom =
        tailProductStep P n B aB (r + 1) i.succ (is.map Fin.succ) m
          ((tailPartialSourcePullback P n B r is).inv ≫
            (inverseImage (setting P n).Coefficient (lastProjection B r)).map α ≫
            (targetPullbackIso P n (lastProjection B r) (towerBase aB r) m).hom)
          ((tailDivisorSourcePullback P n B r i).inv ≫
            (inverseImage (setting P n).Coefficient (lastProjection B r)).map β ≫
            (shiftedLinePullback (setting P n) (lastProjection B r)
              (towerBase aB r)).hom)) ∧
    ((successorTailSourcePullback P n B r).inv ≫
        (inverseImage (setting P n).Coefficient (lastProjection B r)).map
          (supportedClass P n B aB r) ≫
        (targetPullbackIso P n (lastProjection B r) (towerBase aB r) r).hom =
      (tailPartialSourcePullback P n B r (List.finRange r)).inv ≫
        (inverseImage (setting P n).Coefficient (lastProjection B r)).map
          (product P n B aB r (List.finRange r)) ≫
        (targetPullbackIso P n (lastProjection B r) (towerBase aB r)
          (List.finRange r).length).hom ≫
        eqToHom (congrArg (target P n (iteratedAffineLine B (r + 1)))
          (@List.length_finRange r))) := by
  sorry

end AlgebraicGeometry.ProEtale.AffineZeroPurity
