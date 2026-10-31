/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FieldShriekSystemModels
import Mathlib.CategoryTheory.Functor.OfSequence

/-! # Actual coefficient maps of finite field inclusions

The maps on the ell-power quotients and their inverse towers are induced by the
integral inclusion, rather than chosen from a mere existence statement.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.FieldShriekSystem

attribute [local irreducible] constantSheaf

variable (P : PurityFiniteSetting.{u}) {E F : Index P} (h : E ≤ F)

private def inclusion :=
  integralScalarIntegerInclusion P.coefficients.l E.val F.val
    (IntermediateField.inclusion h)

private theorem ideal_map (n : ℕ) :
    Ideal.map (inclusion P h) (spEllIdeal P.coefficients.l E.val ^ (n + 1)) =
      spEllIdeal P.coefficients.l F.val ^ (n + 1) := by
  simp only [Ideal.map_pow, spEllIdeal, Ideal.map_span, Set.image_singleton,
    map_natCast]

private def quotient (n : ℕ) :
    SpTowerShriek.R P.coefficients.l E.val n →+*
      SpTowerShriek.R P.coefficients.l F.val n :=
  Ideal.quotientMap _ (inclusion P h)
    (Ideal.map_le_iff_le_comap.mp (le_of_eq (ideal_map P h n)))

private theorem reduction (n : ℕ) :
    (quotient P h n).comp
        (Ideal.Quotient.factorPowSucc (spEllIdeal P.coefficients.l E.val) (n + 1)) =
      (Ideal.Quotient.factorPowSucc (spEllIdeal P.coefficients.l F.val) (n + 1)).comp
        (quotient P h (n + 1)) := by
  apply Ideal.Quotient.ringHom_ext
  ext x
  rfl

private def lifted (n : ℕ) :
    CommRingCat.of (ULift.{u + 1} (SpTowerShriek.R P.coefficients.l E.val n)) ⟶
      CommRingCat.of (ULift.{u + 1} (SpTowerShriek.R P.coefficients.l F.val n)) :=
  CommRingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp ((quotient P h n).comp ULift.ringEquiv.toRingHom))

private theorem lifted_reduction (n : ℕ) :
    CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      ((Ideal.Quotient.factorPowSucc (spEllIdeal P.coefficients.l E.val) (n + 1)).comp
        ULift.ringEquiv.toRingHom)) ≫ lifted P h n =
      lifted P h (n + 1) ≫ CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
        ((Ideal.Quotient.factorPowSucc (spEllIdeal P.coefficients.l F.val) (n + 1)).comp
          ULift.ringEquiv.toRingHom)) := by
  ext x
  exact RingHom.congr_fun (reduction P h n) x.down

set_option maxHeartbeats 4000000 in
-- Comparing the actual constant-sheaf sequence maps unfolds the quotient transitions.
private def tower (T : Scheme.{u}) :
    spCoefficientCommRings P.coefficients.l E.val T ⟶
      spCoefficientCommRings P.coefficients.l F.val T :=
  NatTrans.ofOpSequence
    (fun n ↦ (constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}).map
      (lifted P h n)) (fun n ↦ by
        simp only [spCoefficientCommRings, Functor.ofOpSequence_map_homOfLE_succ]
        dsimp only [Functor.ofOpSequence, Functor.leftOp, Functor.ofSequence]
        exact ((constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}).map_comp
          _ _).symm.trans (((constantSheaf (Scheme.ProEt.topology T)
            CommRingCat.{u + 1}).congr_map (lifted_reduction P h n)).trans
              ((constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}).map_comp _ _)))

/-- The integral inclusion induces the specified residue-class maps and a morphism
of their constant-sheaf towers.

Source: latest blueprint, field-extension towers proof (2), coefficient square
(blueprint: lem-route-field-shriek-system-coefficient-construction).

Proof: the integral inclusion sends the natural number ell to itself, so the image
of the principal ell ideal and each positive power is the corresponding target ideal.
The quotient universal property therefore induces each ring map. Both composites with
a successor reduction send a residue class to the class of its integral image. Lift
the maps through ULift and apply the constant-sheaf functor. The successor squares give
a natural transformation of inverse sequences; its components have the required formula. -/
theorem field_shriek_coefficients_exists : Nonempty (Coefficients P E F h) := by
  exact ⟨{ quotient := quotient P h
           quotient_mk := fun _ _ ↦ rfl
           tower := tower P h
           tower_app := fun _ _ ↦ rfl }⟩

end AlgebraicGeometry.ProEtale.FieldShriekSystem
