/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.NumberTheory.Padics.FiniteCoefficientFields
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic

/-!
# Comparison of the two finite integral coefficient conventions

Source: Mathlib `spectralNorm_unique_field_norm_ext`, applied to the coefficient
conventions in blueprint `det-lem-int-integral-heart-triangulated`.
(blueprint: lem-int-integral-coefficient-ring-comparison)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.ProEtale

/-- A finite extension with its spectral norm has the same condensed integer ring as
its image inside the fixed algebraic closure. Source: the uniqueness of the extended
p-adic absolute value and the continuous-function construction of condensed coefficients.
Proof: choose an algebra embedding into the algebraic closure and take its field range.
The range is finite over the base field. The resulting algebra equivalence is isometric
by uniqueness of the extended absolute value. Restrict it to the closed unit balls,
using the defining membership theorem for coefficientExtensionIntegers. It is a
homeomorphism of rings. Postcomposition on each profinite set gives inverse natural
ring maps, hence an isomorphism of commutative monoid objects in condensed abelian groups.
(blueprint: lem-int-integral-coefficient-ring-comparison). -/
theorem integralCoefficientRingComparison (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E] :
    let := spectralNorm.normedField (Padic ℓ) E
    ∃ F : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ),
      Nonempty (Mon.mk (Profinite.continuousMapRingObj.{u}
        (Padic.coefficientExtensionIntegers ℓ E)) ≅
        Mon.mk (Profinite.padicIntegersRingObj.{u} ℓ F.val)) := by
  classical
  let := spectralNorm.normedField (Padic ℓ) E
  let f : E →ₐ[Padic ℓ] PadicAlgCl ℓ := IsAlgClosed.lift
  let e : E ≃ₐ[Padic ℓ] f.fieldRange := f.equivFieldRange
  let : FiniteDimensional (Padic ℓ) f.fieldRange := e.toLinearEquiv.finiteDimensional
  let F : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ) := ⟨f.fieldRange, inferInstance⟩
  let A : AbsoluteValue E ℝ :=
    { toFun := fun x ↦ ‖f x‖
      map_mul' := fun x y ↦ by simp only [map_mul, norm_mul]
      nonneg' := fun x ↦ norm_nonneg _
      eq_zero' := fun x ↦ by simp only [norm_eq_zero, map_eq_zero]
      add_le' := fun x y ↦ by simpa only [map_add] using norm_add_le (f x) (f y) }
  have hnorm (x : E) : ‖f x‖ = ‖x‖ := by
    exact spectralNorm_unique_field_norm_ext (K := Padic ℓ) (L := E) (f := A)
      (fun z ↦ by
        change ‖f (algebraMap (Padic ℓ) E z)‖ = ‖z‖
        rw [f.commutes]
        exact PadicAlgCl.norm_extends ℓ z) x
  have hO (x : E) : x ∈ Padic.coefficientExtensionIntegers ℓ E ↔ ‖x‖ ≤ 1 := by
    exact (Padic.extension_integers_dvr ℓ E (Padic.coefficientExtensionAbsoluteValue ℓ E)
      (spectralNorm_extends (K := Padic ℓ) (L := E))).choose_spec.choose_spec.1 x
  let _ := PadicAlgCl.normedFieldOfAlgebra ℓ F.val
  let eO : Padic.coefficientExtensionIntegers ℓ E ≃+* PadicAlgCl.integers ℓ F.val :=
    { toFun := fun x ↦ ⟨e x, by
        rw [PadicAlgCl.mem_integers_iff]
        change ‖f x‖₊ ≤ 1
        exact_mod_cast (hnorm x).symm ▸ (hO x).mp x.property⟩
      invFun := fun x ↦ ⟨e.symm x, by
        rw [hO]
        have h := x.property
        rw [PadicAlgCl.mem_integers_iff] at h
        have heq : f (e.symm x) = (x.val : PadicAlgCl ℓ) := by
          change (e (e.symm x) : PadicAlgCl ℓ) = _
          rw [e.apply_symm_apply]
        rw [← hnorm, heq]
        exact_mod_cast h⟩
      left_inv := fun x ↦ Subtype.ext (e.symm_apply_apply x.val)
      right_inv := fun x ↦ Subtype.ext (e.apply_symm_apply x.val)
      map_mul' := fun x y ↦ Subtype.ext (map_mul e x.val y.val)
      map_add' := fun x y ↦ Subtype.ext (map_add e x.val y.val) }
  have hcont : Continuous eO := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    have hf : Isometry f := AddMonoidHomClass.isometry_of_norm f hnorm
    exact hf.continuous.comp continuous_subtype_val
  have hcont' : Continuous eO.symm := by
    have he : Isometry eO := by
      apply AddMonoidHomClass.isometry_of_norm eO
      intro x
      exact hnorm x
    exact (show IsometryEquiv _ _ from ⟨eO.toEquiv, he⟩).symm.continuous
  let eS : Profinite.continuousMapRingSheaf.{u} (Padic.coefficientExtensionIntegers ℓ E) ≅
      Profinite.padicIntegersCondensedRing.{u} ℓ F.val :=
    { hom := Profinite.continuousMapRingSheafMap eO.toRingHom hcont
      inv := Profinite.continuousMapRingSheafMap eO.symm.toRingHom hcont'
      hom_inv_id := by
        ext S x
        apply ULift.ext
        apply ContinuousMap.ext
        intro t
        change eO.symm (eO (x.down t)) = x.down t
        exact eO.symm_apply_apply _
      inv_hom_id := by
        ext S x
        apply ULift.ext
        apply ContinuousMap.ext
        intro t
        change eO (eO.symm (x.down t)) = x.down t
        exact eO.apply_symm_apply _ }
  let eC := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso eS
  have : IsMonHom eC.hom :=
    inferInstanceAs (IsMonHom ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map eS.hom))
  exact ⟨F, ⟨Mon.mkIso' eC⟩⟩

end AlgebraicGeometry.ProEtale
