/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import Mathlib.RingTheory.TensorProduct.Quotient

/-! # Exactness on affine sections for algebra reduction along a closed immersion

## References

* Stacks Project, Tags 01I9 and 01BJ
-/

@[expose] public section

universe u

open CategoryTheory Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option hygiene false in
local notation "𝒪⁎" g:max => Under.mk (⟨(g).c⟩ : Scheme.sheaf _ ⟶
  (TopCat.Sheaf.pushforward CommRingCat.{u} (g).base).obj (Scheme.sheaf _))

/-- An adjoint algebra reduction is surjective on affine sections, with the expected kernel
(Stacks, Tags 01I9 and 01BJ). -/
theorem closedImmersion_algebra_sections_exact
    {X Z Y : Scheme.{u}} (j : Z ⟶ X) [IsClosedImmersion j] (p : Y ⟶ Z)
    (B : X.CommAlgebraSheaf) [B.toModule.IsQuasicoherent]
    (α : (Scheme.Modules.tensorPullback j).obj B.toModule ≅
      (Scheme.Modules.pushforward p).obj (SheafOfModules.unit Y.ringCatSheaf))
    (b : B ⟶ 𝒪⁎(p ≫ j))
    (hb : ∀ (U : X.Opens) (x : B.right.obj.obj (op U)),
      (b.right.hom.app (op U)).hom x =
        ((Scheme.Modules.pushforwardComp p j).hom.app
          (SheafOfModules.unit Y.ringCatSheaf)).app U
            (((Scheme.Modules.pushforward j).map α.hom).app U
              (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction j)).unit.app
                B.toModule).app U x)))
    (U : X.Opens) (hU : IsAffineOpen U) :
    Function.Surjective (b.right.hom.app (op U)).hom ∧
      RingHom.ker (b.right.hom.app (op U)).hom =
        (RingHom.ker (j.app U).hom).map (B.hom.hom.app (op U)).hom := by
  classical
  let R : Type u := Γ(X, U)
  let S : Type u := Γ(Z, j ⁻¹ᵁ U)
  let T : Type u := B.right.obj.obj (op U)
  let φ : R →+* S := (j.appLE U (j ⁻¹ᵁ U) le_rfl).hom
  let : Algebra R S := φ.toAlgebra
  let : Algebra R T := (B.hom.hom.app (op U)).hom.toAlgebra
  have hφ : Function.Surjective φ := by
    simpa [φ, Scheme.Hom.appLE]
      using j.app_surjective U hU
  let qe : (R ⧸ (RingHom.ker φ)) ≃ₐ[R] S :=
    Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R S) hφ
  let : ∀ F : X.Modules, Module R Γ((Scheme.Modules.tensorPullback j).obj F, j ⁻¹ᵁ U) :=
    fun F ↦ Module.compHom _ φ
  obtain ⟨c, hc, _, hcp, _⟩ := Scheme.Modules.exists_tensorPullback_affine_sections
    j ⟨U, hU⟩ ⟨j ⁻¹ᵁ U, hU.preimage j⟩ le_rfl
  let qc := c B.toModule inferInstance
  let ce := LinearEquiv.ofBijective qc (hc B.toModule inferInstance)
  let te := TensorProduct.congr (LinearEquiv.refl R T) qe.toLinearEquiv
  let de := (Algebra.TensorProduct.quotIdealMapEquivTensorQuot T (RingHom.ker φ)).toLinearEquiv
  let d := de.toAddEquiv.trans (te.toAddEquiv.trans ce.toAddEquiv)
  have hd (x : T) : d (Ideal.Quotient.mk _ x) =
      (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction j)).unit.app
        B.toModule).app U x) := by
    change qc (x ⊗ₜ[R] (qe (1 : R ⧸ RingHom.ker φ))) = _
    rw [map_one]
    have hh := hcp B.toModule inferInstance x 1
    simp only [one_smul, homOfLE_refl, op_id] at hh
    have hid := ((Scheme.Modules.tensorPullback j).obj B.toModule).presheaf.map_id
      (op (j ⁻¹ᵁ U))
    rw [hid] at hh
    exact hh
  let ai := (SheafOfModules.evaluation Z.ringCatSheaf (op (j ⁻¹ᵁ U))).mapIso α
  let ae := ai.toLinearEquiv.toAddEquiv
  let d' := d.trans ae
  have hd' (x : T) : d' (Ideal.Quotient.mk _ x) =
      (b.right.hom.app (op U)).hom x := by
    change α.hom.app (j ⁻¹ᵁ U) (d (Ideal.Quotient.mk _ x)) = _
    rw [hd]
    exact (hb U x).symm
  constructor
  · intro y
    obtain ⟨z, hz⟩ := d'.surjective y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨x, (hd' x).symm.trans hz⟩
  · ext x
    change (b.right.hom.app (op U)).hom x = 0 ↔
      x ∈ (RingHom.ker (j.app U).hom).map (B.hom.hom.app (op U)).hom
    rw [← hd', ← d'.map_zero, d'.injective.eq_iff]
    have he : (RingHom.ker φ).map (algebraMap R T) =
        (RingHom.ker (j.app U).hom).map (B.hom.hom.app (op U)).hom := by
      simp [φ, Scheme.Hom.appLE]
      rfl
    exact (Ideal.Quotient.eq_zero_iff_mem).trans (by rw [he])

end AlgebraicGeometry
