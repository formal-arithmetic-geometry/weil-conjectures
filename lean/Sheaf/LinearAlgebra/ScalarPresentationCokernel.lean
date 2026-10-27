/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F8
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # Normalized scalar extension of a specified finite presentation

Source: Stacks Project, Tags 00DF and 03EK; Bhatt--Scholze, Proposition 6.8.14(2).
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace ModuleCat

private def scalarPowerIso {R T : Type u} [CommRing R] [CommRing T]
    (f : R →+* T) (n : ℕ) :
    (extendScalars f).obj (of R (Fin n → R)) ≅ of T (Fin n → T) := by
  letI := f.toAlgebra
  exact (TensorProduct.piScalarRight R T T (Fin n)).toModuleIso

private theorem scalarPowerIso_unit {R T : Type u} [CommRing R] [CommRing T]
    (f : R →+* T) (n : ℕ) (x : Fin n → R) :
    (scalarPowerIso f n).hom
      (ExtendRestrictScalarsAdj.Unit.map f x) = fun i ↦ f (x i) := by
  let := f.toAlgebra
  change TensorProduct.piScalarRight R T T (Fin n) (1 ⊗ₜ[R] x) = _
  rw [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
  funext i
  exact mul_one (f (x i))

private theorem scalarPowerIso_natural {R T : Type u} [CommRing R] [CommRing T]
    (f : R →+* T) {m n : ℕ} (D : Matrix (Fin n) (Fin m) R) :
    (extendScalars f).map (ofHom (Matrix.toLin' D)) ≫ (scalarPowerIso f n).hom =
      (scalarPowerIso f m).hom ≫ ofHom (Matrix.toLin' (D.map f)) := by
  apply ExtendScalars.hom_ext
  intro x
  change (scalarPowerIso f n).hom
      (ExtendRestrictScalarsAdj.Unit.map f (Matrix.toLin' D x)) =
    Matrix.toLin' (D.map f)
      ((scalarPowerIso f m).hom (ExtendRestrictScalarsAdj.Unit.map f x))
  rw [scalarPowerIso_unit, scalarPowerIso_unit]
  funext i
  simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, map_sum, map_mul]

/-- Scalar extension preserves a specified right-exact finite presentation, with its
quotient map normalized on the original basis vectors. No flatness or injectivity is
required. Source: Stacks Project, Tags 00DF and 03EK; Bhatt--Scholze,
Proposition 6.8.14(2).
(blueprint: lem-per-scalar-presentation-cokernel).

Proof: Exactness and surjectivity identify the given module with the categorical
cokernel of the relation matrix. Extension of scalars is left adjoint to restriction,
so it preserves this cokernel. The tensor finite-power isomorphism sends 1 tensor x
to the coordinatewise image of x. Naturality of that isomorphism identifies the
extended relation map with the coefficientwise image of the matrix. Transport the
cokernel and its projection through these isomorphisms. Empty powers use the same
formulas and require no extra hypotheses. -/
theorem scalarPresentationCokernel {R T : Type u} [CommRing R] [CommRing T]
    (f : R →+* T) (N : ModuleCat.{u} R) (m n : ℕ)
    (D : Matrix (Fin n) (Fin m) R) (q : of R (Fin n → R) ⟶ N)
    (hex : Function.Exact (Matrix.toLin' D) q) (hsurj : Function.Surjective q) :
    ∃ (p : of T (Fin n → T) ⟶ (extendScalars f).obj N)
      (v : (extendScalars f).obj N ≅ cokernel (ofHom (Matrix.toLin' (D.map f)))),
      (∀ x : Fin n → R, p (fun i ↦ f (x i)) =
        ExtendRestrictScalarsAdj.Unit.map f (q x)) ∧
      p ≫ v.hom = cokernel.π (ofHom (Matrix.toLin' (D.map f))) := by
  let F := extendScalars f
  let d := ofHom (Matrix.toLin' D)
  have : F.IsLeftAdjoint := (extendRestrictScalarsAdj f).isLeftAdjoint
  let c := isColimitCokernelCofork d q hex hsurj
  let e : N ≅ cokernel d := c.coconePointUniqueUpToIso (colimit.isColimit _)
  have he : q ≫ e.hom = cokernel.π d :=
    c.comp_coconePointUniqueUpToIso_hom (colimit.isColimit _) WalkingParallelPair.one
  let t := cokernel.mapIso (F.map d) (ofHom (Matrix.toLin' (D.map f)))
    (scalarPowerIso f m) (scalarPowerIso f n) (scalarPowerIso_natural f D)
  let v := F.mapIso e ≪≫ PreservesCokernel.iso F d ≪≫ t
  let p := (scalarPowerIso f n).inv ≫ F.map q
  refine ⟨p, v, ?_, ?_⟩
  · intro x
    have hx := scalarPowerIso_unit f n x
    have hi : (scalarPowerIso f n).inv (fun i ↦ f (x i)) =
        ExtendRestrictScalarsAdj.Unit.map f x := by
      rw [← hx]
      exact ConcreteCategory.congr_hom (scalarPowerIso f n).hom_inv_id _
    change F.map q ((scalarPowerIso f n).inv (fun i ↦ f (x i))) = _
    rw [hi]
    rfl
  · change (scalarPowerIso f n).inv ≫ F.map q ≫
      F.map e.hom ≫ (PreservesCokernel.iso F d).hom ≫ t.hom = _
    rw [← F.map_comp_assoc, he, PreservesCokernel.π_iso_hom_assoc]
    simp [t]

end ModuleCat
