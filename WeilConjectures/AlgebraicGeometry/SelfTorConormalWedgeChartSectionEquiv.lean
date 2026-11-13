/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.SelfTorAffineSection
public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.AffineConormalSections
import WeilConjectures.AlgebraicGeometry.Modules.ExteriorSheafAffineUnit
import WeilConjectures.AlgebraicGeometry.SelfTorConormalExteriorSectionModel
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry
/-- The affine section calculation underlying the conormal wedge chart. -/
theorem exists_selfTor_conormal_wedge_chart_section_equiv
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (n : ℕ) (U : Y.affineOpens) :
    let N := (Scheme.Modules.tensorPullback i).obj i.ker.toModules
    let E := Scheme.Modules.exteriorPower N n
    let M := conormalExteriorModule (Γ(Y, U.1) : Type u) (i.ker.ideal U) n
    let T := tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom ⋙
      Scheme.Modules.pushforward U.1.ι ⋙ Scheme.Modules.tensorPullback i
    ∃ e : ((E.over (i ⁻¹ᵁ U.1)).val.obj
          (op (Over.mk (𝟙 (i ⁻¹ᵁ U.1))))) ≃ₗ[Z.presheaf.obj (op (i ⁻¹ᵁ U.1))]
        ((T.obj M).over (i ⁻¹ᵁ U.1)).val.obj
          (op (Over.mk (𝟙 (i ⁻¹ᵁ U.1)))),
      ∀ b : Fin n → i.ker.toModules.val.obj (op U.1),
        e (Scheme.Modules.wedge (M := N) (r := n) (U := (i ⁻¹ᵁ U.1))
          (fun j ↦ ((Classical.choose
            (Scheme.Modules.exists_tensorPullbackAdjunction i)).unit.app
              i.ker.toModules).val.app (op U.1) (b j))) =
          selfTorAffineSection i U M (selfTorIdealWedge i U n b) := by
  classical
  let N := (Scheme.Modules.tensorPullback i).obj i.ker.toModules
  have : N.IsQuasicoherent := (Scheme.Modules.affine_conormal_sections.{u, u} i).1
  let V : Z.affineOpens := ⟨i ⁻¹ᵁ U.1, U.2.preimage i⟩
  let η := ((PresheafOfModules.sheafificationAdjunction.{u}
    (𝟙 Z.ringCatSheaf.obj)).unit.app
      (_root_.PresheafOfModules.exteriorPower (R := _) N.val n)).app (op V.1)
  let e₁ : (⋀[Z.presheaf.obj (op V.1)]^n (N.val.obj (op V.1))) ≃ₗ[
      Z.presheaf.obj (op V.1)] (Scheme.Modules.exteriorPower N n).val.obj (op V.1) :=
    LinearEquiv.ofBijective η.hom
    (Scheme.Modules.exteriorSheaf_affine_unit_bijective N n V)
  obtain ⟨e₂, h₂⟩ := exists_selfTor_conormal_exterior_section_model i n U
  refine ⟨e₁.symm.trans e₂, ?_⟩
  intro b
  change e₂ (e₁.symm (e₁ (exteriorPower.ιMulti
    (Z.presheaf.obj (op V.1)) n
    (fun j ↦ ((Classical.choose
      (Scheme.Modules.exists_tensorPullbackAdjunction i)).unit.app
        i.ker.toModules).val.app (op U.1) (b j))))) = _
  rw [e₁.symm_apply_apply]
  exact h₂ b

end AlgebraicGeometry
