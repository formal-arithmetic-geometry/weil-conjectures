/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FiniteAffineCechCoefficientComparisonMap
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.AlgebraicGeometry.CoefficientIntersectionScalarDecomposition

/-! # Scalar transport into the coefficient generator span

Source: Stacks Project, Tags 02KG, 01I9, 01IA and 0097.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- A section-ring multiple of a unit generator is in the base-ring span
(Stacks, Tags 02KG, 01I9, 01IA and 0097). -/
theorem coefficientTarget_scalar_span
    {X T : Scheme.{u}} (f : X ⟶ T) [IsSeparated f]
    (F : X.Modules) [F.IsQuasicoherent]
    (U : T.Opens) (hU : IsAffineOpen U)
    (Z : (f ⁻¹ᵁ U).toScheme.Opens) (hZ : IsAffineOpen Z)
    {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
    (sq : IsPullback g' f' f (g ≫ U.ι))
    (W : X'.Opens) (hW : W = g' ⁻¹ᵁ ((f ⁻¹ᵁ U).ι ''ᵁ Z))
    (B : T'.Opens) (hB : IsAffineOpen B) :
    letI : Algebra Γ(U.toScheme, ⊤) Γ(T', B) :=
      (g.appLE ⊤ B (by simp)).hom.toAlgebra
    let N := (ModuleCat.restrictScalars
      (((Scheme.ΓSpecIso Γ(U.toScheme, ⊤)).inv ≫
        ((f ∣_ U) ≫ U.toScheme.toSpecΓ).appTop).hom)).obj
          ((F.restrict (f ⁻¹ᵁ U).ι).presheafModuleCat.obj (op Z))
    let M := (pullback g').obj F
    ∀ (a : Γ(X', W ⊓ f' ⁻¹ᵁ B)) (s : N),
      (coefficientSupportIso f' M W B).inv
        (a • (M.presheaf.map (homOfLE (inf_le_left : W ⊓ f' ⁻¹ᵁ B ≤ W)).op
            (coefficientPullbackGenerator F (f ⁻¹ᵁ U) Z g' W hW s))) ∈
      Submodule.span (Γ(T', B)) (Set.range (fun t : N ↦
        (coefficientSupportIso f' M W B).inv
          (M.presheaf.map (homOfLE (inf_le_left : W ⊓ f' ⁻¹ᵁ B ≤ W)).op
            (coefficientPullbackGenerator F (f ⁻¹ᵁ U) Z g' W hW t)))) := by
  dsimp only
  intro a s
  let M := (pullback g').obj F
  let V := (f ⁻¹ᵁ U).ι ''ᵁ Z
  let e := F.restrictAppIso (f ⁻¹ᵁ U).ι Z
  let u := fun t : Γ(F.restrict (f ⁻¹ᵁ U).ι, Z) ↦
    M.presheaf.map (homOfLE (inf_le_left : W ⊓ f' ⁻¹ᵁ B ≤ W)).op
      (coefficientPullbackGenerator F (f ⁻¹ᵁ U) Z g' W hW t)
  let k := fun t : Γ(F.restrict (f ⁻¹ᵁ U).ι, Z) ↦
    (coefficientSupportIso f' M W B).inv (u t)
  let ρ := fun r : Γ(T', B) ↦ X'.presheaf.map
    (homOfLE (inf_le_right : W ⊓ f' ⁻¹ᵁ B ≤ f' ⁻¹ᵁ B)).op (f'.app B r)
  let δ := fun d : Γ(X, V) ↦ X'.presheaf.map
    (homOfLE (show W ⊓ f' ⁻¹ᵁ B ≤ g' ⁻¹ᵁ V from
      inf_le_left.trans hW.le)).op (g'.app V d)
  have hu (d : Γ(X, V)) :
      u (e.inv (d • e.hom s)) = δ d • u s := by
    dsimp [u, coefficientPullbackGenerator]
    rw [Iso.inv_hom_id_apply]
    let η : Γ(F, V) ⟶ Γ(M, g' ⁻¹ᵁ V) :=
      ((pullbackPushforwardAdjunction g').unit.app F).app V
    have hunit : η (d • e.hom s) = g'.app V d • η (e.hom s) :=
      Hom.app_smul ((pullbackPushforwardAdjunction g').unit.app F) d (e.hom s)
    rw [hunit, map_smul, map_smul]
    congr 1
    simp only [δ, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  have hρ (r : Γ(T', B)) (x : Γ(M, W ⊓ f' ⁻¹ᵁ B)) :
      (coefficientSupportIso f' M W B).inv (ρ r • x) =
        r • (coefficientSupportIso f' M W B).inv x := by
    apply (ConcreteCategory.bijective_of_isIso (coefficientSupportIso f' M W B).hom).injective
    simp only [Iso.inv_hom_id_apply, coefficientSupportIso_smul]
    rfl
  obtain ⟨n, r, d, ha⟩ :=
    coefficientIntersection_scalar_decomposition f U hU Z hZ g g' f' sq W hW B hB a
  change (coefficientSupportIso f' M W B).inv (a • u s) ∈
    Submodule.span (Γ(T', B)) (Set.range k)
  change a = ∑ j, ρ (r j) * δ (d j) at ha
  rw [ha, Finset.sum_smul, map_sum]
  apply Submodule.sum_mem
  intro j _
  rw [mul_smul, ← hu, hρ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span
    (Set.mem_range_self (e.inv (d j • e.hom s))))

end
end AlgebraicGeometry.Scheme.Modules
