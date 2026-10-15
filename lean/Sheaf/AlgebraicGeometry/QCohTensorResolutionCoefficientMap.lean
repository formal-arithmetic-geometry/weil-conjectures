module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

@[expose] public section
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Chosen affine section coordinates carry the canonical restriction semilinearly. -/
theorem exists_tensorResolutionCoefficientMap
    (Y : Scheme.{u}) (N : Y.Modules)
    (NA : ∀ U : Y.affineOpens, ModuleCat.{u} (Γ(Y, U.1) : Type u))
    (sN : ∀ U : Y.affineOpens, NA U ≃ₗ[Γ(Y, U.1)] N.val.obj (op U.1))
    (V U : Y.affineOpens) (h : V.1 ≤ U.1) :
    let φ := (Y.presheaf.map (homOfLE h).op).hom
    ∃ b : NA U →ₛₗ[φ] NA V,
      ∀ y, sN V (b y) = N.val.map (homOfLE h).op (sN U y) := by
  let φ := (Y.presheaf.map (homOfLE h).op).hom
  let b : NA U →ₛₗ[φ] NA V :=
    { toFun := fun y ↦ (sN V).symm (N.val.map (homOfLE h).op (sN U y))
      map_add' := by
        intro x y
        simp only [map_add]
      map_smul' := by
        intro r y
        apply (sN V).injective
        simp only [LinearEquiv.apply_symm_apply, LinearEquiv.map_smul]
        exact N.map_smul (homOfLE h) r (sN U y) }
  exact ⟨b, by intro y; exact (sN V).apply_symm_apply _⟩

end AlgebraicGeometry
