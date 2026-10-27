module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.Ideal.Cotangent

/-! # Geometric local tangent vectors

Source: ILO VIII 4.2.3, printed p.119 (blueprint: def-per-geometric-local-tangent).

The balancing equation presents Hom over the residue field with values in the geometric
residue field, equivalently the dual after scalar extension. No coefficient field is chosen.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- The actual map on maximal-ideal cotangent spaces, retaining its integral linearity.
Source: ILO VIII 4.2.3 (blueprint: def-per-geometric-local-tangent). -/
def localCotangentMap {Y X : Scheme.{u}} (f : Y ⟶ X) (y : Y) :
    IsLocalRing.CotangentSpace (X.presheaf.stalk (f y)) →ₗ[ℤ]
      IsLocalRing.CotangentSpace (Y.presheaf.stalk y) :=
  Ideal.mapCotangent _ _ (f.stalkMap y).hom.toIntAlgHom
    (fun _ hr ↦ map_nonunit (f.stalkMap y).hom _ hr)

/-- The geometric tangent space is the residue-linear dual of the local cotangent space.
The equation imposes exactly residue-field linearity; values already lie in Ω.
Source: ILO VIII 4.2.3 (blueprint: def-per-geometric-local-tangent). -/
def geometricLocalTangent {X : Scheme.{u}} {Ω : Type u} [Field Ω]
    (t : Spec (.of Ω) ⟶ X) :
    Submodule Ω
      (IsLocalRing.CotangentSpace
        (X.presheaf.stalk (t (IsLocalRing.closedPoint Ω))) →ₗ[ℤ] Ω) where
  carrier := {φ | ∀ (r : X.presheaf.stalk (t (IsLocalRing.closedPoint Ω)))
    (v : IsLocalRing.CotangentSpace (X.presheaf.stalk (t (IsLocalRing.closedPoint Ω)))),
      φ (r • v) = Scheme.stalkClosedPointTo t r * φ v}
  zero_mem' := by simp
  add_mem' := by
    intro φ ψ hφ hψ r v
    simp only [LinearMap.add_apply]
    rw [hφ r v, hψ r v, mul_add]
  smul_mem' := by
    intro c φ hφ r v
    simp only [LinearMap.smul_apply, smul_eq_mul]
    rw [hφ r v]
    ring

end AlgebraicGeometry
