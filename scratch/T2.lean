module

public import WeilConjectures.AlgebraicGeometry.Modules.Fiber
public import WeilConjectures.AlgebraicGeometry.Modules.LocallyTrivial
public import WeilConjectures.AlgebraicGeometry.Modules.TrivialLineBundle

@[expose] public section

universe u

open CategoryTheory Opposite SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

variable {Y : Scheme.{u}}

/-- The global function by which an endomorphism of the structure sheaf multiplies. -/
noncomputable def unitEndSection (ψ : Y.structureModules ⟶ Y.structureModules) : Γ(Y, ⊤) :=
  Hom.app ψ ⊤ (1 : Γ(Y, ⊤))

lemma mul_restrict_unitEndSection (ψ : Y.structureModules ⟶ Y.structureModules) (U : Y.Opens)
    (r : Γ(Y, U)) :
    r * Y.presheaf.map (homOfLE (le_top (a := U))).op (unitEndSection ψ) = Hom.app ψ U r := by
  have h1 : Hom.app ψ U (r • (1 : Γ(Y, U))) = r • Hom.app ψ U (1 : Γ(Y, U)) := Hom.app_smul ψ r _
  have h2 := Hom.naturality_apply ψ (homOfLE (le_top (a := U))) (1 : Γ(Y, ⊤))
  rw [show (Y.structureModules).presheaf.map (homOfLE (le_top (a := U))).op (1 : Γ(Y, ⊤)) =
      (1 : Γ(Y, U)) from map_one (Y.presheaf.map _).hom] at h2
  have h3 : Hom.app ψ U r = r • Hom.app ψ U (1 : Γ(Y, U)) := by
    rw [← h1]
    congr 1
    exact (mul_one r).symm
  rw [h3, h2]
  rfl

/-- **Multiplication by a unit is an isomorphism.** An endomorphism of the structure sheaf whose
global function is a unit of `Γ(Y, 𝒪_Y)` is an isomorphism. -/
theorem isIso_of_isUnit_unitEndSection (ψ : Y.structureModules ⟶ Y.structureModules)
    (h : IsUnit (unitEndSection ψ)) : IsIso ψ := by
  rw [Hom.isIso_iff_isIso_app]
  intro U
  rw [ConcreteCategory.isIso_iff_bijective]
  obtain ⟨u, hu⟩ := h.map (Y.presheaf.map (homOfLE (le_top (a := U))).op).hom
  have hbu : IsUnit (Y.presheaf.map (homOfLE (le_top (a := U))).op (unitEndSection ψ)) := ⟨u, hu⟩
  constructor
  · intro s t hst
    refine hbu.mul_left_injective ?_
    exact (mul_restrict_unitEndSection ψ U s).trans
      (hst.trans (mul_restrict_unitEndSection ψ U t).symm)
  · intro t
    obtain ⟨t', rfl⟩ : ∃ t' : Γ(Y, U), t' = t := ⟨t, rfl⟩
    refine ⟨((u⁻¹ : Γ(Y, U)ˣ) : Γ(Y, U)) * t', ?_⟩
    rw [← mul_restrict_unitEndSection ψ U (((u⁻¹ : Γ(Y, U)ˣ) : Γ(Y, U)) * t'), ← hu,
      mul_comm ((u⁻¹ : Γ(Y, U)ˣ) : Γ(Y, U)) t', mul_assoc, u.inv_mul, mul_one]

/-- **The fibre of multiplication by a global function.** The map induced on the fibre at `y` by
an endomorphism of the structure sheaf vanishes exactly when its global function vanishes
at `y`. -/
theorem fiberMap_eq_zero_iff_Γevaluation_eq_zero (ψ : Y.structureModules ⟶ Y.structureModules)
    (y : Y) : fiberMap ψ y = 0 ↔ Y.Γevaluation y (unitEndSection ψ) = 0 := by
  have hv : fiberMk Y.structureModules y (1 : Γ(Y, ⊤)) ≠ 0 :=
    fiberMk_unit_ne_zero_of_isUnit isUnit_one y
  have hkey : fiberMap ψ y (fiberMk Y.structureModules y (1 : Γ(Y, ⊤))) =
      fiberMk Y.structureModules y (unitEndSection ψ) := fiberMap_fiberMk ψ y _
  constructor
  · intro h
    refine (fiberMk_unit_eq_zero_iff y (unitEndSection ψ)).1 ?_
    rw [← hkey, h]
    simp
  · intro h
    have hz : fiberMap ψ y (fiberMk Y.structureModules y (1 : Γ(Y, ⊤))) = 0 := by
      rw [hkey]
      exact (fiberMk_unit_eq_zero_iff y (unitEndSection ψ)).2 h
    have hfin : Module.finrank (Y.residueField y) (Y.structureModules.fiber y) = 1 := by
      rw [(fiberUnitIso Y y).toLinearEquiv.finrank_eq, Module.finrank_self]
    ext w
    obtain ⟨c, rfl⟩ := (_root_.finrank_eq_one_iff_of_nonzero' _ hv).1 hfin w
    simp [hz]

end AlgebraicGeometry.Scheme.Modules
