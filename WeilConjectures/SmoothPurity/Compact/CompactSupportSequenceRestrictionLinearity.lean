/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Compact.CompactSupportReductionTowerData
public import WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
public import WeilConjectures.CategoryTheory.ModuleObjects.Linear
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic

/-! # Linearity of completed restriction from a coefficient sequence

Source: the constant-section scalar calculation in the proof of the coherent
compact-support reduction tower, step 8; Stacks Tags 03DA and 0941.
(blueprint: lem-weil-compact-support-sequence-restriction-linearity).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory Opposite AlgebraicGeometry MonObj
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures

private theorem scalarRestrictionHomTransport
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u + 1}} {M M' N N' : SheafOfModules.{u + 1} R}
    (hM : M = M') (hN : N = N') (f : M ⟶ N) (g : M' ⟶ N')
    (h : ∀ V : Cᵒᵖ, HEq (fun x ↦ f.val.app V x) (fun x ↦ g.val.app V x)) :
    f = eqToHom hM ≫ g ≫ eqToHom hN.symm := by
  subst M' N'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  ext V x
  exact congrFun (eq_of_heq (h V)) x

/-- Restriction along a condensed coefficient map is linear for sectionwise compatible scalars.

Source: current blueprint, `lem-coef-integral-compact-support.proof.md`, paragraph 1
(canonical coefficient comparison), and `def-sfb-modobj-restriction`.
(blueprint: lem-weil-compact-support-sequence-restriction-linearity).

Proof: the two global scalar sections agree after the coefficient map because their maps
on every object of the pro-etale site agree. Sheaf and natural-transformation extensionality
give equality of global sections. Restriction leaves underlying morphisms unchanged and
its action by a global scalar is the action by the image scalar. The scalar-identity
criterion for linearity, implemented by `Mod.linear_comap`, finishes the proof.
This works for zero rings, zero modules and the empty scheme, and assumes neither
flatness nor surjectivity of the coefficient map. -/
theorem compactSupportSequenceRestriction_linear_of_sections
    (W : Scheme.{u})
    (Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (φ : Λ ⟶ Λ') [IsMonHom φ]
    (K : Type v) [Ring K]
    (sR : K →+* Γ (condensedRingObj Λ W))
    (sS : K →+* Γ (condensedRingObj Λ' W))
    (hc : ∀ (a : K) (V : W.ProEtᵒᵖ),
      (sR a).hom.hom.app V ≫ ((upperStarFromPoint W).map φ).hom.app V =
        (sS a).hom.hom.app V) :
    letI := Mod.linearOfRingHom sR
    letI := Mod.linearOfRingHom sS
    (Mod.comap (D := Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})
      ((upperStarFromPoint W).map φ)).Linear K := by
  apply Mod.linear_comap
  intro a
  apply Γ.ext
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  exact hc a V

end WeilConjectures
