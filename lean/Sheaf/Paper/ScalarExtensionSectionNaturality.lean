/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F5
-/
module

public import Sheaf.Paper.SemilinearSystemModels

/-! # Naturality of the normalized scalar-extension section -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe c v r u
open CategoryTheory Opposite
namespace WeilConjectures.SemilinearSections

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] scalarExtensionSection
attribute [local implicit_reducible] transition

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  {R S : Sheaf J CommRingCat.{max c v r}} (φ : R ⟶ S)
  (A : ScalarData.{c, v, max c v r} φ) (M : Mod.{c, v, max c v r} J R)

private theorem section_unit (U : Cᵒᵖ) (x : M.val.obj U) :
    scalarExtensionSection.{c, v, max c v r} φ A M U x =
      (A.ordinaryAdjunction.unit.app M).val.app U x := by
  unfold scalarExtensionSection
  rw [← A.unit_section]
  exact congrArg (fun f ↦ f.val.app U ((A.ordinaryAdjunction.unit.app M).val.app U x))
    (eqToIso (A.model.obj_eq M)).hom_inv_id

/-- The normalized scalar-extension section commutes with all restrictions in the site.

Source: Zheng Construction 4.1 and Stacks 03CZ, the scalar-extension unit on sheaves.
(blueprint: lem-coef-scalar-extension-section-naturality).

Proof: the defining unit_section equation identifies the specified section with the
ordinary adjunction unit, after cancelling the canonical object comparison and its inverse.
The unit is a morphism of sheaves of modules. Its presheaf naturality at the given site
arrow is the asserted equation, since scalar restriction retains every underlying section
and restriction map. This works for identities and for empty section groups as well.
-/
private theorem scalarExtensionSection_naturality {U V : Cᵒᵖ} (p : U ⟶ V)
    (x : M.val.obj U) :
    (A.model.E.obj M).val.map p (scalarExtensionSection.{c, v, max c v r} φ A M U x) =
      scalarExtensionSection.{c, v, max c v r} φ A M V (M.val.map p x) := by
  rw [section_unit.{c, v, r}, section_unit.{c, v, r}]
  exact (PresheafOfModules.naturality_apply
    (A.ordinaryAdjunction.unit.app M).val p x).symm

private theorem generic_transition_apply
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [EssentiallySmall.{u + 1} C]
    (B : ℕ → Sheaf J CommRingCat.{u + 1}) (τ : ∀ n, B (n + 1) ⟶ B n)
    {m n : ℕ} (h : n ≤ m)
    (M : SemilinearSections.Systems.{u + 1, u, u + 1} J B τ) (U : Cᵒᵖ)
    (x : M.val.obj (op (m, U.unop))) :
    ((SemilinearSections.transition.{u + 1, u, u + 1} J B τ h).app M).val.app U x =
      M.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x := by
  exact congrFun (eq_of_heq
    ((SemilinearSections.transition_exists.{u + 1, u, u + 1}
      J B τ h).exists.choose_spec M U)) x


/-- The scalar-adjunction unit commutes with the evaluated horizontal transition.
The two explicit evaluated sections allow different scalar-restriction carriers.

Source: Zheng Construction 4.1 and Stacks 03CZ.
(blueprint: lem-coef-scalar-extension-section-naturality).

Proof: identify the two sections with their normalized scalar-adjunction units.
The defining transition equation identifies the finite-level map on sections with
the original presheaf restriction in the sequence site. The scalar section equals
the ordinary adjunction unit by unit_section and cancellation of the object
comparison. The unit is a module-sheaf morphism; its presheaf naturality at the
horizontal sequence-site arrow gives the formula. This includes equal indices,
empty charts, and zero section groups.
-/
theorem scalarExtensionSection_transition
    {D : Type (u + 1)} [Category.{u} D] (K : GrothendieckTopology D)
    [EssentiallySmall.{u + 1} D]
    (B : ℕ → Sheaf K CommRingCat.{u + 1}) (τ : ∀ n, B (n + 1) ⟶ B n)
    {R : Sheaf (coefficientSequenceTopology K) CommRingCat.{u + 1}}
    (φ : R ⟶ systemRing K B τ)
    (A : ScalarData.{u + 1, u, u + 1} φ)
    (M : Mod.{u + 1, u, u + 1} (coefficientSequenceTopology K) R)
    {m n : ℕ} (h : n ≤ m) (U : Dᵒᵖ) (x : M.val.obj (op (m, U.unop)))
    (v : ((evaluation.{u + 1, u, u + 1} K B τ m).obj (A.model.E.obj M)).val.obj U)
    (w : ((evaluation.{u + 1, u, u + 1} K B τ n).obj (A.model.E.obj M)).val.obj U)
    (hv : HEq v (scalarExtensionSection.{u + 1, u, u + 1}
      φ A M (op (m, U.unop)) x))
    (hw : HEq w (scalarExtensionSection.{u + 1, u, u + 1}
      φ A M (op (n, U.unop))
        (M.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x))) :
    HEq (((transition.{u + 1, u, u + 1} K B τ h).app
      (A.model.E.obj M)).val.app U v) w := by
  have hv' : v = scalarExtensionSection.{u + 1, u, u + 1}
      φ A M (op (m, U.unop)) x := eq_of_heq hv
  have hw' : w = scalarExtensionSection.{u + 1, u, u + 1}
      φ A M (op (n, U.unop))
        (M.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x) := eq_of_heq hw
  rw [hv', hw']
  exact heq_of_eq ((generic_transition_apply K B τ h (A.model.E.obj M) U _).trans
    (scalarExtensionSection_naturality.{u + 1, u, u + 1}
      (coefficientSequenceTopology K) φ A M
      (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x))

end WeilConjectures.SemilinearSections
attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
