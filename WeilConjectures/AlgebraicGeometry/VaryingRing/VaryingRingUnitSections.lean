/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations

/-! # Unit sections of the varying-ring inverse image

Sectionwise formulas for the unit of the inverse image adjunction on the ℓ-power sequence
site: its naturality, and the inverse-image compositor `moduleGComp` on iterated unit
sections (restricted along the pullback pasting isomorphism).

Source: Stacks 03EK and 0D6D (blueprint: def-sp-varying-ring-operations).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.VaryingRing

variable (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n : ℕ, R (n + 1) ⟶ R n)

/-- The inverse image of a map on unit sections. -/
theorem pull_map_unit_apply {X Y : Scheme.{u}} (f : X ⟶ Y) {A B : Modules R φ Y} (ψ : A ⟶ B)
    (n : ℕ) (U : Y.ProEt) (z : A.val.obj (op (n, U))) :
    ((pull R φ f).map ψ).val.app (op (n, (Scheme.proEtaleBaseChange f).obj U))
        (((moduleAdj R φ f).unit.app A).val.app (op (n, U)) z) =
      ((moduleAdj R φ f).unit.app B).val.app (op (n, U)) (ψ.val.app (op (n, U)) z) :=
  (congrArg (fun χ ↦ χ.val.app (op (n, U)) z) ((moduleAdj R φ f).unit.naturality ψ)).symm

/-- The inverse-image compositor on iterated unit sections. -/
theorem moduleGComp_inv_app_unit {X Z Y : Scheme.{u}} (i : X ⟶ Z) (g : Z ⟶ Y)
    (A : Modules R φ Y) (n : ℕ) (U : Y.ProEt) (z : A.val.obj (op (n, U))) :
    ((moduleGComp R φ i g).inv.app A).val.app (op (n, (Scheme.proEtaleBaseChange (i ≫ g)).obj U))
        (((pull R φ i).obj ((pull R φ g).obj A)).val.map
          (Prod.mkHom (𝟙 n) ((MorphismProperty.Over.pullbackComp i g).hom.app U)).op
          (((moduleAdj R φ i).unit.app ((pull R φ g).obj A)).val.app
            (op (n, (Scheme.proEtaleBaseChange g).obj U))
            (((moduleAdj R φ g).unit.app A).val.app (op (n, U)) z))) =
      ((moduleAdj R φ (i ≫ g)).unit.app A).val.app (op (n, U)) z := by
  have hspec := (modulePComp_existsUnique R φ i g).choose_spec.1
  have h := congrArg (fun χ ↦ χ.val.app (op (n, U)) z)
    (unit_conjugateEquiv_symm (moduleAdj R φ (i ≫ g)) ((moduleAdj R φ g).comp (moduleAdj R φ i))
      (modulePComp R φ i g).inv A)
  have h' := congrArg (fun w ↦ ((modulePComp R φ i g).hom.app ((pull R φ (i ≫ g)).obj A)).val.app
    (op (n, U)) w) h
  have hn := congrArg (fun χ ↦ χ.val.app (op (n, U))
      ((((moduleAdj R φ g).comp (moduleAdj R φ i)).unit.app A).val.app (op (n, U)) z))
    ((modulePComp R φ i g).hom.naturality ((moduleGComp R φ i g).inv.app A))
  dsimp only at h h' hn
  rw [← hspec]
  exact hn.symm.trans (h'.symm.trans (congrArg (fun χ ↦ χ.val.app (op (n, U))
    (((moduleAdj R φ (i ≫ g)).unit.app A).val.app (op (n, U)) z))
    ((modulePComp R φ i g).inv_hom_id_app ((pull R φ (i ≫ g)).obj A))))

end AlgebraicGeometry.ProEtale.VaryingRing
