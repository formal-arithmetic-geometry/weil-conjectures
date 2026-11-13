/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.Stability
import WeilConjectures.AlgebraicGeometry.IntrinsicFlatModuleStalkTensorPresentation
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Flat affine sections give flat stalks

## References

* Stacks Project, Tag 01U4.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- Flat affine sections of a quasi-coherent module give flat modules at every stalk.
(Stacks, Tag 01U4) -/
theorem flat_stalk_of_affine_sections_flat {Y : Scheme.{u}} (G : Y.Modules)
    [SheafOfModules.IsQuasicoherent.{u} G]
    (hflat : ∀ V : Y.affineOpens,
      letI : Module Γ(Y, V.1) Γ(G, V.1) :=
        Module.compHom _ ((𝟙 Y : Y ⟶ Y).appLE V.1 V.1 (le_rfl)).hom
      Module.Flat (Γ(Y, V.1)) (Γ(G, V.1))) (x : Y) :
    Module.Flat (Y.presheaf.stalk x)
      ((RingedSpace.moduleStalkFunctor Y.toRingedSpace x).obj G) := by
  obtain ⟨U, hU, hx, _⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Y) (x := x) (U := ⊤) (by trivial)
  let V : Y.affineOpens := ⟨U, hU⟩
  let : Module Γ(Y, V.1) Γ(G, V.1) :=
    Module.compHom _ ((𝟙 Y : Y ⟶ Y).appLE V.1 V.1 (le_rfl)).hom
  let : Algebra Γ(Y, V.1) (Y.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨x, hx⟩
  have : Module.Flat Γ(Y, V.1) Γ(G, V.1) := hflat V
  have : Module.Flat (Y.presheaf.stalk x)
      (TensorProduct Γ(Y, V.1) (Y.presheaf.stalk x) Γ(G, V.1)) :=
    Module.Flat.baseChange _ _ _
  obtain ⟨e⟩ := affine_sections_stalk_tensor_presentation G V x hx
  exact Module.Flat.of_linearEquiv e.symm

end AlgebraicGeometry
