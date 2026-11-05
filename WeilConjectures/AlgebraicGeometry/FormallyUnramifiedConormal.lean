/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.UniversalFirstOrderThickeningExists
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module

/-!
# Conormal sheaf of a formally unramified morphism

Source: Stacks Project, More on Morphisms, Definition 04F4 (2), and Morphisms,
Definition 01R2 (blueprint: def-weil-pbc-conormal-sheaf-formally-unramified).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- The conormal sheaf for the chosen universal first order thickening of `h`.
Its ideal is `i.ker`, and its square is zero by `H.1.2`; hence pulling back the ideal
is the same conormal module as pulling back its quotient by its square.
Source: Stacks Project, Definition 04F4 (2) and Definition 01R2
(blueprint: def-weil-pbc-conormal-sheaf-formally-unramified). -/
noncomputable def formallyUnramifiedConormal {Z X Z' : Scheme.{u}}
    (h : Z ⟶ X) [FormallyUnramified h] (i : Z ⟶ Z') (h' : Z' ⟶ X)
    (_H : IsUniversalFirstOrderThickening h i h') : Z.Modules :=
  (Scheme.Modules.tensorPullback i).obj i.ker.toModules

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem range_kernelIdeal {A B : Scheme.{u}} (i : A ⟶ B)
    [IsClosedImmersion i] (U : B.Opens) :
    Set.range (i.ker.toModulesι.app U) = {x | i.app U x = 0} := by
  rw [Scheme.IdealSheafData.range_toModulesι_app_eq]
  ext x
  change i.imageι.app U x = 0 ↔ i.app U x = 0
  have hi := Scheme.Hom.congr_app i.toImage_imageι U
  rw [Scheme.Hom.comp_app] at hi
  have hcomp : (i.imageι.app U ≫ i.toImage.app (i.imageι ⁻¹ᵁ U)) x = 0 ↔
      i.app U x = 0 := by
    rw [hi]
    have heq {V W : A.Opens} (he : V = W) (y : Γ(A, W)) :
        A.presheaf.map (eqToHom he).op y = 0 ↔ y = 0 :=
      map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
        (A.presheaf.map (eqToHom he).op)).1
    exact heq _ _
  exact (map_eq_zero_iff _
    (ConcreteCategory.bijective_of_isIso (i.toImage.app (i.imageι ⁻¹ᵁ U))).1).symm.trans
      hcomp

end AlgebraicGeometry
