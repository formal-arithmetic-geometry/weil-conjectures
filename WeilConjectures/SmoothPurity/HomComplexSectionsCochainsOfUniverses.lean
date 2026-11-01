/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts

public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexProjections

/-!
# Degreewise sections of the sheaf Hom complex

Source: Stacks Project, Tag 0A8Y, Equation (21.34.0.1).
(blueprint: lem-pur-hom-complex-sections-cochains-universes)
-/

@[expose] public section

universe u v r
open CategoryTheory Opposite
namespace CategoryTheory

private theorem fan_projection_bijective.{t} {ι : Type} {X : ι → Type t}
    {P : Type t} (π : ∀ i, P ⟶ X i) (h : Limits.IsLimit (Limits.Fan.mk P π)) :
    Function.Bijective (fun x i ↦ π i x) := by
  let e := h.conePointUniqueUpToIso (Limits.Types.productLimitCone X).isLimit
  have he (x : P) (i : ι) : e.hom x i = π i x :=
    ConcreteCategory.congr_hom (h.conePointUniqueUpToIso_hom_comp
      (Limits.Types.productLimitCone X).isLimit ⟨i⟩) x
  have hf : (fun x i ↦ π i x) = e.toEquiv := by
    funext x i
    exact (he x i).symm
  rw [hf]
  exact e.toEquiv.bijective

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
-- Chosen products and section evaluation require extra elaboration heartbeats.
set_option backward.isDefEq.respectTransparency true in
end CategoryTheory
