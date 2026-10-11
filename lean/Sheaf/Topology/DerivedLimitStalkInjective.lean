/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
import Sheaf.Topology.OpenModuleDerivedSections
import Sheaf.Algebra.Homology.ModuleStalkFunctor
import Sheaf.CategoryTheory.DerivedLimitRoosAbelianGroups
import Sheaf.CategoryTheory.Triangulated.DerivedLimit
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Stalk injectivity for a derived inverse limit

Source: Stacks Project, Cohomology of Sheaves, Tag 0D61,
lemma-cohomology-derived-limit-injective
(blueprint: lem-pc-ringed-space-derived-limit-stalk-injective).
-/

universe u v w

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.RingedSpace

/-- Eventual injectivity of open cohomology and vanishing of its first derived inverse
limit imply injectivity of the specified projection on cohomology stalks.
Source: Stacks Project, Cohomology of Sheaves, Tag 0D61,
lemma-cohomology-derived-limit-injective
(blueprint: lem-pc-ringed-space-derived-limit-stalk-injective).

Proof:
1. By lem-pc-ringed-space-sheafification-cohomology (Tag 0BKJ), represent a stalk class
in the kernel by a class over an open neighborhood. Its image has zero germ, so shrink
until its image at level n₀ vanishes, then refine to an element of the fundamental system.
2. Apply lem-pc-ringed-space-rgamma-derived-limit (Tag 0D60). Its Milnor short exact
sequence has left term zero by hlim. The inverse limit maps injectively to level n₀:
compatibility and hinj kill all later components, and compatibility kills earlier ones.
The representative therefore vanishes.
3. Its germ is zero, giving the claimed injectivity. The projection used throughout
is p followed by the n₀-th product projection; no canonical derived limit is chosen. -/
theorem derivedLimit_stalk_injective (X : RingedSpace.{u})
    [HasDerivedCategory.{v} (SheafOfModules.{u} (moduleRings X))]
    [HasDerivedCategory.{w} AddCommGrpCat.{u}]
    (K : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{u} (moduleRings X)))
    (L : DerivedCategory (SheafOfModules.{u} (moduleRings X)))
    (p : L ⟶ ∏ᶜ (fun n : ℕ => K.obj (op n)))
    (δ : (∏ᶜ (fun n : ℕ => K.obj (op n))) ⟶ L⟦(1 : ℤ)⟧)
    (hK : IsDerivedLimitTriangle
      (fun n : ℕ => K.map (homOfLE (Nat.le_succ n)).op) L p δ)
    (x : X) (m : ℤ) (n₀ : ℕ) (B : Set (Opens X))
    (hB_mem : ∀ U ∈ B, x ∈ U)
    (hB_basis : ∀ V : Opens X, x ∈ V → ∃ U ∈ B, U ≤ V)
    (hlim : ∀ U ∈ B, IsZero
      ((@Functor.rightDerived _ _ _ _ _
        (@InjectiveResolution.instHasInjectiveResolutions _ _ _ roosTowerEnoughInjectives) _
        (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}) roosLimitAdditive 1).obj
        (K ⋙ openModuleDerivedSections X U ⋙
          DerivedCategory.homologyFunctor AddCommGrpCat.{u} (m - 1))))
    (hinj : ∀ U ∈ B, ∀ (n : ℕ) (h : n₀ ≤ n), Function.Injective
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).map
        ((openModuleDerivedSections X U).map (K.map (homOfLE h).op)))) :
    Function.Injective ((moduleStalkFunctor X x).map
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (moduleRings X)) m).map
        (p ≫ Pi.π (fun n : ℕ => K.obj (op n)) n₀))).hom := by
  sorry

end AlgebraicGeometry.RingedSpace
