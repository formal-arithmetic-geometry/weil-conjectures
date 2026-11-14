/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassChern

/-! # Extract the positive Kummer equation of normalized Chern data
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false

attribute [local irreducible] HasDerivedCategory.standard DerivedCategory.singleFunctors
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerClasses

variable (l : ℕ) [Fact l.Prime]

/-- The positive target-normalization predicate with its category data shared. -/
def ChernData.rootNormalized
    (T : Scheme.{u})
    (R A : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (φ : SemilinearSections.systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
        (fun n ↦ R.obj (op n)) (fun n ↦ R.map (homOfLE (Nat.le_succ n)).op) ⟶
      SemilinearSections.systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
        (fun n ↦ A.obj (op n)) (fun n ↦ A.map (homOfLE (Nat.le_succ n)).op))
    (c : ChernData l T R A φ) : Prop :=
  c.reduction.model.targetNormalization
      (ShortComplex.mk c.kummer.inclusion c.kummer.power c.kummer.zero)
      c.kummer.exact c.rootIso c.rootForget

/-- The positive Kummer normalization follows from normalized Chern data. -/
theorem chern_integral_target_normalization
    (T : Scheme.{u})
    (R A : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (φ : SemilinearSections.systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
        (fun n ↦ R.obj (op n)) (fun n ↦ R.map (homOfLE (Nat.le_succ n)).op) ⟶
      SemilinearSections.systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
        (fun n ↦ A.obj (op n)) (fun n ↦ A.map (homOfLE (Nat.le_succ n)).op))
    (c : ChernData l T R A φ)
    (q : coefficient T R ⟶ (SemilinearSections.res.{u + 1, u, u + 1} φ).obj
      (coefficient T A)) (n : ChernData.Normalized l T R A φ c q) :
    c.rootNormalized l T R A φ := by
  exact n.2.1

end AlgebraicGeometry.ProEtale.SpTowerClasses
