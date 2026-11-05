/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import WeilConjectures.CategoryTheory.RoosFinitePrefixLimits
import WeilConjectures.CategoryTheory.RoosPrefixAcyclic

/-!
# The functorial acyclic resolution of a tower

The finite-prefix construction of Stacks Project, Tag 07KW, Lemma 15.88.1.
(blueprint: lem-pc-roos-functorial-acyclic-resolution).
-/

@[expose] public section

universe u

namespace CategoryTheory

open Limits

@[reassoc] private theorem prefixLimitIso_π (s : ℕ) (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) (i : ℕ) :
    (prefixLimitIso s A).hom ≫ Pi.π (fun j : ℕ ↦ A.obj (Opposite.op j)) i =
      limit.π (roosPrefixTower s A) (Opposite.op (i + 1)) ≫
        roosPrefixEval s A (i + 1) i (by omega) := by
  change Pi.lift _ ≫ _ = _
  rw [Pi.lift_π]
  rfl

@[reassoc] private theorem prefixLimitIso_π_at (s : ℕ)
    (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) (n i : ℕ) (h : i < n + s) :
    (prefixLimitIso s A).hom ≫ Pi.π (fun j : ℕ ↦ A.obj (Opposite.op j)) i =
      limit.π (roosPrefixTower s A) (Opposite.op n) ≫ roosPrefixEval s A n i h := by
  rw [prefixLimitIso_π]
  exact roosPrefixCone_coordinate s A (limit.cone _) (i + 1) n i (by omega) h

end CategoryTheory
