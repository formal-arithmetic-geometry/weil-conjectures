/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.Opposite
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.Algebra.Module.Basic
public import WeilConjectures.Algebra.Homology.BilinearHomComplex
/-! # Product Hom complexes for a separately additive coefficient bifunctor
Source: Stacks Project, sites-cohomology.tex, Section 0A8X, and Algebraization, Tag 099I
(blueprint: lem-weil-pbc-bilinear-hom-complex).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory
variable {A B D : Type u} [Category.{v} A] [Category.{v} B] [Category.{v} D]
  [Preadditive A] [Preadditive B] [Preadditive D] [HasProducts.{0} D]
  (H : Aᵒᵖ ⥤ B ⥤ D) [H.Additive] [∀ a, (H.obj a).Additive]

omit [Preadditive A] [Preadditive B] [Preadditive D] [HasProducts D]
    [H.Additive] [∀ a, (H.obj a).Additive] in
@[simp] private lemma hMap_id (a : A) (b : B) :
    hMap H (𝟙 a) (𝟙 b) = 𝟙 (hObj H a b) := by
  exact (Functor.uncurry.obj H).map_id (op a, b)

end CategoryTheory
