/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.CartanEilenbergExists
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import WeilConjectures.CategoryTheory.DoubleComplexTotal
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic

/-! # Presentations by injective and Cartan--Eilenberg resolutions

Source: Stacks Project, Derived Categories, Tags 015H and 015K
(blueprint: def-sp-cartan-eilenberg-presentation).
-/

@[expose] public section

universe uA vA uB vB uC vC

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable {B : Type uB} [Category.{vB} B] [Abelian B]

namespace CartanEilenbergPresentation

variable {F : A ⥤ B} [F.Additive]

variable {C : Type uC} [Category.{vC} C] [Abelian C]

/-- Apply `G` vertically and extend the resolution degree by zero.
Source: Stacks, Tag 015K (blueprint: def-sp-cartan-eilenberg-presentation). -/
noncomputable def mappedFunctor (G : B ⥤ C) [G.Additive] :
    HomologicalComplex₂ B (ComplexShape.up ℤ) (ComplexShape.up ℕ) ⥤
      HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (G.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
    ComplexShape.embeddingUpNat.extendFunctor C).mapHomologicalComplex (ComplexShape.up ℤ)

end CartanEilenbergPresentation
end CategoryTheory
