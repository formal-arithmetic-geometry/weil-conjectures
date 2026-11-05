/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityFreeResolution
public import WeilConjectures.WeilSheaf.SmoothPurityFreeComparison

/-!
# Testing a trace on free objects

An invertible comparison with the free functor transfers the universal property of
an underlying trace to free Weil objects. The free resolution criterion then extends
that universal property to bounded Weil objects. This avoids choosing a geometric
comparison for a native right adjoint.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Adjunction

/-- A universal arrow has an invertible adjoint transpose. -/
theorem isIso_homEquiv_of_bijective
    {C D : Type*} [Category C] [Category D] {T : C ⥤ D} {R : D ⥤ C}
    (adj : T ⊣ R) {H : C} {Y : D} (d : T.obj H ⟶ Y)
    (hd : ∀ M, Function.Bijective (fun u : M ⟶ H ↦ T.map u ≫ d)) :
    IsIso (adj.homEquiv H Y d) := by
  apply isIso_of_yoneda_map_bijective
  intro M
  change Function.Bijective (fun u : M ⟶ H ↦ u ≫ adj.homEquiv H Y d)
  have h : (fun u : M ⟶ H ↦ u ≫ adj.homEquiv H Y d) =
      (adj.homEquiv M Y) ∘ (fun u : M ⟶ H ↦ T.map u ≫ d) := by
    funext u
    exact (adj.homEquiv_naturality_left u d).symm
  rw [h]
  exact (adj.homEquiv M Y).bijective.comp (hd M)

end CategoryTheory.Adjunction

namespace CategoryTheory.Endofunctor.IsoAlgebra

universe v v'

variable {C : Type*} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  {F : C ⥤ C} [F.Additive] [F.IsEquivalence]
  {D : Type*} [Category.{v'} D] [Abelian D] [IsGrothendieckAbelian.{v'} D]
  {G : D ⥤ D} [G.Additive] [G.IsEquivalence]
  [HasDerivedCategory.{v} (IsoAlgebra F)] [HasDerivedCategory.{v'} (IsoAlgebra G)]
  [HasDerivedCategory.{v} C] [HasDerivedCategory.{v'} D]

end CategoryTheory.Endofunctor.IsoAlgebra
