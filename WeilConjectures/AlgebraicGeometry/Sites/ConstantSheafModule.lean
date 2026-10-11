/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.ConstantSheafSections
public import WeilConjectures.AlgebraicGeometry.Sites.PointCohomology
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) {Λ : Type (u + 1)} [CommRing Λ] (M : ModuleCat.{u + 1} Λ)

example : X.smallEtaleTopology.PreservesSheafification
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) := inferInstance

example : (Functor.const X.Etaleᵒᵖ).obj M ⋙ forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  = (Functor.const X.Etaleᵒᵖ).obj ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj M) :=
  rfl

example {T : X.Etale} (hT : IsTerminal T) :
    (constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ) hT).unit.app M =
    (CategoryTheory.toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M)).app
        (op T) := by
  simp [constantSheafAdj, Adjunction.comp_unit_app]

end AlgebraicGeometry.Scheme
