/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.CategoryTheory.Functor.OfSequence
import Sheaf.RingTheory.ModuleLocalizationFilteredColimit

/-! # Finite families of localization power systems

Source: Stacks Project, Tag 00CM and perfect.tex Tag 0911.
(blueprint: lem-sc-finite-localization-power-colimit).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

variable (A : Type u) [CommRing A] (ι : Type) (κ : ι → Type)
  (N : ι → ModuleCat.{u} A) (g : ∀ i, κ i → A)

/-- The direct sum of the pointwise multiplication maps.
Source: Stacks, Tag 00CM (blueprint: lem-sc-finite-localization-power-colimit). -/
def finiteLocalizationPowerStep :
    (DirectSum ι (fun i ↦ κ i → N i)) →+ DirectSum ι (fun i ↦ κ i → N i) :=
  DirectSum.map fun i ↦
    { toFun := fun x t ↦ g i t • x t
      map_zero' := by ext t; exact smul_zero _
      map_add' := by intro x y; ext t; exact smul_add _ _ _ }

/-- The sequential diagram of multiplication by the specified elements.
Source: Stacks, Tag 00CM (blueprint: lem-sc-finite-localization-power-colimit). -/
def finiteLocalizationPowerDiagram : ℕ ⥤ AddCommGrpCat.{u} :=
  Functor.ofSequence
    (X := fun _ ↦ AddCommGrpCat.of (DirectSum ι (fun i ↦ κ i → N i)))
    (fun _ ↦ AddCommGrpCat.ofHom (finiteLocalizationPowerStep A ι κ N g))

/-- Finite direct sums of finite products of power systems have the expected
localized colimit.

Source: Stacks Project, algebra.tex Tag 00CM; perfect.tex Tag 0911
(blueprint: lem-sc-finite-localization-power-colimit).

Proof: for each pair (i,t), apply ModuleCat.localization_away_colimit to N i and
 g i t. Forgetting to additive groups preserves filtered colimits of modules,
so the fraction map identifies the additive colimit with the additive group of
LocalizedModule.Away (g i t) (N i). Filtered colimits of additive groups commute
with finite products: representatives of finitely many coordinates can be
moved to one common stage, and finitely many equalities can likewise be checked
at a common stage. Colimits commute with direct sums by their universal
properties. Apply these identifications to the finite coordinate families;
the successive maps are exactly finiteLocalizationPowerStep. Empty families
have zero direct sum, or the zero group as their empty product, so are included.
-/
theorem finiteLocalizationPowerColimit [Finite ι] [∀ i, Finite (κ i)] :
    Nonempty (colimit (finiteLocalizationPowerDiagram A ι κ N g) ≅
      AddCommGrpCat.of (DirectSum ι
        (fun i ↦ ∀ t : κ i, LocalizedModule.Away (g i t) (N i)))) := by sorry

end AlgebraicGeometry
