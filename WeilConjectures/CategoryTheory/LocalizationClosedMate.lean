/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# The closed quotient comparison is the adjunction mate

Source: trace-additivity proof Steps 2(b) and 6, adjunction triangle identities
(blueprint: lem-trf-localization-closed-mate).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe vC uC vD uD
open CategoryTheory
namespace CategoryTheory
variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  (G : C ⥤ C) (H : D ⥤ D) (d : G ⋙ L ≅ L ⋙ H)

/-- The unit determines the quotient comparison as the specified mate.
Source: trace-additivity Steps 2(b) and 6.
Proof: the unit equation for the mates correspondence, followed by cancellation
of the inverse square comparison.
(blueprint: lem-trf-localization-closed-mate). -/
theorem localizationClosedMate_unit (M : C) :
    G.map (adj.unit.app M) ≫
        (mateEquiv adj adj (TwoSquare.mk _ _ _ _ d.hom)).app (L.obj M) ≫
        R.map (d.inv.app M) = adj.unit.app (G.obj M) := by
  rw [← Category.assoc, unit_mateEquiv]
  simp [Category.assoc, ← R.map_comp]

/-- An epic pulled-back unit uniquely determines the closed comparison.
Source: trace-additivity Step 6.
Proof: both candidates have the same composite with the epic pulled-back unit;
the mate candidate has that composite by its unit equation.
(blueprint: lem-trf-localization-closed-mate). -/
theorem localizationClosedMate_eq (M : C) [Epi (G.map (adj.unit.app M))]
    (β : G.obj (R.obj (L.obj M)) ⟶ R.obj (L.obj (G.obj M)))
    (hβ : G.map (adj.unit.app M) ≫ β = adj.unit.app (G.obj M)) :
    β = (mateEquiv adj adj (TwoSquare.mk _ _ _ _ d.hom)).app (L.obj M) ≫
      R.map (d.inv.app M) := by
  apply (cancel_epi (G.map (adj.unit.app M))).1
  rw [hβ]
  exact (localizationClosedMate_unit adj G H d M).symm

/-- Invertibility on the closed restrictions implies invertibility on every object
of the closed category, using the invertible counit.
Source: trace-additivity Step 6.
Proof: apply the assumed invertibility to R(N). The counit identifies LR(N) with N,
and naturality conjugates the mate component at LR(N) to its component at N.
(blueprint: lem-trf-localization-closed-mate). -/
theorem localizationClosedMate_isIso [IsIso adj.counit]
    (h : ∀ M : C,
      IsIso ((mateEquiv adj adj (TwoSquare.mk _ _ _ _ d.hom)).app (L.obj M))) :
    IsIso (mateEquiv adj adj (TwoSquare.mk _ _ _ _ d.hom)).natTrans := by
  let e := (mateEquiv adj adj (TwoSquare.mk _ _ _ _ d.hom)).natTrans
  suffices ∀ N, IsIso (e.app N) by
    let := this
    exact NatIso.isIso_of_isIso_app e
  intro N
  have hn := e.naturality (adj.counit.app N)
  dsimp only [Functor.id_obj, Functor.comp_obj] at hn
  have : IsIso (e.app (L.obj (R.obj N))) := h (R.obj N)
  have : IsIso ((R ⋙ G).map (adj.counit.app N) ≫ e.app N) := by
    rw [hn]
    infer_instance
  exact IsIso.of_isIso_comp_left ((R ⋙ G).map (adj.counit.app N)) (e.app N)

end CategoryTheory
