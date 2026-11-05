/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
public import WeilConjectures.CategoryTheory.Functor.CurryComparison

/-! # The unit transpose of the uncurried open projection map -/

@[expose] public section

namespace CategoryTheory.Adjunction

variable {A B : Type*} [Category* A] [Category* B]
  {E : A ⥤ B} {R : B ⥤ A} (adj : E ⊣ R)
  {TA : A × A ⥤ A} {TB : B × B ⥤ B}

/-- The transpose of the projection map for an uncurried tensor comparison. -/
lemma homEquiv_projectionMap_curryCompIsoOfIso
    (ρ : TB ⋙ R ≅ R.prod R ⋙ TA) (M : A) (N : B) :
    adj.homEquiv _ _ (((adj.projectionMap R (Functor.curry.obj TA) (Functor.curry.obj TB)
      (Functor.curryCompIsoOfIso ρ).inv).app M).app N) =
      TA.map (Prod.mkHom (adj.unit.app M) (𝟙 _)) ≫ ρ.inv.app (E.obj M, N) := by
  rw [projectionMap_app_app, Equiv.apply_symm_apply]
  simp [projectionMapTranspose, Functor.curryCompIsoOfIso]

end CategoryTheory.Adjunction
