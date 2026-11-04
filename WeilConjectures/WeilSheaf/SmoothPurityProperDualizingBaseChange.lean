/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityProperTraceCoordinates

/-!
# The exceptional base-change component at the unit

For a proper structural map, field-extension base change of the dualizing
complex implies invertibility of the exceptional base-change component at the
unit, without a smoothness assumption on the compactification.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (l : ℕ) [Fact l.Prime] {F L : Type u} [Field F] [Field L] [Algebra F L]
  [Fact (ringChar F).Prime] [Fact (ringChar F ≠ l)]
  [Fact (ringChar L).Prime] [Fact (ringChar L ≠ l)]
  {X : Over (Spec (.of F))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [IsProper (toPoint X).left]
  {X' : Over (Spec (.of L))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [IsProper (toPoint X').left]
  {π : X'.left ⟶ X.left}
  (e : (boundedConstructibleUpperStarOfMap l (X := point F) (Y := point L)
    (Spec.map (CommRingCat.ofHom (algebraMap F L)))).obj (𝟙_ _) ⟶ 𝟙_ _)
  (sq : IsPullback π (toPoint X').left (toPoint X).left
    (Spec.map (CommRingCat.ofHom (algebraMap F L))))

/-- The dualizing comparison is the exceptional comparison at the unit followed
by the image of the unit comparison. -/
lemma dualizingComplexBaseChange_eq_unit_component :
    dualizingComplexBaseChange l e sq =
      (upperShriekBaseChangeOfMap l sq).app (𝟙_ _) ≫
        (boundedConstructibleUpperShriek l (toPoint X')).map e := by
  simp only [dualizingComplexBaseChange, Adjunction.unitBaseChangeOfEq,
    upperShriek_toPoint_obj_unit, eqToHom_refl, Category.id_comp, Category.comp_id,
    Adjunction.unitBaseChange, upperShriekBaseChangeOfMap]
  rfl

/-- The exceptional base-change component at the unit is invertible for any
proper structural morphism after a field extension. -/
theorem isIso_upperShriekBaseChangeOfMap_unit_of_fieldExtension [IsIso e] :
    IsIso ((upperShriekBaseChangeOfMap l sq).app (𝟙_ _)) := by
  have hi := isIso_dualizingComplexBaseChange_of_fieldExtension l e sq
  rw [dualizingComplexBaseChange_eq_unit_component] at hi
  exact IsIso.of_isIso_comp_right _
    ((boundedConstructibleUpperShriek l (toPoint X')).map e)

end AlgebraicGeometry.ProEtale.CondensedRing
