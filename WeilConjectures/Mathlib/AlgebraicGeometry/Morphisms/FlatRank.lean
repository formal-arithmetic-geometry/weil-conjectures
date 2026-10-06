/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-!
# The rank of a morphism out of the empty scheme

- `AlgebraicGeometry.Scheme.Hom.finrank_eq_zero_of_isEmpty`: a morphism out of an empty scheme
  has rank `0` everywhere.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- A morphism out of an empty scheme has rank `0` everywhere. -/
lemma Scheme.Hom.finrank_eq_zero_of_isEmpty {Z T : Scheme.{u}} (g : Z ⟶ T) [IsEmpty Z]
    (t : T) : g.finrank t = 0 := by
  obtain ⟨R, i, _, y, rfl⟩ := T.exists_Spec_apply_eq t
  rw [← Scheme.Hom.finrank_pullback_snd]
  have : IsEmpty ↥(pullback g i) := Function.isEmpty (pullback.fst g i)
  let φ : R ⟶ CommRingCat.of PUnit.{u + 1} := CommRingCat.punitIsTerminal.from R
  have e : pullback.snd g i = isInitialOfIsEmpty.to (Spec (CommRingCat.of PUnit.{u + 1})) ≫
      Spec.map φ := isInitialOfIsEmpty.hom_ext _ _
  rw [e, finrank_comp_left_of_isIso,
    finrank_SpecMap_eq_finrank ((IsFinite.SpecMap_iff φ).mp inferInstance)
      (Flat.SpecMap_iff.mp inferInstance)]
  let := φ.hom.toAlgebra
  exact congrFun Module.rankAtStalk_eq_zero_of_subsingleton y

end AlgebraicGeometry
