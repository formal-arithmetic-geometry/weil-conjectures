/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.InternalCurrying
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence

/-!
# The categorical trace, and internal duals of dualizable objects

In a braided monoidal category, an object `X` with a right dual `Xᘁ` has an
`ExactPairing X Xᘁ`, hence a coevaluation `𝟙_ C ⟶ X ⊗ Xᘁ` and an evaluation
`Xᘁ ⊗ X ⟶ 𝟙_ C`. The *trace* of an endomorphism `f : X ⟶ X` is the resulting
endomorphism of the unit object.

This is the categorical trace used by the Lefschetz trace formula: for
`C = Perf(R) ⊆ D(R)` it is the usual trace of an endomorphism of a perfect complex,
and `End (𝟙_ C) = R`.

## Main definitions

- `CategoryTheory.MonoidalCategory.trace`: the trace of an endomorphism of a dualizable
  object; it does not depend on the choice of the dual
  (`CategoryTheory.MonoidalCategory.trace_eq_of_exactPairing`) and is preserved by braided
  monoidal functors (`CategoryTheory.Functor.map_trace`).
- `CategoryTheory.MonoidalCategory.ihomUnitIsoRightDual`: in a braided monoidal closed
  category, the internal dual `ihom X (𝟙_ C)` of an object with a right dual `Xᘁ` is `Xᘁ`.

- `CategoryTheory.MonoidalClosed.toIhomIhomUnit`: the canonical biduality map
  `X ⟶ [[X, 𝟙_ C], 𝟙_ C]` of a braided monoidal closed category.

## Main statements

- `CategoryTheory.MonoidalClosed.isIso_toIhomIhomUnit`: the biduality map of an object with a
  right dual is an isomorphism.

- `CategoryTheory.IsDualizable.ihom_unit`: in a braided monoidal closed category, the internal
  dual of a dualizable object is dualizable.

## Implementation notes

In a merely braided category the two ways of turning `X ⊗ Xᘁ` into `Xᘁ ⊗ X` differ, and
`trace` uses `(β_ X Xᘁ).hom`. In the symmetric case, which is the one the trace formula
uses, the two agree.
-/

@[expose] public section

namespace CategoryTheory.MonoidalCategory

open Functor.LaxMonoidal Functor.OplaxMonoidal

variable {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]

/-- The trace of an endomorphism `f : X ⟶ X` of an object with a right dual `Xᘁ` is the
composite

```
       η_ X Xᘁ        f ▷ Xᘁ        β_ X Xᘁ        ε_ X Xᘁ
  𝟙_ C ──────→ X ⊗ Xᘁ ──────→ X ⊗ Xᘁ ──────→ Xᘁ ⊗ X ──────→ 𝟙_ C
```

of the coevaluation, `f ⊗ 𝟙`, the braiding and the evaluation. For the symmetric monoidal
category `(Perf R, ⊗ᴸ_R, R)` of perfect complexes over a commutative ring `R` this is
`tr_R(f | P)`, an element of `End (𝟙_ C) = R`
(blueprint: `sk-d-trace`). -/
noncomputable def trace {X : C} [HasRightDual X] (f : X ⟶ X) : 𝟙_ C ⟶ 𝟙_ C :=
  η_ X Xᘁ ≫ f ▷ Xᘁ ≫ (β_ X Xᘁ).hom ≫ ε_ X Xᘁ

/-- The trace does not depend on the choice of the right dual: it can be computed with any
exact pairing `X ⊗ Y`. -/
lemma trace_eq_of_exactPairing {X : C} [HasRightDual X] (Y : C) [ExactPairing X Y]
    (f : X ⟶ X) :
    trace f = η_ X Y ≫ f ▷ Y ≫ (β_ X Y).hom ≫ ε_ X Y := by
  let e := rightDualIso (inferInstance : ExactPairing X Xᘁ) (inferInstance : ExactPairing X Y)
  have h₁ : η_ X Xᘁ ≫ X ◁ e.hom = η_ X Y := by
    have := @coevaluation_comp_rightAdjointMate C _ _ X X ⟨Y⟩ ⟨Xᘁ⟩ (𝟙 X)
    rw [id_whiskerRight, Category.comp_id] at this
    exact this
  have h₂ : e.hom ▷ X ≫ ε_ X Y = ε_ X Xᘁ := by
    have := @rightAdjointMate_comp_evaluation C _ _ X X ⟨Y⟩ ⟨Xᘁ⟩ (𝟙 X)
    rw [whiskerLeft_id, Category.id_comp] at this
    exact this
  rw [trace, ← h₂, ← h₁]
  simp only [Category.assoc]
  congr 1
  rw [BraidedCategory.braiding_naturality_left_assoc,
    BraidedCategory.braiding_naturality_left_assoc,
    BraidedCategory.braiding_naturality_right_assoc, whisker_exchange_assoc]

section

variable {D : Type*} [Category D] [MonoidalCategory D] [BraidedCategory D]

/-- **A braided monoidal functor preserves traces.** For a braided monoidal functor `F` and an
endomorphism `f` of a dualizable object `X` such that `F X` is dualizable,
`tr(F f) = ε⁻¹ ∘ F(tr f) ∘ ε`, where `ε : 𝟙_ ⟶ F 𝟙_` is the unit of `F`. -/
lemma _root_.CategoryTheory.Functor.map_trace (F : C ⥤ D) [F.Braided] {X : C} [HasRightDual X]
    [HasRightDual (F.obj X)] (f : X ⟶ X) :
    trace (F.map f) = ε F ≫ F.map (trace f) ≫ η F := by
  let := ExactPairing.map F X Xᘁ
  rw [trace_eq_of_exactPairing (F.obj Xᘁ), trace]
  change (ε F ≫ F.map (η_ X Xᘁ) ≫ δ F X Xᘁ) ≫ F.map f ▷ F.obj Xᘁ ≫ (β_ _ _).hom ≫
    μ F Xᘁ X ≫ F.map (ε_ X Xᘁ) ≫ η F = _
  simp only [Category.assoc, Functor.map_comp]
  congr 2
  rw [Functor.Monoidal.map_whiskerRight, Functor.map_braiding]
  simp only [Category.assoc, Functor.Monoidal.μ_δ_assoc]

end

/-- In a braided monoidal closed category, the internal hom `[X, 𝟙_ C]` out of an object `X`
with a right dual `Xᘁ` is isomorphic to `Xᘁ`: both `ihom X` and `tensorRight Xᘁ` are right
adjoint to `X ⊗ - ≅ - ⊗ X`. -/
noncomputable def ihomUnitIsoRightDual [MonoidalClosed C] (X : C) [HasRightDual X] :
    (ihom X).obj (𝟙_ C) ≅ Xᘁ :=
  ((ihom.adjunction X).rightAdjointUniq ((tensorRightAdjunction X Xᘁ).ofNatIsoLeft
      (BraidedCategory.tensorLeftIsoTensorRight X).symm)).app _ ≪≫ λ_ _

end CategoryTheory.MonoidalCategory

namespace CategoryTheory

open MonoidalCategory

variable {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C]

/-- In a braided monoidal closed category, the internal dual `[X, 𝟙_ C]` of a dualizable
object `X` is dualizable, with right dual `X`. -/
theorem IsDualizable.ihom_unit {X : C} (hX : IsDualizable X) :
    IsDualizable ((ihom X).obj (𝟙_ C)) := by
  obtain ⟨_⟩ := hX
  let := BraidedCategory.exactPairing_swap X Xᘁ
  let := exactPairingCongrLeft (Y := X) (ihomUnitIsoRightDual X)
  exact ⟨⟨X⟩⟩

namespace MonoidalClosed

/-- The canonical biduality map `X ⟶ [[X, 𝟙_ C], 𝟙_ C]` of a braided monoidal closed category:
the transpose of
```
                       β_                         ev
  [X, 𝟙_ C] ⊗ X ──────────→ X ⊗ [X, 𝟙_ C] ──────────→ 𝟙_ C.
```
-/
noncomputable def toIhomIhomUnit (X : C) : X ⟶ (ihom ((ihom X).obj (𝟙_ C))).obj (𝟙_ C) :=
  curry ((β_ _ X).hom ≫ (ihom.ev X).app (𝟙_ C))

/-- In a braided monoidal closed category, the canonical biduality map
`X ⟶ [[X, 𝟙_ C], 𝟙_ C]` of an object with a right dual is an isomorphism. -/
theorem isIso_toIhomIhomUnit (X : C) [HasRightDual X] : IsIso (toIhomIhomUnit X) := by
  -- `Xᘁ` is a left dual of `X` for the evaluation `X ⊗ Xᘁ ≅ Xᘁ ⊗ X ⟶ 𝟙_ C` along the inverse
  -- braiding, which identifies `[X, 𝟙_ C]` with `Xᘁ` compatibly with `β_`.
  let := @BraidedCategory.exactPairing_swap C _ _ (reverseBraiding C) X Xᘁ _
  have hε : ε_ Xᘁ X = (β_ Xᘁ X).inv ≫ ε_ X Xᘁ := rfl
  let e := ihomObjUnitIso Xᘁ X
  have h : toIhomIhomUnit X ≫ (pre e.inv).app (𝟙_ C) = curry (ε_ X Xᘁ) := by
    rw [toIhomIhomUnit, curry_pre_app, BraidedCategory.braiding_naturality_left_assoc,
      ← curry_evaluation, whiskerLeft_curry_ihom_ev_app, hε, Iso.hom_inv_id_assoc]
  have : IsIso ((pre e.inv).app (𝟙_ C)) :=
    ⟨(pre e.hom).app (𝟙_ C), by simp [← NatTrans.comp_app, ← pre_map], by
      simp [← NatTrans.comp_app, ← pre_map]⟩
  have : IsIso (toIhomIhomUnit X ≫ (pre e.inv).app (𝟙_ C)) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((pre e.inv).app (𝟙_ C))

section

variable (Y X : C) [ExactPairing Y X] (e : Y ⊗ X ≅ 𝟙_ C)

/-- **Twisting by an invertible object cancels in internal homs.** If `Y` and `X` form an exact
pairing with `Y ⊗ X ≅ 𝟙_ C`, then `[A ⊗ X, Z] ⊗ X ≅ [X, [A, Z]] ⊗ X ≅ (Y ⊗ [A, Z]) ⊗ X ≅ [A, Z]`.
-/
noncomputable def ihomTensorObjWhiskerRightIso (A Z : C) :
    (ihom (A ⊗ X)).obj Z ⊗ X ≅ (ihom A).obj Z :=
  whiskerRightIso (ihomCurryIso A X Z ≪≫ ihomObjIsoTensor Y X _ ≪≫ β_ Y _) X ≪≫ α_ _ _ _ ≪≫
    whiskerLeftIso _ e ≪≫ ρ_ _

/-- The isomorphism `[A ⊗ X, Z] ⊗ X ≅ [A, Z]` is natural in `A`. -/
@[reassoc]
lemma pre_whiskerRight_app_whiskerRight_comp_ihomTensorObjWhiskerRightIso_hom {A A' : C}
    (f : A' ⟶ A) (Z : C) :
    (pre (f ▷ X)).app Z ▷ X ≫ (ihomTensorObjWhiskerRightIso Y X e A' Z).hom =
      (ihomTensorObjWhiskerRightIso Y X e A Z).hom ≫ (pre f).app Z := by
  simp only [ihomTensorObjWhiskerRightIso, ihomObjIsoTensor, Iso.trans_hom, whiskerRightIso_hom,
    Iso.app_hom, whiskerLeftIso_hom, comp_whiskerRight, Category.assoc]
  rw [← comp_whiskerRight_assoc, pre_whiskerRight_app_comp_ihomCurryIso_hom,
    comp_whiskerRight_assoc, ← comp_whiskerRight_assoc ((ihom X).map _),
    (ihomIsoTensorLeft Y X).hom.naturality, curriedTensor_obj_map, comp_whiskerRight_assoc,
    ← comp_whiskerRight_assoc (Y ◁ _), BraidedCategory.braiding_naturality_right,
    comp_whiskerRight_assoc, associator_naturality_left_assoc, ← whisker_exchange_assoc,
    rightUnitor_naturality]

end

end MonoidalClosed

end CategoryTheory
