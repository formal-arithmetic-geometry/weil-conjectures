/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.InternalCurrying
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic

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
  object.
- `CategoryTheory.MonoidalCategory.ihomUnitIsoRightDual`: in a braided monoidal closed
  category, the internal dual `ihom X (𝟙_ C)` of an object with a right dual `Xᘁ` is `Xᘁ`.

- `CategoryTheory.MonoidalClosed.toIhomIhomUnit`: the canonical biduality map
  `X ⟶ [[X, 𝟙_ C], 𝟙_ C]` of a braided monoidal closed category.

## Main statements

- `CategoryTheory.MonoidalClosed.isIso_toIhomIhomUnit`: the biduality map of an object with a
  right dual is an isomorphism.

- `CategoryTheory.IsDualizable.ihom_unit`: in a braided monoidal closed category, the internal
  dual of a dualizable object is dualizable.

- `CategoryTheory.MonoidalClosed.IsPerfectPairing.braiding_hom_comp`,
  `CategoryTheory.MonoidalClosed.isPerfectPairing_braiding_hom_comp_iff`: perfectness of a
  pairing of dualizable objects is symmetric in the two variables.

## Implementation notes

In a merely braided category the two ways of turning `X ⊗ Xᘁ` into `Xᘁ ⊗ X` differ, and
`trace` uses `(β_ X Xᘁ).hom`. In the symmetric case, which is the one the trace formula
uses, the two agree.
-/

@[expose] public section

namespace CategoryTheory.MonoidalCategory

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

/-- A perfect pairing `b : X ⊗ Y ⟶ 𝟙_ C` of a dualizable object `X` is the evaluation of an
exact pairing of `Y` and `X` (`IsPerfectPairing.evaluation_exactPairing`): `Y` is a
left dual of `X`. -/
@[instance_reducible]
noncomputable def IsPerfectPairing.exactPairing {X Y : C} (hX : IsDualizable X)
    {b : X ⊗ Y ⟶ 𝟙_ C} (h : IsPerfectPairing b) : ExactPairing Y X :=
  have := h.isIso
  have : IsIso (ihomUnitTensorToIhom X X) := by
    obtain ⟨_⟩ := hX
    let := BraidedCategory.exactPairing_swap X Xᘁ
    exact isIso_ihomUnitTensorToIhom Xᘁ X X
  let := exactPairingOfIsIso X
  exactPairingCongrLeft (asIso (curry b))

/-- The evaluation of the exact pairing `IsPerfectPairing.exactPairing` of a perfect pairing
`b` is `b`. -/
lemma IsPerfectPairing.evaluation_exactPairing {X Y : C} (hX : IsDualizable X)
    {b : X ⊗ Y ⟶ 𝟙_ C}
    (h : IsPerfectPairing b) :
    letI := h.exactPairing hX
    ε_ Y X = b :=
  uncurry_curry b

/-- Blueprint `rem-ptr-pod-perfect-derived-pairing-6` (pointer to the properties of
`def-pod-perfect-derived-pairing`): perfectness of a pairing is symmetric in the two variables.

If `X` is dualizable and the pairing `b : X ⊗ Y ⟶ 𝟙_ C` is perfect, `Y ≅ [X, 𝟙_ C]`, then the
swapped pairing `Y ⊗ X ⟶ X ⊗ Y ⟶ 𝟙_ C` is perfect as well, `X ≅ [Y, 𝟙_ C]`: `b` is the
evaluation of an exact pairing of `Y` and `X`, and the braiding turns it into an exact pairing
of `X` and `Y` whose evaluation is the swapped pairing. -/
theorem IsPerfectPairing.braiding_hom_comp {X Y : C} (hX : IsDualizable X)
    {b : X ⊗ Y ⟶ 𝟙_ C} (h : IsPerfectPairing b) : IsPerfectPairing ((β_ Y X).hom ≫ b) := by
  let := h.exactPairing hX
  let := BraidedCategory.exactPairing_swap Y X
  have hε : ε_ X Y = (β_ Y X).hom ≫ b := by
    rw [← h.evaluation_exactPairing hX]
    rfl
  exact ⟨hε ▸ isIso_curry_evaluation X Y⟩

/-- Blueprint `rem-ptr-pod-perfect-derived-pairing-6` (pointer to the properties of
`def-pod-perfect-derived-pairing`): perfectness of a pairing is symmetric in the two variables.

In a symmetric monoidal closed category, a pairing `b : X ⊗ Y ⟶ 𝟙_ C` of dualizable objects
(for instance perfect point complexes) is perfect, `Y ≅ [X, 𝟙_ C]`, if and only if the swapped
pairing `Y ⊗ X ⟶ X ⊗ Y ⟶ 𝟙_ C` is perfect, `X ≅ [Y, 𝟙_ C]`. -/
theorem isPerfectPairing_braiding_hom_comp_iff {C : Type*} [Category C] [MonoidalCategory C]
    [SymmetricCategory C] [MonoidalClosed C] {X Y : C} (hX : IsDualizable X)
    (hY : IsDualizable Y) {b : X ⊗ Y ⟶ 𝟙_ C} :
    IsPerfectPairing ((β_ Y X).hom ≫ b) ↔ IsPerfectPairing b := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.braiding_hom_comp hX⟩
  simpa using h.braiding_hom_comp hY

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
