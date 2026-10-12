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
  object.
- `CategoryTheory.MonoidalCategory.ihomUnitIsoRightDual`: in a braided monoidal closed
  category, the internal dual `ihom X (𝟙_ C)` of an object with a right dual `Xᘁ` is `Xᘁ`.

- `CategoryTheory.MonoidalClosed.toIhomIhom`: the double-dual map `X ⟶ [[X, W], W]` relative to
  an object `W`, natural in `X` (`CategoryTheory.MonoidalClosed.toIhomIhomNatTrans`).
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

/-- The canonical double-dual map `X ⟶ [[X, W], W]` relative to an object `W` of a braided
monoidal closed category: the transpose of
```
                 β_                  ev
  [X, W] ⊗ X ──────────→ X ⊗ [X, W] ──────────→ W.
```
For `W = 𝟙_ C` it is `CategoryTheory.MonoidalClosed.toIhomIhomUnit`. -/
noncomputable def toIhomIhom (W X : C) : X ⟶ (ihom ((ihom X).obj W)).obj W :=
  curry ((β_ _ X).hom ≫ (ihom.ev X).app W)

lemma uncurry_toIhomIhom (W X : C) :
    uncurry (toIhomIhom W X) = (β_ _ X).hom ≫ (ihom.ev X).app W :=
  uncurry_curry _

/-- The double-dual map is natural: for `f : X ⟶ Y` the square
```
  X ───────── f ─────────→ Y
  │                        │
  toIhomIhom W X     toIhomIhom W Y
  ↓                        ↓
  [[X, W], W] ─[[f, W], W]→ [[Y, W], W]
```
commutes. -/
@[reassoc]
lemma toIhomIhom_naturality (W : C) {X Y : C} (f : X ⟶ Y) :
    f ≫ toIhomIhom W Y = toIhomIhom W X ≫ (pre ((pre f).app W)).app W := by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_pre_app, uncurry_toIhomIhom, uncurry_toIhomIhom,
    BraidedCategory.braiding_naturality_right_assoc, BraidedCategory.braiding_naturality_left_assoc,
    id_tensor_pre_app_comp_ev]

/-- The double-dual maps `X ⟶ [[X, W], W]` as a natural transformation from the identity to
the square of the contravariant functor `[-, W]`. -/
@[simps]
noncomputable def toIhomIhomNatTrans (W : C) :
    𝟭 C ⟶ (internalHom.flip.obj W).rightOp ⋙ internalHom.flip.obj W where
  app X := toIhomIhom W X
  naturality _ _ f := toIhomIhom_naturality W f

/-- The double-dual map is extranatural in the dualizing object: for `g : W ⟶ W'` both ways
from `X` to `[[X, W], W']`,
```
  X ──── toIhomIhom W X ────→ [[X, W], W]
  │                               │
  toIhomIhom W' X           [[X, W], g]
  ↓                               ↓
  [[X, W'], W'] ──[[X, g], W']──→ [[X, W], W']
```
agree. -/
@[reassoc]
lemma toIhomIhom_comp_ihom_map {W W' : C} (g : W ⟶ W') (X : C) :
    toIhomIhom W X ≫ (ihom _).map g = toIhomIhom W' X ≫ (pre ((ihom X).map g)).app W' := by
  apply uncurry_injective
  rw [uncurry_natural_right, uncurry_toIhomIhom, uncurry_pre_app, uncurry_toIhomIhom,
    BraidedCategory.braiding_naturality_left_assoc, Category.assoc, ihom.ev_naturality]

section Functor

variable {D : Type*} [Category D] [MonoidalCategory D] [BraidedCategory D] [MonoidalClosed D]

open Functor.LaxMonoidal in
/-- The double-dual map is compatible with lax braided functors: for `G : C ⥤ D` lax braided
between braided monoidal closed categories, with comparison maps `c : G [A, B] ⟶ [G A, G B]`
(`CategoryTheory.Functor.LaxMonoidal.ihomComparison`), the square
```
  G X ─────────── G δ ───────────→ G [[X, W], W]
   │                                    │
   δ                                    c
   ↓                                    ↓
  [[G X, G W], G W] ──[c, G W]──→ [G [X, W], G W]
```
commutes, where `δ` is `CategoryTheory.MonoidalClosed.toIhomIhom`. -/
@[reassoc]
lemma map_toIhomIhom_comp_ihomComparison (G : C ⥤ D) [G.LaxBraided] (W X : C) :
    G.map (toIhomIhom W X) ≫ (ihomComparison G ((ihom X).obj W)).natTrans.app W =
      toIhomIhom (G.obj W) (G.obj X) ≫
        (pre ((ihomComparison G X).natTrans.app W)).app (G.obj W) := by
  apply uncurry_injective
  rw [uncurry_pre_app, uncurry_toIhomIhom, uncurry_natural_left, uncurry_eq,
    ihomComparison_ev, μ_natural_right_assoc, ← G.map_comp, ← uncurry_eq, uncurry_toIhomIhom,
    G.map_comp, Functor.LaxBraided.braided_assoc, BraidedCategory.braiding_naturality_left_assoc,
    ihomComparison_ev]

open Functor.LaxMonoidal in
/-- If the comparison maps `G [A, B] ⟶ [G A, G B]` of a lax braided functor `G` are
isomorphisms, then `G` carries the double-dual map `X ⟶ [[X, W], W]` to an isomorphism if and
only if the double-dual map `G X ⟶ [[G X, G W], G W]` is an isomorphism
(`CategoryTheory.MonoidalClosed.map_toIhomIhom_comp_ihomComparison`). -/
lemma isIso_map_toIhomIhom_iff (G : C ⥤ D) [G.LaxBraided] (W X : C)
    [IsIso ((ihomComparison G X).natTrans.app W)]
    [IsIso ((ihomComparison G ((ihom X).obj W)).natTrans.app W)] :
    IsIso (G.map (toIhomIhom W X)) ↔ IsIso (toIhomIhom (G.obj W) (G.obj X)) := by
  have h := map_toIhomIhom_comp_ihomComparison G W X
  constructor
  · intro
    have : IsIso (toIhomIhom (G.obj W) (G.obj X) ≫
        (pre ((ihomComparison G X).natTrans.app W)).app (G.obj W)) := by
      rw [← h]
      infer_instance
    exact IsIso.of_isIso_comp_right _ ((pre ((ihomComparison G X).natTrans.app W)).app _)
  · intro
    have : IsIso (G.map (toIhomIhom W X) ≫
        (ihomComparison G ((ihom X).obj W)).natTrans.app W) := by
      rw [h]
      infer_instance
    exact IsIso.of_isIso_comp_right _ ((ihomComparison G ((ihom X).obj W)).natTrans.app W)

open Functor.LaxMonoidal in
/-- The double-dual map under a lax braided functor `G` with a map `ε : G W ⟶ W'`, for instance
a direct image with the counit `Rf_* ω_X ⟶ ω_Y`: the comparison
`φ_X : G [X, W] ⟶ [G X, G W] ⟶ [G X, W']` carries `G δ` to `δ`,
```
  G X ─────────── G δ ───────────→ G [[X, W], W]
   │                                    │
   δ                                    φ
   ↓                                    ↓
  [[G X, W'], W'] ───[φ, W']───→ [G [X, W], W']
```
-/
@[reassoc]
lemma map_toIhomIhom_comp_ihomComparison_comp_ihom_map (G : C ⥤ D) [G.LaxBraided] (W X : C)
    {W' : D} (ε : G.obj W ⟶ W') :
    G.map (toIhomIhom W X) ≫ (ihomComparison G ((ihom X).obj W)).natTrans.app W ≫
        (ihom _).map ε =
      toIhomIhom W' (G.obj X) ≫
        (pre ((ihomComparison G X).natTrans.app W ≫ (ihom _).map ε)).app W' := by
  rw [map_toIhomIhom_comp_ihomComparison_assoc, pre_comm_ihom_map,
    toIhomIhom_comp_ihom_map_assoc, pre_map, NatTrans.comp_app]

open Functor.LaxMonoidal in
/-- If the comparisons `φ_X : G [X, W] ⟶ [G X, W']` of
`CategoryTheory.MonoidalClosed.map_toIhomIhom_comp_ihomComparison_comp_ihom_map` are
isomorphisms, then `G` carries the double-dual map `X ⟶ [[X, W], W]` to an isomorphism if and
only if the double-dual map `G X ⟶ [[G X, W'], W']` is an isomorphism. -/
lemma isIso_map_toIhomIhom_iff_of_isIso_comp (G : C ⥤ D) [G.LaxBraided] (W X : C)
    {W' : D} (ε : G.obj W ⟶ W')
    [IsIso ((ihomComparison G X).natTrans.app W ≫ (ihom _).map ε)]
    [IsIso ((ihomComparison G ((ihom X).obj W)).natTrans.app W ≫ (ihom _).map ε)] :
    IsIso (G.map (toIhomIhom W X)) ↔ IsIso (toIhomIhom W' (G.obj X)) := by
  have h := map_toIhomIhom_comp_ihomComparison_comp_ihom_map G W X ε
  constructor
  · intro
    have : IsIso (toIhomIhom W' (G.obj X) ≫
        (pre ((ihomComparison G X).natTrans.app W ≫ (ihom _).map ε)).app W') := by
      rw [← h]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      ((pre ((ihomComparison G X).natTrans.app W ≫ (ihom _).map ε)).app W')
  · intro
    have : IsIso (G.map (toIhomIhom W X) ≫
        (ihomComparison G ((ihom X).obj W)).natTrans.app W ≫ (ihom _).map ε) := by
      rw [h]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      ((ihomComparison G ((ihom X).obj W)).natTrans.app W ≫ (ihom _).map ε)

end Functor

/-- The canonical biduality map `X ⟶ [[X, 𝟙_ C], 𝟙_ C]` of a braided monoidal closed category:
the transpose of
```
                       β_                         ev
  [X, 𝟙_ C] ⊗ X ──────────→ X ⊗ [X, 𝟙_ C] ──────────→ 𝟙_ C.
```
-/
noncomputable def toIhomIhomUnit (X : C) : X ⟶ (ihom ((ihom X).obj (𝟙_ C))).obj (𝟙_ C) :=
  curry ((β_ _ X).hom ≫ (ihom.ev X).app (𝟙_ C))

/-- The double-dual map relative to the unit is `toIhomIhomUnit`. -/
lemma toIhomIhom_unit (X : C) : toIhomIhom (𝟙_ C) X = toIhomIhomUnit X := rfl

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

/-- **Duality into an invertible object.** In a braided monoidal closed category, for a
dualizable `K` and an invertible `ω`, the double `ω`-dual of `K` is `K`:
`[[K, ω], ω] ≅ K`. Indeed `[K, ω] ≅ Kᘁ ⊗ ω`, whose left dual is `M ⊗ K` for a tensor inverse `M`
of `ω`, so `[[K, ω], ω] ≅ (M ⊗ K) ⊗ ω ≅ K ⊗ (M ⊗ ω) ≅ K`. -/
theorem nonempty_iso_ihom_obj_ihom_obj_of_isInvertible {K ω : C} (hK : IsDualizable K)
    (hω : IsInvertible ω) :
    Nonempty ((ihom ((ihom K).obj ω)).obj ω ≅ K) := by
  obtain ⟨_⟩ := hK
  obtain ⟨M, ⟨e⟩, ⟨e'⟩⟩ := hω
  let : ExactPairing M ω := exactPairingOfTensorIso e' e
  let : ExactPairing Kᘁ K := BraidedCategory.exactPairing_swap K Kᘁ
  let : ExactPairing (M ⊗ K) ((ihom K).obj ω) :=
    exactPairingCongrRight (MonoidalClosed.ihomObjIsoTensor Kᘁ K ω)
  exact ⟨MonoidalClosed.ihomObjIsoTensor (M ⊗ K) ((ihom K).obj ω) ω ≪≫
    whiskerRightIso (β_ M K) ω ≪≫ α_ K M ω ≪≫ whiskerLeftIso K e' ≪≫ ρ_ K⟩


section ExternalHom

variable {C₁ C₂ : Type*} [Category C₁] [Category C₂] [MonoidalCategory C₁] [MonoidalCategory C₂]
  [BraidedCategory C₁] [BraidedCategory C₂] [MonoidalClosed C₁] [MonoidalClosed C₂]
  (F₁ : C₁ ⥤ C) (F₂ : C₂ ⥤ C) [F₁.Monoidal] [F₂.Monoidal]

/-- The rearrangement `(a ⊗ b) ⊗ (c ⊗ d) ≅ (c ⊗ a) ⊗ (b ⊗ d)` in a braided monoidal category. -/
noncomputable def tensorTensorRearrangeIso (a b c d : C) :
    (a ⊗ b) ⊗ (c ⊗ d) ≅ (c ⊗ a) ⊗ (b ⊗ d) :=
  α_ a b (c ⊗ d) ≪≫ whiskerLeftIso a (α_ b c d).symm ≪≫
    whiskerLeftIso a (whiskerRightIso (β_ b c) d) ≪≫ whiskerLeftIso a (α_ c b d) ≪≫
    (α_ a c (b ⊗ d)).symm ≪≫ whiskerRightIso (β_ a c) (b ⊗ d)

/-- **The external Hom map for dualizable objects.** For monoidal functors `F₁ : C₁ ⥤ C`,
`F₂ : C₂ ⥤ C` into a braided monoidal closed category and dualizable `E₁`, `E₂`,
`F₁ [E₁, N₁] ⊗ F₂ [E₂, N₂] ≅ [F₁ E₁ ⊗ F₂ E₂, F₁ N₁ ⊗ F₂ N₂]`: both sides are
`F₂ E₂ᘁ ⊗ F₁ E₁ᘁ ⊗ F₁ N₁ ⊗ F₂ N₂` up to rearrangement, internal homs out of dualizable objects
being tensor products with their duals. -/
theorem nonempty_iso_tensorObj_map_ihom_obj {E₁ N₁ : C₁} {E₂ N₂ : C₂} (h₁ : IsDualizable E₁)
    (h₂ : IsDualizable E₂) :
    Nonempty (F₁.obj ((ihom E₁).obj N₁) ⊗ F₂.obj ((ihom E₂).obj N₂) ≅
      (ihom (F₁.obj E₁ ⊗ F₂.obj E₂)).obj (F₁.obj N₁ ⊗ F₂.obj N₂)) := by
  obtain ⟨_⟩ := h₁
  obtain ⟨_⟩ := h₂
  let _ : ExactPairing E₁ᘁ E₁ := BraidedCategory.exactPairing_swap E₁ E₁ᘁ
  let _ : ExactPairing E₂ᘁ E₂ := BraidedCategory.exactPairing_swap E₂ E₂ᘁ
  let _ : ExactPairing (F₁.obj E₁) (F₁.obj E₁ᘁ) := ExactPairing.map F₁ E₁ E₁ᘁ
  let _ : ExactPairing (F₂.obj E₂) (F₂.obj E₂ᘁ) := ExactPairing.map F₂ E₂ E₂ᘁ
  let _ : ExactPairing (F₂.obj E₂ᘁ ⊗ F₁.obj E₁ᘁ) (F₁.obj E₁ ⊗ F₂.obj E₂) :=
    BraidedCategory.exactPairing_swap _ _
  exact ⟨(F₁.mapIso (MonoidalClosed.ihomObjIsoTensor E₁ᘁ E₁ N₁) ⊗ᵢ
      F₂.mapIso (MonoidalClosed.ihomObjIsoTensor E₂ᘁ E₂ N₂)) ≪≫
    ((Functor.Monoidal.μIso F₁ _ _).symm ⊗ᵢ (Functor.Monoidal.μIso F₂ _ _).symm) ≪≫
    tensorTensorRearrangeIso _ _ _ _ ≪≫
    (MonoidalClosed.ihomObjIsoTensor (F₂.obj E₂ᘁ ⊗ F₁.obj E₁ᘁ) _ _).symm⟩

omit [MonoidalCategory C₁] [BraidedCategory C₁] [MonoidalClosed C₁] [F₁.Monoidal] in
/-- **The Künneth–Verdier map for a dualizable second factor.** For monoidal functors
`F₁ : C₁ ⥤ C`, `F₂ : C₂ ⥤ C` into a braided monoidal closed category and a dualizable `N`,
`F₁ M ⊗ F₂ [N, ω] ≅ [F₂ N, F₁ M ⊗ F₂ ω]`: both sides are `F₂ Nᘁ ⊗ F₁ M ⊗ F₂ ω`. -/
theorem nonempty_iso_tensorObj_map_ihom_obj_right (M : C₁) {N : C₂} (ω : C₂)
    (hN : IsDualizable N) :
    Nonempty (F₁.obj M ⊗ F₂.obj ((ihom N).obj ω) ≅
      (ihom (F₂.obj N)).obj (F₁.obj M ⊗ F₂.obj ω)) := by
  obtain ⟨_⟩ := hN
  let _ : ExactPairing Nᘁ N := BraidedCategory.exactPairing_swap N Nᘁ
  let _ : ExactPairing (F₂.obj Nᘁ) (F₂.obj N) := ExactPairing.map F₂ Nᘁ N
  exact ⟨whiskerLeftIso (F₁.obj M) (F₂.mapIso (MonoidalClosed.ihomObjIsoTensor Nᘁ N ω) ≪≫
      (Functor.Monoidal.μIso F₂ _ _).symm) ≪≫ (α_ _ _ _).symm ≪≫
    whiskerRightIso (β_ _ _) _ ≪≫ α_ _ _ _ ≪≫
    (MonoidalClosed.ihomObjIsoTensor (F₂.obj Nᘁ) (F₂.obj N) _).symm⟩

end ExternalHom

end CategoryTheory
