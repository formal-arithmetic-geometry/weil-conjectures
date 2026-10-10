/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Category

/-!

# Dualizable and invertible objects of a monoidal category

`CategoryTheory.HasRightDual` is a class carrying a right dual as *data*. This file records
the corresponding *property*, `CategoryTheory.IsDualizable X`, that some right dual exists,
together with the stronger property `CategoryTheory.IsInvertible X` that `X` admits a
two-sided tensor inverse (`CategoryTheory.IsInvertible.isDualizable`).

## Main definitions

- `CategoryTheory.IsDualizable`: `X` admits a right dual.
- `CategoryTheory.IsInvertible`: `X` admits a two-sided tensor inverse.
- `CategoryTheory.exactPairingOfTensorIso`: the exact pairing of an object with a two-sided
  tensor inverse.
- `CategoryTheory.MonoidalClosed.ihomIsoTensorLeft`: for an exact pairing of `Y` and `X`, the
  internal hom `ihom X` is `Y ⊗ -`.
- `CategoryTheory.MonoidalClosed.ihomUnitTensorToIhom`: the canonical comparison map
  `(ihom X).obj (𝟙_ C) ⊗ Z ⟶ (ihom X).obj Z`.
- `CategoryTheory.tensorRightCompIsoOfTensorInverse`: for `F ⊣ G ⊣ H` with `F` monoidal and `L`
  invertible, `H (K ⊗ L) ≅ H K ⊗ F L` (co-projection).

## Main statements

- `CategoryTheory.isDualizable_of_tensorIso`, `CategoryTheory.IsInvertible.isDualizable`: an
  object with a two-sided tensor inverse is dualizable.
- `CategoryTheory.MonoidalClosed.curry_evaluation`: the transpose `Y ⟶ (ihom X).obj (𝟙_ C)` of
  the evaluation of an exact pairing of `Y` and `X` is an isomorphism.
- `CategoryTheory.MonoidalClosed.isIso_ihomUnitTensorToIhom`: the comparison map is an
  isomorphism when `X` has a left dual.
- `CategoryTheory.MonoidalClosed.exactPairingOfIsIso`: conversely, if the comparison map
  `(ihom X).obj (𝟙_ C) ⊗ X ⟶ (ihom X).obj X` is an isomorphism, `(ihom X).obj (𝟙_ C)` is a
  left dual of `X`.

-/

@[expose] public section

open CategoryTheory MonoidalCategory

namespace CategoryTheory

variable {C : Type*} [Category C] [MonoidalCategory C]

/-- An object `X` of a monoidal category is *dualizable* if it admits a right dual, that is,
an object `Xᘁ` together with an exact pairing `X ⊗ Xᘁ ⟶ 𝟙_ C`, `𝟙_ C ⟶ Xᘁ ⊗ X`.

Unlike `CategoryTheory.HasRightDual`, which carries the dual as data, this is a `Prop`. -/
def IsDualizable (X : C) : Prop :=
  Nonempty (HasRightDual X)

theorem isDualizable_of_hasRightDual (X : C) [HasRightDual X] : IsDualizable X :=
  ⟨inferInstance⟩

theorem isDualizable_unit : IsDualizable (𝟙_ C) :=
  isDualizable_of_hasRightDual _

theorem IsDualizable.tensorObj {X Y : C} (hX : IsDualizable X) (hY : IsDualizable Y) :
    IsDualizable (X ⊗ Y) := by
  obtain ⟨_⟩ := hX
  obtain ⟨_⟩ := hY
  exact ⟨hasRightDualTensor⟩

/-- Dualizability is invariant under isomorphism. -/
theorem IsDualizable.of_iso {X Y : C} (e : X ≅ Y) (hX : IsDualizable X) : IsDualizable Y := by
  obtain ⟨_⟩ := hX
  exact ⟨{ rightDual := Xᘁ, exact := exactPairingCongrLeft e.symm }⟩

/-- An object `X` of a monoidal category is *invertible* if it admits a two-sided tensor
inverse, that is, an object `Y` with `X ⊗ Y ≅ 𝟙_ C` and `Y ⊗ X ≅ 𝟙_ C`. The Tate twists of the
`ℓ`-adic formalism are the motivating example.

Both isomorphisms are required: without a braiding, `X ⊗ Y ≅ 𝟙_ C` alone does not make `X`
invertible (for endofunctors under composition it only says that `X` has a section). -/
def IsInvertible (X : C) : Prop :=
  ∃ Y, Nonempty (X ⊗ Y ≅ 𝟙_ C) ∧ Nonempty (Y ⊗ X ≅ 𝟙_ C)

theorem isInvertible_unit : IsInvertible (𝟙_ C) :=
  ⟨𝟙_ C, ⟨λ_ _⟩, ⟨λ_ _⟩⟩

/-- In a braided monoidal category a one-sided tensor inverse is two-sided. -/
theorem isInvertible_iff_of_braided [BraidedCategory C] (X : C) :
    IsInvertible X ↔ ∃ Y, Nonempty (X ⊗ Y ≅ 𝟙_ C) :=
  ⟨fun ⟨Y, e, _⟩ ↦ ⟨Y, e⟩, fun ⟨Y, ⟨e⟩⟩ ↦ ⟨Y, ⟨e⟩, ⟨β_ Y X ≪≫ e⟩⟩⟩

/-- An object `X` with a two-sided tensor inverse `Y`, `X ⊗ Y ≅ 𝟙_ C ≅ Y ⊗ X`, forms an exact
pairing with `Y`. The coevaluation is the inverse of `X ⊗ Y ≅ 𝟙_ C`; the evaluation is
`Y ⊗ X ≅ 𝟙_ C` corrected by an automorphism of `X` so that the first zigzag identity holds,
and the second zigzag identity then follows, since `- ▷ X` is injective. -/
@[instance_reducible]
noncomputable def exactPairingOfTensorIso {X Y : C} (e : X ⊗ Y ≅ 𝟙_ C) (e' : Y ⊗ X ≅ 𝟙_ C) :
    ExactPairing X Y :=
  let φ : X ⟶ X := (λ_ X).inv ≫ e.inv ▷ X ≫ (α_ X Y X).hom ≫ X ◁ e'.hom ≫ (ρ_ X).hom
  let ε : Y ⊗ X ⟶ 𝟙_ C := Y ◁ inv φ ≫ e'.hom
  have zig : (λ_ X).inv ≫ e.inv ▷ X ≫ (α_ X Y X).hom ≫ X ◁ ε ≫ (ρ_ X).hom = 𝟙 X := by
    have : (λ_ X).inv ≫ e.inv ▷ X ≫ (α_ X Y X).hom ≫ X ◁ ε ≫ (ρ_ X).hom = inv φ ≫ φ := by
      simp only [ε, φ, MonoidalCategory.whiskerLeft_comp, Category.assoc]
      rw [← associator_naturality_right_assoc, ← whisker_exchange_assoc,
        leftUnitor_inv_naturality_assoc]
    rw [this, IsIso.inv_hom_id]
  have zag : (ρ_ Y).inv ≫ Y ◁ e.inv ≫ (α_ Y X Y).inv ≫ ε ▷ Y ≫ (λ_ Y).hom = 𝟙 Y := by
    apply whiskerRight_injective_of_tensorIso e
    rw [id_whiskerRight, ← cancel_mono ε, Category.id_comp]
    calc _ = (ρ_ Y).inv ▷ X ≫ (Y ◁ e.inv) ▷ X ≫ (α_ Y X Y).inv ▷ X ≫ (α_ (Y ⊗ X) Y X).hom ≫
          ε ▷ (Y ⊗ X) ≫ (λ_ (Y ⊗ X)).hom ≫ ε := by monoidal
      _ = (ρ_ Y).inv ▷ X ≫ (Y ◁ e.inv) ▷ X ≫ (α_ Y X Y).inv ▷ X ≫ (α_ (Y ⊗ X) Y X).hom ≫
          (Y ⊗ X) ◁ ε ≫ (ρ_ (Y ⊗ X)).hom ≫ ε := by
        rw [whiskerRight_comp_leftUnitor_hom_comp]
      _ = Y ◁ ((λ_ X).inv ≫ e.inv ▷ X ≫ (α_ X Y X).hom ≫ X ◁ ε ≫ (ρ_ X).hom) ≫ ε := by
        monoidal
      _ = ε := by rw [zig, whiskerLeft_id, Category.id_comp]
  { coevaluation' := e.inv
    evaluation' := ε
    coevaluation_evaluation' := by
      rw [← cancel_epi (ρ_ Y).inv, ← cancel_mono (λ_ Y).hom]
      simpa using zag
    evaluation_coevaluation' := by
      rw [← cancel_epi (λ_ X).inv, ← cancel_mono (ρ_ X).hom]
      simpa using zig }

/-- An object with a two-sided tensor inverse is dualizable. -/
theorem isDualizable_of_tensorIso {X Y : C} (e : X ⊗ Y ≅ 𝟙_ C) (e' : Y ⊗ X ≅ 𝟙_ C) :
    IsDualizable X :=
  letI := exactPairingOfTensorIso e e'
  ⟨⟨Y⟩⟩

/-- An invertible object is dualizable. -/
theorem IsInvertible.isDualizable {X : C} (hX : IsInvertible X) : IsDualizable X := by
  obtain ⟨Y, ⟨e⟩, ⟨e'⟩⟩ := hX
  exact isDualizable_of_tensorIso e e'

/-- The counit of `tensorLeftAdjunction Y X : tensorLeft X ⊣ tensorLeft Y` at `Z` is the composite
```
              α⁻¹                 ε_ Y X ▷ Z            λ_ Z
  X ⊗ (Y ⊗ Z) ───→ (X ⊗ Y) ⊗ Z ──────────→ 𝟙_ C ⊗ Z ─────→ Z.
```
-/
theorem tensorLeftAdjunction_counit_app (Y X : C) [ExactPairing Y X] (Z : C) :
    (tensorLeftAdjunction Y X).counit.app Z = (α_ _ _ _).inv ≫ ε_ Y X ▷ Z ≫ (λ_ Z).hom := by
  simp [tensorLeftAdjunction, tensorLeftHomEquiv]

namespace MonoidalClosed

variable [MonoidalClosed C]

/-- If `Y` is a left dual of `X`, that is, `Y` and `X` form an exact pairing, then the internal
hom `ihom X` of a monoidal closed category is tensoring on the left with `Y`: both are right
adjoint to `X ⊗ -`. -/
noncomputable def ihomIsoTensorLeft (Y X : C) [ExactPairing Y X] : ihom X ≅ tensorLeft Y :=
  (ihom.adjunction X).rightAdjointUniq (tensorLeftAdjunction Y X)

/-- If `Y` is a left dual of `X`, then `(ihom X).obj Z ≅ Y ⊗ Z`. -/
noncomputable def ihomObjIsoTensor (Y X : C) [ExactPairing Y X] (Z : C) :
    (ihom X).obj Z ≅ Y ⊗ Z :=
  (ihomIsoTensorLeft Y X).app Z

/-- If `Y` is a left dual of `X`, then the internal dual `(ihom X).obj (𝟙_ C)` is `Y`. -/
noncomputable def ihomObjUnitIso (Y X : C) [ExactPairing Y X] : (ihom X).obj (𝟙_ C) ≅ Y :=
  ihomObjIsoTensor Y X (𝟙_ C) ≪≫ ρ_ Y

/-- The canonical comparison map `(ihom X).obj (𝟙_ C) ⊗ Z ⟶ (ihom X).obj Z`: the transpose of
`X ⊗ ((ihom X).obj (𝟙_ C) ⊗ Z) ≅ (X ⊗ (ihom X).obj (𝟙_ C)) ⊗ Z ⟶ 𝟙_ C ⊗ Z ≅ Z`, built from
the evaluation `X ⊗ (ihom X).obj (𝟙_ C) ⟶ 𝟙_ C`. -/
noncomputable def ihomUnitTensorToIhom (X Z : C) : (ihom X).obj (𝟙_ C) ⊗ Z ⟶ (ihom X).obj Z :=
  curry ((α_ _ _ _).inv ≫ (ihom.ev X).app (𝟙_ C) ▷ Z ≫ (λ_ Z).hom)

/-- If `Y` is a left dual of `X`, the comparison map is identified with `ihomObjIsoTensor`:
the square
```
                              ihomUnitTensorToIhom X Z
  (ihom X).obj (𝟙_ C) ⊗ Z ──────────────────────────→ (ihom X).obj Z
              │                                              │
  (ihomObjUnitIso Y X).hom ▷ Z               (ihomObjIsoTensor Y X Z).hom
              ↓                                              ↓
            Y ⊗ Z ═══════════════════════════════════════ Y ⊗ Z
```
commutes. -/
theorem ihomUnitTensorToIhom_eq (Y X : C) [ExactPairing Y X] (Z : C) :
    ihomUnitTensorToIhom X Z = (ihomObjUnitIso Y X).hom ▷ Z ≫ (ihomObjIsoTensor Y X Z).inv := by
  have h₁ := (ihom.adjunction X).rightAdjointUniq_hom_app_counit (tensorLeftAdjunction Y X) (𝟙_ C)
  have h₂ := (tensorLeftAdjunction Y X).rightAdjointUniq_hom_app_counit (ihom.adjunction X) Z
  rw [tensorLeftAdjunction_counit_app] at h₁ h₂
  dsimp only [ihom.ihom_adjunction_counit] at h₁ h₂
  simp only [curriedTensor_obj_map] at h₁ h₂
  simp only [ihomUnitTensorToIhom, curry_eq_iff, uncurry_eq, ihomObjUnitIso, ihomObjIsoTensor,
    ihomIsoTensorLeft, Iso.trans_hom, Iso.app_inv, Adjunction.rightAdjointUniq_inv_app,
    Iso.app_hom]
  rw [← h₁, MonoidalCategory.whiskerLeft_comp_assoc, h₂]
  monoidal

/-- If `Y` is a left dual of `X`, the transpose `Y ⟶ (ihom X).obj (𝟙_ C)` of the evaluation
`ε_ Y X : X ⊗ Y ⟶ 𝟙_ C` is the inverse of `ihomObjUnitIso Y X`. -/
theorem curry_evaluation (Y X : C) [ExactPairing Y X] :
    curry (ε_ Y X) = (ihomObjUnitIso Y X).inv := by
  have h₁ := (ihom.adjunction X).rightAdjointUniq_hom_app_counit (tensorLeftAdjunction Y X) (𝟙_ C)
  rw [tensorLeftAdjunction_counit_app] at h₁
  dsimp only [ihom.ihom_adjunction_counit] at h₁
  rw [curry_eq_iff, uncurry_eq, ← h₁]
  simp only [ihomObjUnitIso, ihomObjIsoTensor, ihomIsoTensorLeft, Iso.trans_inv, Iso.app_inv,
    curriedTensor_obj_map, MonoidalCategory.whiskerLeft_comp_assoc]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc X
    (((ihom.adjunction X).rightAdjointUniq (tensorLeftAdjunction Y X)).inv.app (𝟙_ C)),
    Iso.inv_hom_id_app]
  monoidal

instance isIso_curry_evaluation (Y X : C) [ExactPairing Y X] :
    IsIso (curry (ε_ Y X)) := by
  rw [curry_evaluation]
  infer_instance

/-- If `X` has a left dual, the comparison map `(ihom X).obj (𝟙_ C) ⊗ Z ⟶ (ihom X).obj Z` is an
isomorphism. -/
theorem isIso_ihomUnitTensorToIhom (Y X : C) [ExactPairing Y X] (Z : C) :
    IsIso (ihomUnitTensorToIhom X Z) := by
  rw [ihomUnitTensorToIhom_eq Y X]
  infer_instance

/-- The transpose of `ihomUnitTensorToIhom X Z` is evaluation of the first factor:
```
X ⊗ ([X, 𝟙] ⊗ Z) --X ◁ ihomUnitTensorToIhom--> X ⊗ [X, Z]
        |                                          |
       α⁻¹                                        ev
        v                                          v
(X ⊗ [X, 𝟙]) ⊗ Z ------ev ▷ Z------> 𝟙 ⊗ Z ---λ---> Z
```
-/
lemma whiskerLeft_ihomUnitTensorToIhom_ev (X Z : C) :
    X ◁ ihomUnitTensorToIhom X Z ≫ (ihom.ev X).app Z =
      (α_ _ _ _).inv ≫ (ihom.ev X).app (𝟙_ C) ▷ Z ≫ (λ_ Z).hom := by
  rw [← uncurry_eq, ihomUnitTensorToIhom, uncurry_curry]

variable (X : C) [IsIso (ihomUnitTensorToIhom X X)]

/-- If the comparison map `(ihom X).obj (𝟙_ C) ⊗ X ⟶ (ihom X).obj X` is an isomorphism, the
coevaluation `𝟙_ C ⟶ (ihom X).obj (𝟙_ C) ⊗ X` is the preimage of the transpose of `ρ_ X`. -/
noncomputable def coevaluationOfIsIso : 𝟙_ C ⟶ (ihom X).obj (𝟙_ C) ⊗ X :=
  curry (ρ_ X).hom ≫ inv (ihomUnitTensorToIhom X X)

/-- The first zigzag identity for `coevaluationOfIsIso`. -/
lemma coevaluationOfIsIso_evaluation :
    X ◁ coevaluationOfIsIso X ≫ (α_ _ _ _).inv ≫ (ihom.ev X).app (𝟙_ C) ▷ X =
      (ρ_ X).hom ≫ (λ_ X).inv := by
  rw [← cancel_mono (λ_ X).hom, Category.assoc, Category.assoc, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, ← whiskerLeft_ihomUnitTensorToIhom_ev, coevaluationOfIsIso,
    ← MonoidalCategory.whiskerLeft_comp_assoc, Category.assoc, IsIso.inv_hom_id,
    Category.comp_id, ← uncurry_eq, uncurry_curry]

/-- The second zigzag identity for `coevaluationOfIsIso`. -/
lemma evaluation_coevaluationOfIsIso :
    coevaluationOfIsIso X ▷ (ihom X).obj (𝟙_ C) ≫ (α_ _ _ _).hom ≫
      (ihom X).obj (𝟙_ C) ◁ (ihom.ev X).app (𝟙_ C) =
      (λ_ _).hom ≫ (ρ_ _).inv := by
  apply (cancel_mono (ρ_ _).hom).1
  apply cancel_epi (λ_ _).inv |>.1
  apply uncurry_injective
  simp only [uncurry_eq, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    MonoidalCategory.whiskerLeft_comp]
  set D := (ihom X).obj (𝟙_ C)
  set e : X ⊗ D ⟶ 𝟙_ C := (ihom.ev X).app (𝟙_ C)
  have key : X ◁ D ◁ e ≫ X ◁ (ρ_ D).hom ≫ e =
      (α_ X D (X ⊗ D)).inv ≫ e ▷ (X ⊗ D) ≫ (λ_ _).hom ≫ e := by
    rw [MonoidalCategory.whiskerLeft_rightUnitor, Category.assoc,
      associator_inv_naturality_right_assoc, ← rightUnitor_naturality, whisker_exchange_assoc,
      ← unitors_equal, leftUnitor_naturality]
  rw [key, MonoidalCategory.whiskerLeft_id, Category.id_comp]
  have z := coevaluationOfIsIso_evaluation X
  calc _ = X ◁ (λ_ D).inv ≫ (α_ X (𝟙_ C) D).inv ≫
        (X ◁ coevaluationOfIsIso X ≫ (α_ _ _ _).inv ≫ e ▷ X) ▷ D ≫ (α_ (𝟙_ C) X D).hom ≫
          (λ_ _).hom ≫ e := by monoidal
    _ = e := by rw [z]; monoidal

/-- **A criterion for left duals**: if the comparison map
`(ihom X).obj (𝟙_ C) ⊗ X ⟶ (ihom X).obj X` is an isomorphism, then `(ihom X).obj (𝟙_ C)` is a
left dual of `X`, with evaluation the evaluation of the internal hom. -/
@[instance_reducible]
noncomputable def exactPairingOfIsIso : ExactPairing ((ihom X).obj (𝟙_ C)) X where
  coevaluation' := coevaluationOfIsIso X
  evaluation' := (ihom.ev X).app (𝟙_ C)
  coevaluation_evaluation' := coevaluationOfIsIso_evaluation X
  evaluation_coevaluation' := evaluation_coevaluationOfIsIso X

end MonoidalClosed

section TensorInverse

variable {D : Type*} [Category D] [MonoidalCategory D] {F : C ⥤ D} {G : D ⥤ C} {H : C ⥤ D}
  (adj₁ : F ⊣ G) (adj₂ : G ⊣ H)
  (τ : (Functor.postcompose₂.obj F).obj (curriedTensor C) ≅
    (((Functor.whiskeringLeft₂ D).obj F).obj F).obj (curriedTensor D))
  (η : F.obj (𝟙_ C) ≅ 𝟙_ D) {L M : C} (e₁ : L ⊗ M ≅ 𝟙_ C) (e₂ : M ⊗ L ≅ 𝟙_ C)

/-- A functor `F` with `F (K ⊗ M) ≅ F K ⊗ F M` naturally commutes with tensoring on the right
by an object: `F (K ⊗ L) ≅ F K ⊗ F L`, naturally in `K`. -/
noncomputable def tensorRightCompIsoOfTensorNatIso (L : C) :
    tensorRight L ⋙ F ≅ F ⋙ tensorRight (F.obj L) :=
  NatIso.ofComponents (fun K ↦ (τ.app K).app L) fun f ↦ NatTrans.congr_app (τ.hom.naturality f) L

include adj₁ in
/-- Let `F ⊣ G` with `F` monoidal, and let `L` have a two-sided tensor inverse `M`. Then `G`
commutes with tensoring by `M` up to applying `F` to it: `G A ⊗ M ≅ G (A ⊗ F M)`, naturally in
`A`. Both functors are right adjoint to `K ↦ F (K ⊗ L) ≅ F K ⊗ F L`. -/
noncomputable def compTensorRightIsoOfTensorInverse :
    G ⋙ tensorRight M ≅ tensorRight (F.obj M) ⋙ G :=
  letI := exactPairingOfTensorIso e₁ e₂
  letI := exactPairingOfTensorIso (((τ.app L).app M).symm ≪≫ F.mapIso e₁ ≪≫ η)
    (((τ.app M).app L).symm ≪≫ F.mapIso e₂ ≪≫ η)
  conjugateIsoEquiv ((tensorRightAdjunction L M).comp adj₁)
    (adj₁.comp (tensorRightAdjunction (F.obj L) (F.obj M)))
    (tensorRightCompIsoOfTensorNatIso τ L).symm

/-- **Co-projection.** Let `F ⊣ G ⊣ H` with `F` monoidal, and let `L` have a two-sided tensor
inverse. Then `H` commutes with tensoring by `L` up to applying `F` to it:
`H (K ⊗ L) ≅ H K ⊗ F L`, naturally in `K`. Both functors are right adjoint to
`A ↦ G A ⊗ M ≅ G (A ⊗ F M)`, by `CategoryTheory.compTensorRightIsoOfTensorInverse`. -/
noncomputable def tensorRightCompIsoOfTensorInverse :
    tensorRight L ⋙ H ≅ H ⋙ tensorRight (F.obj L) :=
  letI := exactPairingOfTensorIso e₂ e₁
  letI := exactPairingOfTensorIso (((τ.app M).app L).symm ≪≫ F.mapIso e₂ ≪≫ η)
    (((τ.app L).app M).symm ≪≫ F.mapIso e₁ ≪≫ η)
  conjugateIsoEquiv (adj₂.comp (tensorRightAdjunction M L))
    ((tensorRightAdjunction (F.obj M) (F.obj L)).comp adj₂)
    (compTensorRightIsoOfTensorInverse adj₁ τ η e₁ e₂).symm

end TensorInverse

end CategoryTheory
