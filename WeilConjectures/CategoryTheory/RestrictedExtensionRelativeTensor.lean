/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import WeilConjectures.CategoryTheory.SheafificationTensorLocalIso
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import WeilConjectures.CategoryTheory.RegularScalarExtensionMultiplication

/-!
# Restricted internal scalar extension and relative tensor

Source: blueprint main-20261015, `sec-proetale-coefficients`,
`sk-prop-sfb-cartesian-coefficients/lem-sfb-subfield-flat.proof.md`, last sentence,
first inference (blueprint: lem-sfb-restricted-extension-relative-tensor).

The existing `sfbRegularAbMonoidal` and its symmetric and tensor-colimit instances
specialize `sfbSheafTensorStructure` to abelian sheaves. All quotient projections
and module actions below are those of the published internal-module constructions.
-/

@[expose] public section

set_option autoImplicit false

universe uC vC w

open CategoryTheory CategoryTheory.MonoidalCategory

namespace CategoryTheory.Mod

/-- Restricted extension of scalars is naturally relative tensor with the restricted
regular algebra, normalized by both canonical coequalizer projections. The natural
isomorphism lives in the module category, so its components and inverse are linear,
mutually inverse, and natural for every module morphism.

Source: blueprint main-20261015, `lem-sfb-subfield-flat.proof.md`, last sentence,
first inference (blueprint: lem-sfb-restricted-extension-relative-tensor).

Proof, following the node:
1. Write N = Res_phi(B). Its right action is its restricted left action after braiding.
Braiding naturality and commutativity of B identify it with multiplication after
B tensor phi (`sk-def-sfb-change-of-scalars`, `def-sfb-modobj-relative-tensor`).
2. Thus `extendπ phi M` and `tensorObjπ N M` coequalize exactly the same two maps
from (B tensor R) tensor UM to B tensor UM (`def-sfb-modobj-extension`).
3. Factor each projection through the other coequalizer to obtain maps f and g.
Their composites are identities: precompose with the respective epic quotient
projection, then use the two factorization equations.
4. Check R-linearity of f after precomposition with R tensor `extendπ phi M`.
Tensor preserves this epimorphism by `sk-def-sfb-sheaf-tensor`. The formulas
`whiskerLeft_extendπ_smul` and `whiskerLeft_tensorπ_smul`, together with
associator naturality, identify the two actions. The module isomorphism constructor
supplies linearity of the inverse.
5. Check naturality after precomposing with `extendπ phi M`. The formulas
`extendπ_extendScalarsMap` and `tensorObjπ_whiskerLeft` identify both composites.
Assemble the component isomorphisms with `NatIso.ofComponents`. The factorization
equations give both required normalizations. No freeness is used.
-/
theorem exists_restrictedExtension_relativeTensor
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C)
    (R B : Sheaf J Ab.{w}) [MonObj R] [MonObj B]
    [IsCommMonObj R] [IsCommMonObj B] (φ : R ⟶ B) [IsMonHom φ] :
    ∃ κ : extendScalars φ ⋙ comap φ ≅ tensorLeft ((comap φ).obj (regular B)),
      (∀ M : Mod (Sheaf J Ab.{w}) R,
        extendπ φ M ≫ (κ.hom.app M).hom =
          tensorObjπ ((comap φ).obj (regular B)) M) ∧
      (∀ M : Mod (Sheaf J Ab.{w}) R,
        tensorObjπ ((comap φ).obj (regular B)) M ≫ (κ.inv.app M).hom =
          extendπ φ M) :=
  open CategoryTheory.Limits in
  by
  let N := (comap φ).obj (regular B)
  have h : (β_ B R).hom ≫ (ModObj.smul (M := R) (X := N.X)) = B ◁ φ ≫ (MonObj.mul (X := B)) := by
    change (β_ B R).hom ≫ φ ▷ B ≫ (MonObj.mul (X := B)) = _
    rw [← BraidedCategory.braiding_naturality_right_assoc, IsCommMonObj.mul_comm]
  let f (M : Mod (Sheaf J Ab.{w}) R) :
      (extendScalarsObj φ M).X ⟶ (N ⊗ M).X :=
    extendDescHom φ (tensorObjπ N M) (by
      rw [← h]
      exact tensorObjπ_condition N M)
  let g (M : Mod (Sheaf J Ab.{w}) R) :
      (N ⊗ M).X ⟶ (extendScalarsObj φ M).X :=
    coequalizer.desc (extendπ φ M) (by
      change ((β_ B R).hom ≫ (ModObj.smul (M := R) (X := N.X))) ▷ M.X ≫ extendπ φ M = _
      rw [h]
      exact extendπ_condition φ M)
  have hf (M : Mod (Sheaf J Ab.{w}) R) :
      extendπ φ M ≫ f M = tensorObjπ N M :=
    extendπ_extendDescHom φ _ _
  have hg (M : Mod (Sheaf J Ab.{w}) R) :
      tensorObjπ N M ≫ g M = extendπ φ M := coequalizer.π_desc _ _
  let e (M : Mod (Sheaf J Ab.{w}) R) :
      (comap φ).obj (extendScalarsObj φ M) ≅ N ⊗ M := by
    let underlying : (extendScalarsObj φ M).X ≅ (N ⊗ M).X :=
      { hom := f M
        inv := g M
        hom_inv_id := by
          rw [← cancel_epi (extendπ φ M)]
          simp only [← Category.assoc, hf, hg, Category.comp_id]
        inv_hom_id := by
          rw [← cancel_epi (tensorObjπ N M)]
          simp only [← Category.assoc, hg, hf, Category.comp_id] }
    refine isoMk (M := (comap φ).obj (extendScalarsObj φ M))
      (N := N ⊗ M) underlying ?_
    change (φ ▷ _ ≫ (ModObj.smul (M := B) (X := (extendScalarsObj φ M).X))) ≫ f M =
      R ◁ f M ≫ (ModObj.smul (M := R) (X := (N ⊗ M).X))
    simp only [Category.assoc]
    rw [← cancel_epi (R ◁ extendπ φ M)]
    rw [whisker_exchange_assoc, whiskerLeft_extendπ_smul_assoc,
      ← whiskerLeft_comp_assoc, hf, whiskerLeft_tensorπ_smul]
    erw [associator_inv_naturality_left_assoc, comp_whiskerRight, Category.assoc]
  let κ : extendScalars φ ⋙ comap φ ≅ tensorLeft N :=
    NatIso.ofComponents e (by
      intro M M' u
      apply hom_ext
      rw [← cancel_epi (extendπ φ M)]
      change extendπ φ M ≫ (extendScalarsMap φ u).hom ≫ f M' =
        extendπ φ M ≫ f M ≫ (N ◁ u).hom
      rw [extendπ_extendScalarsMap_assoc, hf, ← Category.assoc, hf,
        tensorObjπ_whiskerLeft]
      rfl)
  exact ⟨κ, hf, hg⟩

end CategoryTheory.Mod
