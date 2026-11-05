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
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal

/-!
# Finite free coordinates for internal scalar extension

Source: blueprint main-20261015, `sec-proetale-coefficients`,
`sk-prop-sfb-cartesian-coefficients/lem-sfb-subfield-flat.proof.md`, last sentence,
first inference (blueprint: lem-sfb-finite-free-scalar-coordinates).

The formulas are equalities of morphisms involving the canonical coequalizer projection.
They consequently specify the formulas on local elementary tensors without identifying
sections of a tensor sheaf with objectwise tensors. Finite products represent the finite
powers and, in an additive category, also the finite direct sums.
-/

@[expose] public section

set_option autoImplicit false

universe u v uC vC w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonObj

namespace CategoryTheory.Mod

section Coordinates

variable {H : Type u} [Category.{v} H] [MonoidalCategory H] [BraidedCategory H]
  [Abelian H] [MonoidalPreadditive H] [HasCoequalizers H]
  [∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : H, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  {R B : H} [MonObj R] [MonObj B] [IsCommMonObj R] [IsCommMonObj B]
  (φ : R ⟶ B) [IsMonHom φ]

variable {φ} {n : ℕ} (θ : finiteFree R n ≅ (comap φ).obj (regular B))

end Coordinates

end CategoryTheory.Mod
