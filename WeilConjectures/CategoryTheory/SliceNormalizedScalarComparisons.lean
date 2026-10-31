/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SliceTensorGeneratorInterfaces

/-! # Intermediate generator comparisons

Source: Stacks Project, Modules on Sites, Tags 03DI, 03CY, 03EK and 0E8I.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules.LocalizedStrictTensor

namespace SheafOfModules.SliceTensorGenerator

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]

variable (R : Sheaf J CommRingCat.{max c v r}) (V : C)
  [HasSheafify (J.over V) AddCommGrpCat.{max c v r}]
  [(J.over V).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]

/-- Normalized scalar restriction and scalar extension across a slice.
Source: Stacks 03DI, 03CY, 03EK and 0E8I; scalar-action part of
lem-sf-cbc-slice-tensor-generator-coherence, Steps 2 and 4.
(blueprint: lem-sf-slice-normalized-scalar-comparisons).

Proof: Restricting scalars leaves the direct-sum extension presheaf and its
restriction maps unchanged. Sheafification therefore gives k, the identity on
original summands. Its uniqueness follows by the sheafification adjunction and
direct-sum extensionality. Construct l by the scalar-extension adjunction and
the slice-extension adjunction, whose composed right adjoints agree. Their
adjunction units send m to [m] and to 1 tensor m, respectively. Thus l sends
s tensor [m] to [s tensor m], by linearity over the coefficient ring. Apply the
scalar-extension adjunction, then direct-sum extensionality, to show that this
formula uniquely determines l. This construction includes only the scalar
comparisons; it makes no assertion about ordinary tensors or towers. -/
theorem scalarComparisons_exists :
    ∃ (k : ∀ A : Under R,
    scalars.{max c v, v, r} (R.over V) ((sliceAlgebras.{c, v, r} R V).obj A) ⋙
        localizedSystemExtension.{c, v, r} R V ≅
      localizedSystemExtension.{c, v, r} A.right V ⋙ scalars.{c, v, r} R A)
      (l : ∀ A : Under R, LinearComparison.{c, v, r} R V A),
      (∀ A,
    ScalarExtensionNormalized.{c, v, r} R V A (k A)) ∧
      (∀ A e,
    ScalarExtensionNormalized.{c, v, r} R V A e → e = k A) ∧
      (∀ A, LinearNormalized.{c, v, r} R V A (l A)) ∧
      (∀ A e, LinearNormalized.{c, v, r} R V A e → e = l A) := by sorry

end SheafOfModules.SliceTensorGenerator
