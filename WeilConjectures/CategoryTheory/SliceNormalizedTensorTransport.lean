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

variable (R : Sheaf J CommRingCat.{max c v r})

/-- The ordinary tensor is scalar extension followed by restriction, with the
original pure-tensor normalization.
Source: Stacks 03EK and 03CY; tensor-identification part of
lem-sf-cbc-slice-tensor-generator-coherence, Step 3.
(blueprint: lem-sf-slice-normalized-tensor-transport).

Proof: On presheaves use tensor symmetry to identify M tensor S with the
underlying R-module of S tensor M. The balanced relations are precisely those
of scalar extension. This identification commutes with restriction maps and
with maps of M. Sheafification commutes with scalar restriction: both have the
same underlying abelian sheafification and the same uniquely extended action.
Sheafify the presheaf identification and compose with this comparison.
The sheafification-unit equations give the displayed formula on pure tensors.
Naturality follows by comparing these formulas, since pure tensors generate
before sheafification and the adjunction detects maps after sheafification.
This argument applies to any site, including the slice site. -/
theorem tensorTransport_exists :
    ∃ t : ∀ A : Under R, TensorLift.{c, v, r} R A,
      ∀ A, TensorLiftNormalized.{c, v, r} R A (t A) := by sorry

end SheafOfModules.SliceTensorGenerator
