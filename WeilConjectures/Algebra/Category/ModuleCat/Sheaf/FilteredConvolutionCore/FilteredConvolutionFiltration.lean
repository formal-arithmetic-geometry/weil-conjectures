/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FilteredConvolutionCore.FilteredConvolutionGradedQuotientCore

/-! Construction of the convolution filtration. -/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace SheafOfModules.FilteredConvolutionCore

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {R : Sheaf J CommRingCat.{w}}

/-- The image-sum subobjects form a decreasing filtration of the total tensor.
The proof is the degreewise tensor coherence and the image-subobject universal property.
Source: the convolution filtration step in the blueprint proof.
(blueprint: lem-trf-filtered-convolution-graded-quotient). -/
theorem convolution_filtration_exists
    (P Q : Complex R) (F : DecreasingFiltration P) (G : DecreasingFiltration Q) :
    ∃ H : DecreasingFiltration (P ⊗ Q), ∀ r : ℤ, H.F r = level F G r := by
  sorry

end SheafOfModules.FilteredConvolutionCore
