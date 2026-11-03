/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FilteredConvolutionCore.FilteredConvolutionGradedQuotientCore
public import Mathlib.CategoryTheory.Category.Basic

/-! The canonical comparison map for a convolution graded quotient. -/
@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace SheafOfModules.FilteredConvolutionCore
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {R : Sheaf J CommRingCat.{w}}

/-- The quotient projections of the convolution summands induce a unique map to the
associated graded of the image filtration.  The proof is the two cokernel universal
properties, using preservation of coproducts and cokernels by the sheaf tensor product.
Source: the second step of the proof of `lem-trf-filtered-convolution-graded-quotient`.
(blueprint: lem-trf-filtered-convolution-graded-quotient). -/
theorem canonical_comparison_unique
    {P Q : Complex R} (F : DecreasingFiltration P) (G : DecreasingFiltration Q)
    (H : DecreasingFiltration (P ⊗ Q)) (hH : ∀ r : ℤ, H.F r = level F G r) (r : ℤ) :
    ∃! α : gradedSource F G r ⟶ H.gradedPiece r, IsCanonical F G H r α := by
  sorry

end SheafOfModules.FilteredConvolutionCore
