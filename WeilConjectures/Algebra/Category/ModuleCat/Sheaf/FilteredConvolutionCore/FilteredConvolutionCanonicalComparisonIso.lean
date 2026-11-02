/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FilteredConvolutionCore.FilteredConvolutionGradedQuotientCore
public import Mathlib.CategoryTheory.Category.Basic

/-! Isomorphism of the canonical convolution graded comparison. -/
@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace SheafOfModules.FilteredConvolutionCore
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {R : Sheaf J CommRingCat.{w}}

/-- Under finite bounds, termwise split projections in the first filtration and flat
first graded terms identify the canonical comparison with the associated graded
isomorphism.  The proof is the degreewise finite split calculation and exactness of
flat tensoring, followed by totalization and the Koszul differential check.
Source: Steps 3--6 of the proof of `lem-trf-filtered-convolution-graded-quotient`.
(blueprint: lem-trf-filtered-convolution-graded-quotient). -/
theorem canonical_comparison_isIso
    {P Q : Complex R} (F : DecreasingFiltration P) (G : DecreasingFiltration Q)
    (a b c d : ℤ) (hPa : F.F a = ⊤) (hPb : F.F (b + 1) = ⊥)
    (hQc : G.F c = ⊤) (hQd : G.F (d + 1) = ⊥)
    (hSplit : ∀ p n : ℤ,
      IsSplitEpi ((F.complexQuotientπ p (p + 1) (by omega)).f n))
    (hFlat : ∀ p n : ℤ, IsFlatOnSite (R := R) ((F.gradedPiece p).X n))
    (H : DecreasingFiltration (P ⊗ Q)) (hH : ∀ r : ℤ, H.F r = level F G r)
    (r : ℤ) (α : gradedSource F G r ⟶ H.gradedPiece r)
    (hα : IsCanonical F G H r α) : IsIso α := by
  sorry

end SheafOfModules.FilteredConvolutionCore
