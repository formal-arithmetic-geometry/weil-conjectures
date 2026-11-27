/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralRationalQbarCompactSupport
public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison

import all WeilConjectures.SmoothPurity.Sf.SfCompleteDirectImageReduction
import WeilConjectures.SmoothPurity.CompletedCoefficientPushforward.CompletedCoefficientPushforwardComparison
import Mathlib.Data.Nat.Prime.Infinite

/-!
# Proper direct image preserves derived completeness

## Implementation details

The coefficient adjunction identifies the ringed pushforward with
`sfCompletedModuleDirectImage`. Choosing an auxiliary prime distinct from `l` gives the
normalized completed-coefficient comparison package, whose `completed_image_complete`
consequence in `SfCompleteDirectImageReduction` gives completeness of the total right-derived
image.

## References

* [Bhatt--Scholze, *The pro-étale topology for schemes*, Lemmas 6.1.13 and 6.7.7]
* [Stacks Project, Tags 099N, 0E8I and 0F7J]
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open PurCompactSupport

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
  {X Y : Scheme.{u}} {f : X ⟶ Y}
  [Xbase : X.Over (Spec (.of K₀))] [Ybase : Y.Over (Spec (.of K₀))]
  [Xft : LocallyOfFiniteType (X ↘ Spec (.of K₀))]
  [Xqc : QuasiCompact (X ↘ Spec (.of K₀))]
  [Yft : LocallyOfFiniteType (Y ↘ Spec (.of K₀))]
  [Yqc : QuasiCompact (Y ↘ Spec (.of K₀))]
  [fbase : f.IsOver (Spec (.of K₀))] [fs : IsSeparated f]
  [fft : LocallyOfFiniteType f] [fqc : QuasiCompact f]
  (c : Compactification f)

include K₀ hl Xbase Ybase Xft Xqc Yft Yqc fbase fs fft fqc

-- Keep the section hypotheses of this public statement.
set_option linter.unusedSectionVars false in
attribute [-instance] CompletedCoefficientPushforward.modAbelian
  CompletedCoefficientPushforward.hasDerived in
/-- The proper direct image of a complete completed-coefficient complex is
complete. This is the proper factor of the compact-support image argument. -/
theorem sfQcqsCompactSupport_proper_complete
    (M : DerivedCategory (scalarReductionSource l E c.Z))
    (hM : IsSfDerivedComplete l E c.Z M) :
    IsSfDerivedComplete l E Y
      ((proEtaleRingDerivedDirectImage c.g ((completed l E).ring Y)
        ((completed l E).ring c.Z) ((completed l E).pull c.g)).obj M) := by
  have he : proEtaleRingDirectImageMap c.g ((completed l E).ring Y)
      ((completed l E).ring c.Z) ((completed l E).pull c.g) =
      sfCompletedCoefficientMap l E c.g := by
    exact ((proEtaleSheafAdjunction c.g CommRingCat.{u + 1}).homEquiv _ _).apply_symm_apply _
  have hF : proEtaleRingModuleDirectImage c.g ((completed l E).ring Y)
      ((completed l E).ring c.Z) ((completed l E).pull c.g) =
      sfCompletedModuleDirectImage l E c.g := by
    unfold proEtaleRingModuleDirectImage sfCompletedModuleDirectImage
    rw [he]
  have := sfCompletedModuleDirectImage_additive l E c.g
  let e : proEtaleRingDerivedDirectImage c.g ((completed l E).ring Y)
      ((completed l E).ring c.Z) ((completed l E).pull c.g) ≅
      sfCompletedDerivedDirectImage l E c.g :=
    Functor.rightDerivedFunctorNatIso (eqToIso hF)
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (l + 1)
  have : Fact p.Prime := ⟨hprime⟩
  have hlp : l ≠ p := by omega
  obtain ⟨D⟩ := CompletedCoefficientPushforward.comparison l E c.g p hlp
  exact complete_iso l E Y (e.app M).symm (completed_image_complete l E c.g D M hM)

end WeilConjectures
