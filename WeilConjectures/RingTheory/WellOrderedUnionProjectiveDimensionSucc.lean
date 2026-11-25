/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GlobalDimension
import WeilConjectures.RingTheory.ProjectiveResolutionSuccSplice
public import Mathlib.Order.RelClasses
public import Mathlib.LinearAlgebra.Quotient.Defs
import WeilConjectures.RingTheory.WellOrderedUnionProjectivePresentation

/-!
# succ case of the well-ordered union argument

The successor step of Auslander's well-ordered union argument for projective dimension.

## Implementation details

The Stacks proof uses free presentations of the stages; to keep exact universe generality we
use the projective presentations supplied by `hquot` instead. The direct sum of their
degree-zero terms is formed over the (small) set of indices with nonzero quotient, so that
everything stays in `ModuleCat.{v} R` without constructing a free module in universe
`max u v`. The kernel of the resulting surjection inherits a well-ordered filtration whose
subquotients have length-`n` resolutions by dimension shifting (Schanuel), and the induction
hypothesis is spliced with the presentation.

## References

* Stacks Project, Algebra, Lemma 0D1U (positive-bound case) and Lemma 065S (1).
-/

@[expose] public section

universe u v w

namespace ModuleCat

set_option linter.unusedVariables false in
/-- Successor step in Auslander's well-ordered union argument: assuming the length-`n`
statement `hIH`, if every subquotient `F e / sup_{i < e} F i` of a well-ordered exhaustive
filtration of `M` has a projective resolution of length `n + 1`, then so does `M`. -/
theorem hasProjectiveResolutionLE_of_wellOrderedUnion_succ
    {R : Type u} [CommRing R] (n : ℕ)
    (hIH : ∀ (M : ModuleCat.{v} R) {E : Type w} [LinearOrder E]
      [IsWellOrder E (· < ·)] (F : E → Submodule R M) (hF : Monotone F)
      (hcover : ∀ x : M, ∃ e : E, x ∈ F e)
      (hquot : ∀ e : E, HasProjectiveResolutionLE
        (ModuleCat.of R ((F e) ⧸
          ((⨆ e' : {i : E // i < e}, F e'.val).comap (F e).subtype))) n),
      HasProjectiveResolutionLE M n)
    (M : ModuleCat.{v} R) {E : Type w} [LinearOrder E]
    [IsWellOrder E (· < ·)] (F : E → Submodule R M) (hF : Monotone F)
    (hcover : ∀ x : M, ∃ e : E, x ∈ F e)
    (hquot : ∀ e : E, HasProjectiveResolutionLE
      (ModuleCat.of R ((F e) ⧸
        ((⨆ e' : {i : E // i < e}, F e'.val).comap (F e).subtype))) (n + 1)) :
    HasProjectiveResolutionLE M (n + 1) := by
  obtain ⟨S, hSM, hS, hproj, hker⟩ :=
    exists_shortExact_projective_middle_of_wellOrderedUnion_succ n hIH M F hF hcover hquot
  rw [← hSM]
  exact hasProjectiveResolutionLE_of_shortExact_projective_middle n S hS hproj hker

end ModuleCat
