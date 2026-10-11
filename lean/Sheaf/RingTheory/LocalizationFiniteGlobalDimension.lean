/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
import Sheaf.RingTheory.GlobalDimension
import Mathlib.Algebra.Module.LocalizedModule.Basic

/-!
# Localization and finite global dimension

Source: Stacks Project, Algebra, Lemma 00O8
(blueprint: lem-weil-pbc-localization-finite-gl-dim).
-/

universe u v

namespace Ring

/-- Localization preserves bounds on projective resolution lengths and global dimension.
Source: Stacks Project, Algebra, Lemma 00O8
(blueprint: lem-weil-pbc-localization-finite-gl-dim).

Proof:
1. Localize a projective resolution term by term. Every three-term piece remains exact,
   including the end pieces, by `lem-weil-pbc-localization-module-exact` (Stacks 00CS).
2. Each localized term is projective by `lem-weil-pbc-localization-projective` (05A3).
   The resulting resolution has the same length, proving the first assertion.
3. Regard any module over the localized ring as an R-module and apply the first assertion.
   By `lem-weil-pbc-localization-module-over-localization`, its localization is isomorphic
   to itself. Composing the augmentation with this isomorphism gives the desired resolution,
   proving the uniform global dimension bound.
4. Apply that bound at the least bound for R. The least bound for the localization is no
   larger, proving finite global dimension and the inequality of global dimensions. -/
theorem localization_preserves_projective_and_global_dimension
    (R : Type u) [CommRing R] (S : Submonoid R) (n : ℕ) :
    (∀ M : ModuleCat.{max u v} R,
      ModuleCat.HasProjectiveResolutionLE M n →
        ModuleCat.HasProjectiveResolutionLE
          (ModuleCat.of (Localization S) (LocalizedModule S M)) n) ∧
    (HasGlobalDimensionLE.{u, max u v} R n →
      HasGlobalDimensionLE.{u, max u v} (Localization S) n) ∧
    (∀ h : HasFiniteGlobalDimension.{u, max u v} R,
      ∃ hS : HasFiniteGlobalDimension.{u, max u v} (Localization S),
        globalDimension.{u, max u v} (Localization S) hS ≤
          globalDimension.{u, max u v} R h) := by
  sorry

end Ring
