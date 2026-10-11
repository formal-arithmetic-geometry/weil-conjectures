/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Basic

/-!
# Homogeneous pieces of a module localized at one element

Source: Stacks Project, Cohomology of Schemes, Tag 09MR, Mayer–Vietoris paragraph
(blueprint: def-sc-localized-homogeneous-piece).
-/

@[expose] public section

universe uHP vHP

namespace LocalizedModule

/-- The homogeneous degree `n` fractions in a module localized at `s`, when `s` has degree
`d`: a representative `m / s^k` has numerator in degree `n + k*d`. In particular `n = 0`
gives the degree-zero part used in Stacks, Tag 09MR, Mayer–Vietoris paragraph.
This defines the underlying set, without requiring closure proofs or a chosen decomposition
of the localization. For a compatible grading these sets are additive subgroups.
(blueprint: def-sc-localized-homogeneous-piece) -/
def homogeneousPieceAway {A : Type uHP} [CommRing A] {M : Type vHP} [AddCommGroup M]
    [Module A M] (𝓜 : ℤ → AddSubgroup M) (s : A) (d n : ℤ) : Set (LocalizedModule.Away s M) :=
  {x | ∃ (k : ℕ) (m : M), m ∈ 𝓜 (n + (k : ℤ) * d) ∧
    mk m (⟨s ^ k, ⟨k, rfl⟩⟩ : Submonoid.powers s) = x}

end LocalizedModule
