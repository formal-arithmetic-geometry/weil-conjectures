/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.Regular.RegularSequence
import WeilConjectures.AlgebraicGeometry.Morphisms.RegularImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Local regular generators for a smooth diagonal

## References

* [Stacks Project, Tag 067U](https://stacks.math.columbia.edu/tag/067U)
* [Stacks Project, Tag 067R](https://stacks.math.columbia.edu/tag/067R)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The diagonal of a smooth morphism of pure relative dimension `d`, when it is closed,
has on an affine neighbourhood of every point either the unit ideal or an ideal generated
by a regular sequence of length `d`. The ideal is the kernel of the map on sections. -/
theorem exists_isRegular_smooth_diagonal_generators {X S : Scheme.{u}} (d : ℕ)
    (f : X ⟶ S) [SmoothOfRelativeDimension d f] [IsClosedImmersion (pullback.diagonal f)] :
    ∀ w : (pullback f f : Scheme.{u}), ∃ U : (pullback f f).affineOpens, w ∈ U.1 ∧
      (RingHom.ker ((pullback.diagonal f).app U.1).hom = ⊤ ∨
        ∃ r : List Γ(pullback f f, U.1), r.length = d ∧
          RingTheory.Sequence.IsRegular Γ(pullback f f, U.1) r ∧
          Ideal.ofList r = RingHom.ker ((pullback.diagonal f).app U.1).hom) := by
  classical
  intro w
  let Δ := pullback.diagonal f
  by_cases hw : w ∈ Set.range Δ
  · by_cases hzero : d = 0
    · subst d
      have : Etale f := (Etale.iff_smoothOfRelativeDimension_zero f).mpr inferInstance
      have : IsOpenImmersion Δ := inferInstance
      obtain ⟨_, ⟨U, hU, rfl⟩, hwU, hle⟩ :=
        (pullback f f).isBasis_affineOpens.exists_subset_of_mem_open
          hw Δ.isOpenEmbedding.isOpen_range
      have happ : IsIso (Δ.app U) := Scheme.Hom.isIso_app Δ U hle
      have hker : RingHom.ker (Δ.app U).hom = ⊥ :=
        (RingHom.injective_iff_ker_eq_bot _).mp
          (ConcreteCategory.bijective_of_isIso (Δ.app U)).1
      have : Nontrivial Γ(pullback f f, U) :=
        ((pullback f f).presheaf.germ U w hwU).hom.domain_nontrivial
      refine ⟨⟨U, hU⟩, hwU, Or.inr ⟨[], rfl, ?_, ?_⟩⟩
      · exact ⟨by simp, by simp⟩
      · simpa using hker.symm
    · let : NeZero d := ⟨hzero⟩
      let : IsSeparated f := ⟨inferInstance⟩
      obtain ⟨U, hwU, r, hr, hreg, hI⟩ :=
        IsRegularImmersion.exists_isWeaklyRegular_generators
          (c := d) (i := Δ) w
      have hker : Ideal.ofList r = RingHom.ker (Δ.app U.1).hom := by
        simpa only [Scheme.Hom.ker_apply] using hI
      refine ⟨U, hwU, Or.inr ⟨r, hr, ⟨hreg, ?_⟩, hker⟩⟩
      rw [Ideal.smul_eq_mul, Ideal.mul_top, hker]
      intro heq
      have hone : (Δ.app U.1).hom 1 = 0 := by
        exact RingHom.mem_ker.mp (heq ▸ (show (1 : Γ(pullback f f, U.1)) ∈ ⊤ from trivial))
      obtain ⟨x, rfl⟩ := hw
      have : Nontrivial Γ(X, Δ ⁻¹ᵁ U.1) :=
        (X.presheaf.germ (Δ ⁻¹ᵁ U.1) x hwU).hom.domain_nontrivial
      simp at hone
  · obtain ⟨_, ⟨U, hU, rfl⟩, hwU, hle⟩ :=
      (pullback f f).isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_compl hw) Δ.isClosedEmbedding.isClosed_range.isOpen_compl
    have hempty : Δ ⁻¹ᵁ U = ⊥ := by
      ext x
      simpa using fun hx : Δ x ∈ U ↦ hle hx ⟨x, rfl⟩
    have : Subsingleton Γ(X, Δ ⁻¹ᵁ U) := hempty ▸ inferInstance
    refine ⟨⟨U, hU⟩, hwU, Or.inl ?_⟩
    rw [Ideal.eq_top_iff_one, RingHom.mem_ker]
    exact Subsingleton.elim _ _

end AlgebraicGeometry
