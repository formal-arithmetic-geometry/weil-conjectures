/-
Copyright (c) 2026 The Weil Conjectures Project Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# Low-degree vanishing from the homology sequence

For a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of cochain complexes, the long exact
homology sequence kills the homology of `X₁` in degrees `0` and `1` as soon as `X₃` has no
homology in degree `-1`, `X₂` has no homology in degree `1` and `X₂ ⟶ X₃` is an isomorphism
in degree-`0` homology.
-/

@[expose] public section

namespace CochainComplex

open CategoryTheory Limits

variable {C : Type*} [Category* C] [Abelian C]

/-- Low-degree vanishing in the long exact homology sequence of a short exact sequence
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of cochain complexes: if `X₃` has no homology in degree `-1`,
`X₂` has no homology in degree `1` and `X₂ ⟶ X₃` is an isomorphism in degree-`0` homology,
then `X₁` has no homology in degrees `0` and `1`. -/
lemma isZero_homology_zero_one_of_shortExact
    {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact)
    (h₃ : IsZero (S.X₃.homology (-1))) (h₂ : IsZero (S.X₂.homology 1))
    (hg : IsIso (HomologicalComplex.homologyMap S.g 0)) :
    IsZero (S.X₁.homology 0) ∧ IsZero (S.X₁.homology 1) := by
  constructor
  · have hmono : Mono (HomologicalComplex.homologyMap S.f 0) :=
      (hS.homology_exact₁ (-1) 0 (by simp)).mono_g (h₃.eq_of_src _ _)
    have hzero : HomologicalComplex.homologyMap S.f 0 = 0 := by
      rw [← cancel_mono (HomologicalComplex.homologyMap S.g 0), zero_comp,
        ← HomologicalComplex.homologyMap_comp, S.zero, HomologicalComplex.homologyMap_zero]
    exact IsZero.of_mono_eq_zero _ hzero
  · have hepi : Epi (hS.δ 0 1 (by simp)) :=
      (hS.homology_exact₁ 0 1 (by simp)).epi_f (h₂.eq_of_tgt _ _)
    have hzero : hS.δ 0 1 (by simp) = 0 := by
      rw [← cancel_epi (HomologicalComplex.homologyMap S.g 0), comp_zero]
      exact hS.comp_δ 0 1 (by simp)
    exact IsZero.of_epi_eq_zero _ hzero

end CochainComplex
