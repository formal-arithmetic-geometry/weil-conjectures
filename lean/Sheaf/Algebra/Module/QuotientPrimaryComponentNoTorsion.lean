/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Mathlib.Algebra.Module.Torsion.PrimaryComponent

/-!
# The quotient by ideal-power torsion has no ideal torsion

Source: Stacks Project, More on Algebra, Lemma 05EB (lemma-divide-by-torsion), part (1)
(blueprint: lem-weil-pbc-quotient-by-power-torsion-no-torsion).
-/

@[expose] public section

universe u v

namespace Ideal

/-- Every class in the quotient by the `I`-power torsion submodule that is annihilated
by every element of `I` is zero, when `I` is finitely generated.
Source: Stacks Project, More on Algebra, Lemma 05EB (lemma-divide-by-torsion), part (1)
(blueprint: lem-weil-pbc-quotient-by-power-torsion-no-torsion).

The submodule `primaryComponent M I` is exactly `M[I^∞]`: allowing exponent zero adds
only the zero element, which is also killed by `I^1`.

Proof:
1. Put `T = M[I^∞]`. It is a submodule because powers killing two elements can be
replaced by their maximum, and scalar multiplication preserves annihilation. A lift `x`
of a class annihilated by `I` satisfies `a • x ∈ T` for every `a ∈ I`, by the quotient
kernel criterion.
2. Choose a finite generating set `s` of `I`. For each generator `a`, choose an
exponent `n(a)` such that `I^n(a)` kills `a • x`. Let `N` be the maximum of these
exponents, using zero for the empty set. Monotonicity of ideal-power torsion shows
that `I^N` kills each `a • x`.
3. The preimage of the `I^N`-torsion submodule under the linear map `r ↦ r • x`
is a submodule containing the generators, hence contains `I`. Thus `I^N` kills
`a • x` for every `a ∈ I`. Since `I^(N+1) = I^N * I`, the ideal multiplication
criterion shows that `I^(N+1)` kills `x`.
4. Hence `x ∈ T`, so its quotient class is zero. The maximum construction also
handles the empty generating set: then `I = 0` and `I^1` kills every element.
All steps use only Mathlib's submodule and ideal arithmetic.
-/
theorem eq_zero_of_annihilated_quotient_primaryComponent
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (I : Ideal R) (hI : I.FG) (x : M ⧸ primaryComponent M I)
    (hx : ∀ a : R, a ∈ I → a • x = 0) : x = 0 := by
  classical
  obtain ⟨y, rfl⟩ := (primaryComponent M I).mkQ_surjective x
  have hy (a : R) (ha : a ∈ I) : a • y ∈ primaryComponent M I := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    simpa using hx a ha
  obtain ⟨s, hs⟩ := hI
  have hgens (a : s) : ∃ n : ℕ, a.val • y ∈
      Submodule.torsionBySet R M ↑(I ^ n) := by
    apply (primaryComponent_mem M I _).mp
    apply hy
    rw [← hs]
    exact Submodule.subset_span a.property
  choose n hn using hgens
  let N := s.attach.sup n
  let f := LinearMap.toSpanSingleton R M y
  have hbound : I ≤ (Submodule.torsionBySet R M ↑(I ^ N)).comap f := by
    apply hs.symm.le.trans
    apply Submodule.span_le.mpr
    intro a ha
    change a • y ∈ Submodule.torsionBySet R M ↑(I ^ N)
    apply Submodule.torsionBySet_le_torsionBySet_pow (n ⟨a, ha⟩) N _ I
      (hn ⟨a, ha⟩)
    exact Finset.le_sup (f := n) (s.mem_attach ⟨a, ha⟩)
  have hkill : I ^ (N + 1) ≤ f.ker := by
    rw [pow_succ, Ideal.mul_le]
    intro b hb a ha
    change (b * a) • y = 0
    rw [mul_smul]
    exact (Submodule.mem_torsionBySet_iff _ _).mp (hbound ha) ⟨b, hb⟩
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  apply (primaryComponent_mem M I y).mpr
  refine ⟨N + 1, (Submodule.mem_torsionBySet_iff _ _).mpr ?_⟩
  intro a
  exact hkill a.property

end Ideal
