/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.NumberTheory.Padics.IntegersAlgebra
public import WeilConjectures.SixFunctors.ProEtale.Adic.ConstantCohomologicalDimension
public import WeilConjectures.SixFunctors.ProEtale.Adic.SubfieldSheafColimit

/-!
# Cohomological dimension of `E_X` for a finite extension `E` of `ℚ_ℓ`

Let `S` be a scheme of finite type and of dimension at most `d` over a separably closed field,
and `E ⊆ ℚ̄_ℓ` a finite extension of `ℚ_ℓ` with ring of integers `𝒪_E`. The pro-étale cohomology
of the abelian sheaves `𝒪_{E,S} = C(-, 𝒪_E)` and `E_S = C(-, E)` vanishes in degrees `q > 2d`.

For `𝒪_E` this is the profinite case
(`AlgebraicGeometry.ProEtale.subsingleton_H_continuousSheaf_of_profinite`), with the open
subgroups of `𝒪_E` given by the balls of radius `1 / (m + 1)`. For `E` it follows since
`E_S = 𝒪_{E,S}[1/ℓ]` is the filtered colimit of the tower `𝒪_{E,S} --ℓ--> 𝒪_{E,S} --ℓ--> ⋯`
(`AlgebraicGeometry.ProEtale.isColimitPadicSubfieldSheafCocone`) and pro-étale cohomology of the
qcqs scheme `S` commutes with filtered colimits
(`AlgebraicGeometry.Scheme.ProEt.subsingleton_H_of_isColimit_of_isFiltered`).

## Main statements

- `AlgebraicGeometry.ProEtale.subsingleton_H_padicIntegersSheaf_of_two_mul_lt`: the vanishing of
  `Hᵠ(S_proét, 𝒪_E)` for `q > 2d`.
- `AlgebraicGeometry.ProEtale.subsingleton_H_padicSubfieldSheaf_of_two_mul_lt`
  (blueprint `theorem-trace-isomorphism-top-degree--6`): the vanishing of `Hᵠ(S_proét, E)` for
  `q > 2d`.
-/

@[expose] public section

universe u

open CategoryTheory Limits PadicAlgCl

namespace AlgebraicGeometry.ProEtale

variable {K : Type u} [Field K] [IsSepClosed K] {S : Scheme.{u}} (a : S ⟶ Spec (.of K))
  [LocallyOfFiniteType a] [QuasiCompact a] (d : ℕ)
  (hS : topologicalKrullDim S ≤ (d : WithBot ℕ∞)) (l : ℕ) [Fact l.Prime] (E : Type) [Field E]
  [Algebra E (PadicAlgCl l)] [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]
  [FiniteDimensional ℚ_[l] E]

include a hS

/-- **Cohomological dimension of `𝒪_E`.** For a scheme `S` of finite type and of dimension at
most `d` over a separably closed field and a finite extension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`,
`Hᵠ(S_proét, 𝒪_E) = 0` for `q > 2d`: `𝒪_E` is compact, with the decreasing sequence of open
subgroups `{x | ‖x‖ < 1 / (m + 1)}` of trivial intersection. -/
theorem subsingleton_H_padicIntegersSheaf_of_two_mul_lt (q : ℕ) (hq : 2 * d < q) :
    letI := normedFieldOfAlgebra l E
    Subsingleton (Sheaf.H (continuousMapAbSheaf S (integers l E)) q) := by
  let := normedFieldOfAlgebra l E
  have := isUltrametricDist_ofAlgebra l E
  have := compactSpace_integers l E
  let U : ℕ → OpenAddSubgroup (integers l E) := fun m ↦
    IsUltrametricDist.ball_openAddSubgroup (integers l E) (r := 1 / ((m : ℝ) + 1)) (by positivity)
  refine subsingleton_H_continuousSheaf_of_profinite a d hS U (fun m x hx ↦ ?_)
    (fun x hx ↦ ?_) q hq
  · refine Metric.mem_ball.2 (lt_of_lt_of_le (Metric.mem_ball.1 hx) ?_)
    gcongr
    linarith
  · rw [← dist_eq_zero]
    refine le_antisymm (le_of_forall_pos_lt_add fun ε hε ↦ ?_) dist_nonneg
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
    exact (Metric.mem_ball.1 (hx m)).trans (by simpa using hm)

/-- Blueprint `theorem-trace-isomorphism-top-degree--6` (vanishing with coefficients in a finite
extension `E` of `ℚ_ℓ`): for a scheme `S` of finite type and of dimension at most `d` over a
separably closed field (for instance `X` smooth of pure dimension `d` over an algebraically
closed `k`) and a finite extension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, the pro-étale cohomology
`Hᵠ(S_proét, E_S)` of the abelian sheaf `E_S = C(-, E)` vanishes for `q > 2d`; there is no
cohomology in negative degrees. As `E_S = 𝒪_{E,S}[1/ℓ]` is the filtered colimit of
`𝒪_{E,S} --ℓ--> 𝒪_{E,S} --ℓ--> ⋯`, this follows from the case of `𝒪_E`
(`AlgebraicGeometry.ProEtale.subsingleton_H_padicIntegersSheaf_of_two_mul_lt`). -/
theorem subsingleton_H_padicSubfieldSheaf_of_two_mul_lt (q : ℕ) (hq : 2 * d < q) :
    letI := normedFieldOfAlgebra l E
    Subsingleton (Sheaf.H (continuousMapAbSheaf S E) q) := by
  let := normedFieldOfAlgebra l E
  have := LocallyOfFiniteType.isLocallyNoetherian a
  have := QuasiCompact.compactSpace_of_compactSpace a
  have : IsNoetherian S := {}
  have : IsFiltered (AsSmall.{u + 1} ℕ) := IsFiltered.of_equivalence AsSmall.equiv
  exact Scheme.ProEt.subsingleton_H_of_isColimit_of_isFiltered S
    ((isColimitPadicSubfieldSheafCocone S l E).whiskerEquivalence AsSmall.equiv.symm) q
    fun _ ↦ subsingleton_H_padicIntegersSheaf_of_two_mul_lt a d hS l E q hq

end AlgebraicGeometry.ProEtale
