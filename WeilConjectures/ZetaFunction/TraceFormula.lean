/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Finiteness
public import WeilConjectures.WeilSheaf.StalkCharpoly
public import WeilConjectures.WeilSheaf.StalkPairing
public import WeilConjectures.ZetaSeries

/-!
# The Grothendieck–Lefschetz trace formula and point counts

Let `X₀` be a separated scheme of finite type over the finite field `k₀ = 𝔽_q` and let `K` be a
Weil complex on `X₀`. The Grothendieck–Lefschetz trace formula says that for every `m ≥ 1`

`∑ᵢ (-1)ⁱ Tr(Fᵐ | H_c^i(X₀ ⊗ k̄, K)) = ∑_{y ∈ X₀(𝔽_{qᵐ})} t_K(y)`,

where `t_K` is the trace function of `K` (`AlgebraicGeometry.WeilComplex.traceFunction`). For
the constant Weil sheaf `ℚ̄_ℓ` every local trace is `1`, and the right hand side is the number
`N_m = #X₀(𝔽_{qᵐ})` of `𝔽_{qᵐ}`-rational points. If `X₀` is proper, compactly supported
cohomology is ordinary cohomology.

The trace formula over `ℚ̄_ℓ` itself is the blueprint node `thm-trf-grothendieck-lefschetz-qbar`
of the trace formula chapter (subsection `sk-thm-trace-transport`); it is stated here for the
Weil complexes of this repository, whose compactly supported cohomology is
`AlgebraicGeometry.WeilComplex.compactlySupportedCohomology`, and is proved in that chapter.

## Main statements

- `AlgebraicGeometry.WeilComplex.finsum_trace_compactlySupportedCohomology_eq`: the trace
  formula over `ℚ̄_ℓ` (`thm-trf-grothendieck-lefschetz-qbar`).
- `AlgebraicGeometry.WeilSheaf.traceFunction_adicConstant`: the trace function of the constant
  Weil sheaf is `1`.
- `AlgebraicGeometry.WeilSheaf.pointCount_eq_finsum_trace_compactlySupportedCohomology` and
  `AlgebraicGeometry.WeilSheaf.pointCount_eq_finsum_trace_cohomology`: the point-counting
  trace formula (`cor-trf-point-counting`).
- `AlgebraicGeometry.WeilComplex.sum_traceFunction_eq_finsum_trace` and
  `AlgebraicGeometry.WeilSheaf.pointCount_eq_sum_trace_cohomology`: the Grothendieck–Lefschetz
  trace formula and its every-iterate form for a smooth proper variety
  (`thm-weil-grothendieck-lefschetz-trace`, `prop-every-iterate-trace`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

section Separated

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- Blueprint `thm-trf-grothendieck-lefschetz-qbar` (Grothendieck–Lefschetz formula over `ℚ̄_ℓ`,
subsection `sk-thm-trace-transport` of the trace formula chapter): for a Weil complex `K` on a
separated `k₀`-scheme `X₀` of finite type and every `m ≥ 1`,

`∑ᵢ (-1)ⁱ Tr(F^m | H_c^i(X₀ ⊗ k̄, K)) = ∑_{y ∈ X₀(𝔽_{qᵐ})} ∑ⱼ (-1)ʲ Tr(F_{y,m} | 𝓗ʲ(K)_ȳ)`.

The inner sum on the right is the trace function `t_K(y)` of `K`; both sums are finite
(`AlgebraicGeometry.WeilComplex.exists_subsingleton_compactlySupportedCohomology`,
`AlgebraicGeometry.Scheme.Hom.finite_fieldPoints`). -/
theorem WeilComplex.finsum_trace_compactlySupportedCohomology_eq (K : WeilComplex k₀ l X)
    {m : ℕ} (hm : 1 ≤ m) :
    ∑ᶠ i : ℤ, (i.negOnePow : ℤ) • LinearMap.trace (PadicAlgCl l) _
        ((K.compactlySupportedCohomology i).frobeniusEnd ^ m) =
      ∑ᶠ y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ m),
        K.traceFunction m y :=
  sorry

end Separated

section Constant

variable (k₀ l) (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- The trace function of the constant Weil sheaf `ℚ̄_ℓ` is `1`: its stalks are one-dimensional
and every local Frobenius is the identity
(`AlgebraicGeometry.WeilSheaf.adicConstant_stalkAt_frobenius`). -/
theorem WeilSheaf.traceFunction_adicConstant (n : ℕ)
    (y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    (WeilSheaf.adicConstant k₀ l X).traceFunction n y = 1 :=
  sorry

variable {k₀ l X} in
/-- The trace function of a Weil sheaf, viewed as a Weil complex concentrated in degree zero, is
its trace function as a sheaf. -/
theorem WeilComplex.traceFunction_toComplex (F : WeilSheaf k₀ l X) (n : ℕ)
    (y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    (WeilSheaf.toComplex.obj F).traceFunction n y = F.traceFunction n y :=
  sorry

variable [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- Blueprint `cor-trf-point-counting` (point-counting trace formula, subsection
`sk-thm-trace-transport` of the trace formula chapter), compactly supported form: for a
separated `k₀`-scheme `X₀` of finite type and every `m ≥ 1`,

`#X₀(𝔽_{qᵐ}) = ∑ᵢ (-1)ⁱ Tr(Fᵐ | H_c^i(X₀ ⊗ k̄, ℚ̄_ℓ))`.

It is the trace formula
`AlgebraicGeometry.WeilComplex.finsum_trace_compactlySupportedCohomology_eq` for the constant
Weil sheaf, whose trace function is `1`. -/
theorem WeilSheaf.pointCount_eq_finsum_trace_compactlySupportedCohomology {m : ℕ}
    (hm : 1 ≤ m) :
    ((X ↘ Spec (CommRingCat.of k₀)).pointCount m : PadicAlgCl l) =
      ∑ᶠ i : ℤ, (i.negOnePow : ℤ) • LinearMap.trace (PadicAlgCl l) _
        (((WeilSheaf.adicConstant k₀ l X).compactlySupportedCohomology i).frobeniusEnd ^ m) :=
  sorry

end Constant

section Proper

variable (k₀ l) (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
  [IsProper (X ↘ Spec (CommRingCat.of k₀))]

/-- Blueprint `cor-trf-point-counting` (point-counting trace formula), proper form: for a proper
`k₀`-scheme `X₀` and every `m ≥ 1`,

`#X₀(𝔽_{qᵐ}) = ∑ᵢ (-1)ⁱ Tr(Fᵐ | Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ))`,

compactly supported cohomology being ordinary cohomology
(`AlgebraicGeometry.WeilComplex.nonempty_equiv_compactlySupportedCohomology_cohomology`). -/
theorem WeilSheaf.pointCount_eq_finsum_trace_cohomology {m : ℕ} (hm : 1 ≤ m) :
    ((X ↘ Spec (CommRingCat.of k₀)).pointCount m : PadicAlgCl l) =
      ∑ᶠ i : ℤ, (i.negOnePow : ℤ) • LinearMap.trace (PadicAlgCl l) _
        (((WeilSheaf.adicConstant k₀ l X).cohomology i).frobeniusEnd ^ m) :=
  sorry

/-- Blueprint `thm-weil-grothendieck-lefschetz-trace` (Grothendieck–Lefschetz trace formula):
for a Weil complex `K` on a separated `k₀`-scheme `Y₀` of finite type and `m ≥ 1`, the sum over
`y ∈ Y₀(𝔽_{qᵐ})` of the local alternating traces `t_K(y)` is the alternating trace of `Fᵐ` on
`H_c^•(Y₀ ⊗ k̄, K)`; for `K = ℚ̄_ℓ` and a proper `X₀` this specializes to
`#X₀(𝔽_{qᵐ}) = ∑ᵢ (-1)ⁱ Tr(Fᵐ | Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ))`. -/
theorem WeilComplex.finsum_traceFunction_eq_and_pointCount_eq {Y : Scheme.{u}}
    [Y.Over (Spec (CommRingCat.of k₀))] [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] (K : WeilComplex k₀ l Y) {m : ℕ}
    (hm : 1 ≤ m) :
    ∑ᶠ y : (Y ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ m),
        K.traceFunction m y =
      ∑ᶠ i : ℤ, (i.negOnePow : ℤ) • LinearMap.trace (PadicAlgCl l) _
        ((K.compactlySupportedCohomology i).frobeniusEnd ^ m) ∧
    ((X ↘ Spec (CommRingCat.of k₀)).pointCount m : PadicAlgCl l) =
      ∑ᶠ i : ℤ, (i.negOnePow : ℤ) • LinearMap.trace (PadicAlgCl l) _
        (((WeilSheaf.adicConstant k₀ l X).cohomology i).frobeniusEnd ^ m) :=
  ⟨(K.finsum_trace_compactlySupportedCohomology_eq hm).symm,
    WeilSheaf.pointCount_eq_finsum_trace_cohomology k₀ l X hm⟩

/-- Blueprint `prop-every-iterate-trace` (every-iterate Grothendieck–Lefschetz identity), smooth
proper case: for `X₀` smooth and proper of pure dimension `d` and every `n ≥ 1`,

`N_n(X₀) = ∑_{i = 0}^{2d} (-1)ⁱ Tr(Fⁿ | Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ))`,

the cohomology vanishing outside `[0, 2d]`
(`AlgebraicGeometry.WeilSheaf.subsingleton_cohomology_adicConstant`). The general identity for
a Weil complex on a separated scheme of finite type is
`AlgebraicGeometry.WeilComplex.finsum_traceFunction_eq_and_pointCount_eq`. -/
theorem WeilSheaf.pointCount_eq_sum_trace_cohomology (d : ℕ)
    [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))] {n : ℕ} (hn : 1 ≤ n) :
    ((X ↘ Spec (CommRingCat.of k₀)).pointCount n : PadicAlgCl l) =
      ∑ i ∈ Finset.range (2 * d + 1), (-1) ^ i * LinearMap.trace (PadicAlgCl l) _
        (((WeilSheaf.adicConstant k₀ l X).cohomology i).frobeniusEnd ^ n) :=
  sorry

end Proper

end AlgebraicGeometry
