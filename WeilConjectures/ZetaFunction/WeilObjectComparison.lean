/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Statement
public import WeilConjectures.WeilSheaf.AlgClosedCoefficientCohomology
public import WeilConjectures.WeilSheaf.Stalk

/-!
# Weil complexes as Weil objects of `Dᵇc(-)⟦ℚ̲̄_ℓ⟧`

The zeta-function chapter works with the Weil complexes `AlgebraicGeometry.WeilComplex` on a
scheme `X₀` over a finite field `k₀`, with their compactly supported cohomology modules and
trace functions. The trace formula of the project is stated in
`WeilConjectures.TraceFormula.Statement` for the Weil objects
`ProEtale.CondensedRing.WeilBoundedConstructible` of `Dᵇc(X₀)⟦ℚ̲̄_ℓ⟧` for the identity of `X₀`
(the Frobenius of `Spec k̄` twisted by `e = 𝟙`).

This file states the comparison between the two settings
(`AlgebraicGeometry.WeilComplex.exists_weilBoundedConstructible_comparison`) and deduces the trace
formula for Weil complexes from `ProEtale.CondensedRing.weilTraceFormula`
(`AlgebraicGeometry.WeilComplex.finsum_trace_compactlySupportedCohomology_eq_of_comparison`).

## Sorried input

- `AlgebraicGeometry.WeilComplex.exists_weilBoundedConstructible_comparison`: every Weil complex
  `K` on `X₀` comes from a Weil object `K'` for `𝟙 X₀`, compatibly with the traces. There is an
  additive map `ι : End (𝟙 Mod_{Spec k̄}) ⟶ ℚ̄_ℓ` identifying
  * the global trace of `K'` in degree `n + 1` with the alternating sum of the traces of `F^{n+1}`
    on the compactly supported cohomology of `K`, and
  * the local trace of `K'` at a point of degree `n + 1` with the trace function of `K` at the
    corresponding `𝔽_{q^{n+1}}`-rational point, through a bijection between the two sets of
    points.
  It is the comparison of the Weil complexes of the zeta-function chapter with the bounded
  constructible Weil objects of the trace formula chapter.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- The ring characteristic of a finite field is prime. -/
lemma fact_ringChar_prime_of_finite : Fact (ringChar k₀).Prime :=
  ⟨CharP.char_is_prime_of_pos k₀ (ringChar k₀)⟩

attribute [local instance] fact_ringChar_prime_of_finite

/-- The scheme `X₀` over `Spec k₀` as an object of `Over (Spec k₀)`. -/
noncomputable abbrev WeilComplex.overSpec (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))] :
    Over (Spec (.of k₀)) :=
  Over.mk (X ↘ Spec (CommRingCat.of k₀))

instance : LocallyOfFiniteType (WeilComplex.overSpec (k₀ := k₀) X).hom :=
  inferInstanceAs (LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀)))

instance : QuasiCompact (WeilComplex.overSpec (k₀ := k₀) X).hom :=
  inferInstanceAs (QuasiCompact (X ↘ Spec (CommRingCat.of k₀)))

instance : IsSeparated (WeilComplex.overSpec (k₀ := k₀) X).hom :=
  inferInstanceAs (IsSeparated (X ↘ Spec (CommRingCat.of k₀)))

open ProEtale.CondensedRing in
/-- **Weil complexes are Weil objects of `Dᵇc(-)⟦ℚ̲̄_ℓ⟧`** (comparison of the zeta-function chapter
with the trace formula chapter, sorried): a Weil complex `K` on `X₀` comes from a Weil object `K'`
for `𝟙 X₀` with the same traces. There is an additive map `ι : End (𝟙 Mod_{Spec k̄}) ⟶ ℚ̄_ℓ` such
that, for every `n`,
* `ι` of the global trace of `K'` in degree `n + 1` is
  `∑ᵢ (-1)ⁱ Tr(F^{n+1} | H_c^i(X₀ ⊗ k̄, K))`, and
* there is a bijection between the points of `X₀` of degree `n + 1` for `e = 𝟙` and the
  `𝔽_{q^{n+1}}`-rational points of `X₀`, along which `ι` of the local trace of `K'` is the trace
  function `t_K` of `K` in degree `n + 1`. -/
theorem WeilComplex.exists_weilBoundedConstructible_comparison (K : WeilComplex k₀ l X) :
    ∃ (K' : WeilBoundedConstructible l (Iso.refl (WeilComplex.overSpec (k₀ := k₀) X)).hom)
      (ι : End (𝟙_ (GeometricPointMod l (AlgebraicClosure k₀))) →+ PadicAlgCl l),
      (∀ n : ℕ, ι (weilGlobalSupertrace l (Iso.refl _) K' n) =
        ∑ᶠ i : ℤ, (i.negOnePow : ℤ) • LinearMap.trace (PadicAlgCl l) _
          ((K.compactlySupportedCohomology i).frobeniusEnd ^ (n + 1))) ∧
      ∀ n : ℕ, ∃ eqv : frobeniusFixedPoints (Iso.refl (WeilComplex.overSpec (k₀ := k₀) X)) n ≃
          (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ (n + 1)),
        ∀ x, ι (weilStalkSupertrace l n x.1 x.2.2 K') = K.traceFunction (n + 1) (eqv x) :=
  sorry

open ProEtale.CondensedRing in
/-- **The Grothendieck–Lefschetz trace formula for Weil complexes**, deduced from the trace formula
for Weil objects `ProEtale.CondensedRing.weilTraceFormula` (with `e = 𝟙`) through the comparison
`WeilComplex.exists_weilBoundedConstructible_comparison`. -/
theorem WeilComplex.finsum_trace_compactlySupportedCohomology_eq_of_comparison
    (K : WeilComplex k₀ l X) {m : ℕ} (hm : 1 ≤ m) :
    ∑ᶠ i : ℤ, (i.negOnePow : ℤ) • LinearMap.trace (PadicAlgCl l) _
        ((K.compactlySupportedCohomology i).frobeniusEnd ^ m) =
      ∑ᶠ y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ m),
        K.traceFunction m y := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  obtain ⟨K', ι, hglob, hloc⟩ := K.exists_weilBoundedConstructible_comparison
  obtain ⟨eqv, heqv⟩ := hloc n
  haveI := finite_frobeniusFixedPoints_of_powSucc_eq_refl
    (Iso.refl (WeilComplex.overSpec (k₀ := k₀) X)) ⟨0, rfl⟩ n
  rw [← hglob n, weilTraceFormula l _ ⟨0, rfl⟩ K' n,
    map_finsum ι (Set.toFinite _)]
  exact (finsum_congr heqv).trans (finsum_comp_equiv eqv)

end AlgebraicGeometry
