/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.WeilSheaf.StalkIso

/-!
# The relative trace formula for the direct image with compact support

The sheaf–function dictionary for `Rf_!`: for a separated morphism `f : X ⟶ Y` of finite type
of `k₀`-schemes, a Weil complex `K` on `X`, `n ≥ 1` and an `𝔽_{qⁿ}`-rational point `y` of `Y`,

`t_{Rf_!K}(y) = ∑_{x ∈ X(𝔽_{qⁿ}), f(x) = y} t_K(x)`,

the Grothendieck–Lefschetz trace formula applied to the fibre of `f` over `y`, identified with
the stalk of `Rf_!K` at `ȳ` by proper base change. It is stated here as
`AlgebraicGeometry.WeilComplex.traceFunction_derivedLowerShriek`.

The file also records that trace functions only depend on the isomorphism class of a Weil sheaf
and that the trace function of a Weil sheaf placed in degree zero is that of the sheaf.

## Main statements

- `AlgebraicGeometry.WeilSheaf.traceFunction_congr`: isomorphic Weil sheaves have the same trace
  function.
- `AlgebraicGeometry.WeilComplex.traceFunction_toComplex`: the trace function of a Weil sheaf
  viewed as a complex in degree zero.
- `AlgebraicGeometry.WeilComplex.traceFunction_derivedLowerShriek`: the relative trace formula
  for `Rf_!`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]

/-- Isomorphic Weil sheaves have the same trace function: an isomorphism induces isomorphisms of
Frobenius modules between the stalks (`AlgebraicGeometry.WeilSheaf.nonempty_equiv_stalkAt_of_iso`),
which preserve the characteristic polynomial, hence the trace, of the Frobenius. -/
theorem WeilSheaf.traceFunction_congr {F G : WeilSheaf k₀ l X} (e : F ≅ G) (n : ℕ)
    (x : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    F.traceFunction n x = G.traceFunction n x := by
  simp only [traceFunction]
  rw [LinearMap.trace_eq_neg_charpoly_nextCoeff, LinearMap.trace_eq_neg_charpoly_nextCoeff,
    (nonempty_equiv_stalkAt_of_iso _ _ _ e).some.charpoly_frobeniusEnd]

/-- The trace function of a Weil sheaf placed in degree zero is the trace function of the
sheaf: its only nonzero cohomology sheaf is `𝓗⁰ = F`. -/
theorem WeilComplex.traceFunction_toComplex (F : WeilSheaf k₀ l X) (n : ℕ)
    (x : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    (WeilSheaf.toComplex.obj F).traceFunction n x = F.traceFunction n x := by
  rw [WeilSheaf.toComplex_obj, traceFunction_eq_sum _ {0}
    (fun j hj ↦ isZero_homologySheaf_singleComplex (Finset.notMem_singleton.1 hj) F),
    Finset.sum_singleton, Int.negOnePow_zero, Units.val_one, one_smul]
  exact WeilSheaf.traceFunction_congr (WeilSheaf.toComplexCompHomologySheafIso.app F) n x

/-- **The relative trace formula for `Rf_!`** (sheaf–function dictionary): for a separated
morphism `f : X ⟶ Y` of finite type of `k₀`-schemes, a Weil complex `K` on `X`, `n ≥ 1` and an
`𝔽_{qⁿ}`-rational point `y` of `Y`, the trace function of `Rf_!K` at `y` is the sum of the trace
function of `K` over the `𝔽_{qⁿ}`-rational points `x` of `X` over `y`,

`t_{Rf_!K}(y) = ∑_{x ∈ X(𝔽_{qⁿ}), f(x) = y} t_K(x)`

(the sum is finite, the fibre being of finite type over `𝔽_{qⁿ}`). It is the
Grothendieck–Lefschetz trace formula over `𝔽_{qⁿ}`
(blueprint: `thm-trf-grothendieck-lefschetz-qbar`, subsection `sk-thm-trace-transport`) applied
to the fibre `X_y` of `f` over `y`, whose compactly supported cohomology with its Frobenius is
the stalk of `Rf_!K` at `ȳ` with the Frobenius relative to `𝔽_{qⁿ}`, the points and local
Frobenius of the fibre being those of `X` over `y`
(blueprint: `lem-trf-weil-shriek-operator-fibres`, subsection `sk-d-weil-push`). -/
theorem WeilComplex.traceFunction_derivedLowerShriek (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))] (K : WeilComplex k₀ l X) {n : ℕ}
    (hn : 1 ≤ n)
    (y : (Y ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    ((derivedLowerShriek k₀ l f).obj K).traceFunction n y =
      ∑ᶠ x : {x : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n) //
        x.1 ≫ f = y.1}, K.traceFunction n x.1 :=
  sorry

end AlgebraicGeometry
