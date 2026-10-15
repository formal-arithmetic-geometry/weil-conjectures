/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Cohomology

/-!
# Composition and base change for the compact-support direct image of Weil complexes

Two of the compatibilities of blueprint `prop-weil-operations` ("composition, base change,
projection, purity and duality isomorphisms are morphisms of Weil complexes"), for the direct
image with compact support `Rf₀!` of Weil complexes
(`AlgebraicGeometry.WeilComplex.derivedLowerShriek`), and the Grothendieck–Lefschetz trace
formula for Weil complexes (blueprint `thm-trf-grothendieck-lefschetz-qbar`). They belong to
other blueprint sections and are recorded here, without proof, as inputs of the Fourier trace
formula.

## Main statements

- `AlgebraicGeometry.WeilComplex.nonempty_iso_derivedLowerShriek_comp`: `R(gf)₀! ≅ Rg₀! Rf₀!`.
- `AlgebraicGeometry.WeilComplex.nonempty_iso_derivedLowerShriek_upperStar`: compact-support
  base change `g^* Rf₀! ≅ Rf'₀! g'^*` along a cartesian square.
- `AlgebraicGeometry.WeilComplex.sum_trace_compactlySupportedCohomology_eq_sum_traceFunction`:
  the Grothendieck–Lefschetz trace formula.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- Blueprint `prop-weil-operations`: Six operations on Weil complexes (the composition
isomorphism). For separated quasi-compact morphisms `f : X ⟶ Y`, `g : Y ⟶ Z` locally of finite
type of `k₀`-schemes of finite type, `R(g ∘ f)₀! ≅ Rg₀! ∘ Rf₀!` as functors of Weil
complexes. -/
theorem nonempty_iso_derivedLowerShriek_comp {X Y Z : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    [Z.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Y) (g : Y ⟶ Z)
    [f.IsOver (Spec (CommRingCat.of k₀))] [g.IsOver (Spec (CommRingCat.of k₀))]
    [(f ≫ g).IsOver (Spec (CommRingCat.of k₀))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Z ↘ Spec (CommRingCat.of k₀))] :
    Nonempty (derivedLowerShriek k₀ l (f ≫ g) ≅
      derivedLowerShriek k₀ l f ⋙ derivedLowerShriek k₀ l g) :=
  sorry

/-- Blueprint `prop-weil-operations`: Six operations on Weil complexes (the base change
isomorphism; blueprint `thm-cbc-qbar` for the underlying complexes). For a cartesian square of
`k₀`-schemes

```
  X' ──g'──▶ X
  │f'        │f
  ▼          ▼
  Y' ──g───▶ Y
```

with `f` and `f'` separated quasi-compact locally of finite type, compact-support base change
`g^* Rf₀! ≅ Rf'₀! g'^*` holds as an isomorphism of functors of Weil complexes. -/
theorem nonempty_iso_derivedLowerShriek_upperStar {X Y X' Y' : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    [X'.Over (Spec (CommRingCat.of k₀))] [Y'.Over (Spec (CommRingCat.of k₀))]
    (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X) (h : IsPullback g' f' f g)
    [f.IsOver (Spec (CommRingCat.of k₀))] [g.IsOver (Spec (CommRingCat.of k₀))]
    [f'.IsOver (Spec (CommRingCat.of k₀))] [g'.IsOver (Spec (CommRingCat.of k₀))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f']
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y' ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y' ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y' ↘ Spec (CommRingCat.of k₀))] :
    Nonempty (derivedLowerShriek k₀ l f ⋙ upperStar g ≅
      upperStar g' ⋙ derivedLowerShriek k₀ l f') :=
  sorry

/-- Blueprint `thm-trf-grothendieck-lefschetz-qbar`: the Grothendieck–Lefschetz formula over
`ℚ̄_ℓ`. For a separated `k₀`-scheme `X₀` of finite type, a Weil complex `K` on `X₀` and
`m ≥ 1`,

`∑ᵢ (-1)ⁱ Tr(Fᵐ | H_cⁱ(X, K)) = ∑_{y ∈ X₀(𝔽_{qᵐ})} t_K(y)`,

`F` being the geometric Frobenius on compactly supported cohomology
(`AlgebraicGeometry.WeilComplex.compactlySupportedCohomology`) and `t_K` the trace function
(`AlgebraicGeometry.WeilComplex.traceFunction`). Only finitely many terms are nonzero on
either side. -/
theorem sum_trace_compactlySupportedCohomology_eq_sum_traceFunction {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    (K : WeilComplex k₀ l X) {m : ℕ} (hm : m ≠ 0) :
    ∑ᶠ i : ℤ, (i.negOnePow : ℤ) • LinearMap.trace (PadicAlgCl l) _
        ((K.compactlySupportedCohomology i).frobenius.toLinearMap ^ m) =
      ∑ᶠ y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ m),
        K.traceFunction m y :=
  sorry

end AlgebraicGeometry.WeilComplex
