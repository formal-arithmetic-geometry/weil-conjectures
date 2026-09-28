/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Defs

/-!
# Mixed weight bounds for constructible Weil sheaves and complexes

This file sets up the language in which the Deligne–Laumon reduction to the affine line
(blueprint section `sec-deligne-laumon-general`) is stated. A constructible Weil sheaf is
`ι`-*mixed of weights at most* `w` if it admits a finite filtration whose successive quotients
are punctually `ι`-pure of some weight at most `w`, and a bounded constructible Weil complex `K`
is mixed of weights at most `w` if `𝓗ᵇK` is mixed of weights at most `w + b` for every `b`.

## Conventions

The `ℓ`-adic formalism these statements are phrased against is the provisional interface of
`WeilConjectures.WeilSheaf.Defs`: the abelian categories `AlgebraicGeometry.WeilSheaf k₀ l X` of
constructible Weil `ℚ̄_ℓ`-sheaves on a `k₀`-scheme `X`, their bounded derived categories
`AlgebraicGeometry.WeilComplex k₀ l X`, lissity, the geometric stalks with their local
Frobenius, the punctual weight conditions
`AlgebraicGeometry.WeilSheaf.IsPunctuallyPureOfWeight` and
`AlgebraicGeometry.WeilSheaf.HasWeightsAtMost`, the reality condition
`AlgebraicGeometry.WeilSheaf.IsReal`, and the direct images with compact support
`AlgebraicGeometry.WeilSheaf.higherLowerShriek` (`Rʳf₀!`) and
`AlgebraicGeometry.WeilComplex.derivedLowerShriek` (`Rf₀!`). The notions that other blueprint
blocks own are opaque placeholders there, each tagged `TODO(unify)` with the node that owns it;
what this block owns is the mixed upper bounds defined below.

Cohomological indexing is used throughout: `AlgebraicGeometry.WeilComplex.homologySheaf b` is
the `b`-th *cohomology* sheaf `𝓗ᵇK`, as in `DerivedCategory.homologyFunctor`, so the bound for
a complex of weights at most `w` is `w + b` in degree `b`, Deligne's convention.

## Main definitions

- `AlgebraicGeometry.WeilSheaf.IsMixedOfWeightsAtMost` and
  `AlgebraicGeometry.WeilComplex.IsMixedOfWeightsAtMost`: mixed of weights at most `w`, for a
  sheaf and for a complex.
- `AlgebraicGeometry.WeilSheaf.IsMixed`: mixed, that is, mixed of weights at most `w` for some
  `w`.
- `AlgebraicGeometry.HasDirectImageWeightBound`: the direct-image weight assertion for a single
  morphism, the statement the reductions of `sec-deligne-laumon-general` propagate.

Monotonicity in the bound is proved, and the closure properties the blueprint records alongside
the definition — under subobjects, quotients and extensions — are stated:
`AlgebraicGeometry.WeilSheaf.IsMixedOfWeightsAtMost.mono_weight`, `.of_mono`, `.of_epi` and
`.of_mono_cokernel`.

## References

- [Deligne, *La conjecture de Weil : II*][deligne1980], Publ. Math. IHÉS **52** (1980), §1, for
  mixed sheaves and their weight bounds.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-! ### Mixed sheaves -/

/-- `F` is `ι`-mixed of weights at most `w` if it admits a finite filtration

```
0 = G 0 ↪--- G 1 ↪--- ⋯ ↪--- G n ≅ F
         |        |            |
         v        v            v
      coker φ 0   ⋯      coker φ (n-1)
```

whose successive quotients `coker φᵢ` are punctually `ι`-pure of some weight at most `w`
(blueprint: `sk-d-dl-general-weights`). -/
def WeilSheaf.IsMixedOfWeightsAtMost (ι : PadicAlgCl l →+* ℂ) (F : WeilSheaf k₀ l X) (w : ℝ) :
    Prop :=
  ∃ (n : ℕ) (G : Fin (n + 1) → WeilSheaf k₀ l X)
    (φ : ∀ i : Fin n, G i.castSucc ⟶ G i.succ),
      IsZero (G 0) ∧ IsIsomorphic (G (Fin.last n)) F ∧ (∀ i : Fin n, Mono (φ i)) ∧
        ∀ i : Fin n, ∃ v ≤ w, (cokernel (φ i)).IsPunctuallyPureOfWeight ι v

/-- `F` is `ι`-*mixed* if it is mixed of weights at most `w` for some `w`, that is, if it admits
a finite filtration with punctually `ι`-pure quotients
(blueprint: `sk-d-dl-general-weights`). -/
def WeilSheaf.IsMixed (ι : PadicAlgCl l →+* ℂ) (F : WeilSheaf k₀ l X) : Prop :=
  ∃ w : ℝ, F.IsMixedOfWeightsAtMost ι w

namespace WeilSheaf

variable {ι : PadicAlgCl l →+* ℂ} {F G : WeilSheaf k₀ l X} {w w' : ℝ}

theorem IsMixedOfWeightsAtMost.isMixed (h : F.IsMixedOfWeightsAtMost ι w) : F.IsMixed ι :=
  ⟨w, h⟩

/-- Mixed upper bounds are monotone in the bound (blueprint: `sk-d-dl-general-weights`). -/
theorem IsMixedOfWeightsAtMost.mono_weight (h : F.IsMixedOfWeightsAtMost ι w) (hw : w ≤ w') :
    F.IsMixedOfWeightsAtMost ι w' := by
  obtain ⟨n, G, φ, h0, hlast, hmono, hpure⟩ := h
  refine ⟨n, G, φ, h0, hlast, hmono, fun i ↦ ?_⟩
  obtain ⟨v, hv, hvpure⟩ := hpure i
  exact ⟨v, hv.trans hw, hvpure⟩

/-- A subobject of a sheaf mixed of weights at most `w` is mixed of weights at most `w`: intersect
the filtration (blueprint: `sk-d-dl-general-weights`). -/
theorem IsMixedOfWeightsAtMost.of_mono (i : G ⟶ F) [Mono i] (h : F.IsMixedOfWeightsAtMost ι w) :
    G.IsMixedOfWeightsAtMost ι w :=
  sorry

/-- A quotient of a sheaf mixed of weights at most `w` is mixed of weights at most `w`: take the
images of the filtration (blueprint: `sk-d-dl-general-weights`). -/
theorem IsMixedOfWeightsAtMost.of_epi (p : F ⟶ G) [Epi p] (h : F.IsMixedOfWeightsAtMost ι w) :
    G.IsMixedOfWeightsAtMost ι w :=
  sorry

/-- An extension of a sheaf mixed of weights at most `w` by another one is mixed of weights at
most `w`: splice the two filtrations (blueprint: `sk-d-dl-general-weights`). -/
theorem IsMixedOfWeightsAtMost.of_mono_cokernel (i : G ⟶ F) [Mono i]
    (hG : G.IsMixedOfWeightsAtMost ι w) (hQ : (cokernel i).IsMixedOfWeightsAtMost ι w) :
    F.IsMixedOfWeightsAtMost ι w :=
  sorry

end WeilSheaf

/-! ### Mixed complexes -/

/-- A bounded constructible Weil complex `K` is `ι`-*mixed of weights at most* `w` if its `b`-th
cohomology sheaf `𝓗ᵇK` is mixed of weights at most `w + b`, for every `b`; equivalently, the
bound in total degree `n` is `w + n` (blueprint: `sk-d-dl-general-weights`). -/
def WeilComplex.IsMixedOfWeightsAtMost (ι : PadicAlgCl l →+* ℂ) (K : WeilComplex k₀ l X)
    (w : ℝ) : Prop :=
  ∀ b : ℤ, ((WeilComplex.homologySheaf b).obj K).IsMixedOfWeightsAtMost ι (w + (b : ℝ))

/-- The direct-image weight assertion of the blueprint theorem `sk-thm-dl-general-sheaf`, for a
single morphism `f : X ⟶ Y` of `k₀`-schemes: every constructible Weil sheaf `F` on `X` that is
mixed of weights at most `w` has `Rʳf₀!F` mixed of weights at most `w + r`, for every `r`. The
reductions of the blueprint section `sec-deligne-laumon-general` propagate this assertion along
compositions and open–closed decompositions. -/
def HasDirectImageWeightBound (k₀ : Type u) [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] (ι : PadicAlgCl l →+* ℂ) {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] : Prop :=
  ∀ (w : ℝ) (F : WeilSheaf k₀ l X), F.IsMixedOfWeightsAtMost ι w →
    ∀ r : ℕ, ((WeilSheaf.higherLowerShriek k₀ l f r).obj F).IsMixedOfWeightsAtMost ι (w + r)

end AlgebraicGeometry
