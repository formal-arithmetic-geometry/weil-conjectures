/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Bertini
public import WeilConjectures.DeligneLaumon.Reduction.Weights

/-!
# Real Weil sheaves on an arbitrary base are mixed

A constructible Weil sheaf is `ι`-*real* (`AlgebraicGeometry.WeilSheaf.IsReal`) if the realization
under `ι` of every local Frobenius characteristic polynomial has real coefficients. Over a curve
this forces purity on a dense open, which is the content of the blueprint section
`sec-purity-real-sheaves`; this file states the extension of that statement to an arbitrary
separated finite-type `k₀`-scheme, which is the input the Deligne–Laumon reduction needs in order
to turn the reality of a local `L`-factor into a weight bound.

## Implementation notes

A Noetherian induction reduces to a lisse real sheaf on a smooth affine irreducible stratum, where
an irreducibility-preserving Bertini theorem produces a family of smooth geometrically irreducible
curve sections on which each constituent becomes pure of a weight independent of the curve;
mixedness then descends along finite constant extensions and is spliced back along the open–closed
sequence.

The geometric and group-theoretic inputs of the reduction are stated and proved separately:
`AlgebraicGeometry.Scheme.Hom.exists_isClosedImmersion_connectedSpace_pullback` (Bertini),
`Representation.exists_forall_isIrreducible_baseChange_of_congr` (finite matrix witnesses) and
`Representation.exists_filtration_isIrreducible_restrict` (geometric constituents), and curve
testing for geometric irreducibility below.

## Main statements

- `AlgebraicGeometry.WeilSheaf.exists_isClosedImmersion_isIrreducibleLocalSystem_upperStar`:
  blueprint `lem-zl-curve-testing-irreducibility`.
- `AlgebraicGeometry.WeilSheaf.IsReal.isMixed`: blueprint `sk-i-dl-general-real` and
  `thm-zl-real-mixed-by-curves`.

## TODO

Prove `AlgebraicGeometry.WeilSheaf.exists_isClosedImmersion_isIrreducibleLocalSystem_upperStar`
and `AlgebraicGeometry.WeilSheaf.IsReal.isMixed`, stated with `sorry`, along the reduction above,
once the category is redefined (`sk-d-real-weil`).

## References

- [Deligne, *La conjecture de Weil : II*][deligne1980], Publ. Math. IHÉS **52** (1980), §1.8, for
  real sheaves and their mixedness.
- [Kiehl, Weissauer, *Weil conjectures, perverse sheaves and l-adic Fourier
  transform*][kiehlWeissauer2001], Springer (2001), Appendix B, for the
  irreducibility-preserving Bertini theorem the proof uses.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open scoped ProEtale

/-- **Curve testing for geometric irreducibility**
(blueprint: `lem-zl-curve-testing-irreducibility`). Let `X₀` be a smooth geometrically connected
affine scheme of dimension `d ≥ 1` over a finite field `k₀`, with geometric fiber `X`, let
`𝒮₁, …, 𝒮ᵣ` be Weil sheaves on `X₀` whose geometric restrictions are irreducible local systems,
and let `S` be a nonempty finite set of `k̄`-points of `X`. There is a closed immersion
`i : C ⟶ X` of a smooth connected affine curve over `k̄` through `S`, defined over a finite
extension of `k₀` (stable under a power of the geometric Galois Frobenius of `X`), on which
every `𝒮ⱼ` remains geometrically irreducible. -/
theorem WeilSheaf.exists_isClosedImmersion_isIrreducibleLocalSystem_upperStar {k₀ : Type u}
    [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] {X₀ : Scheme.{u}}
    [X₀.Over (Spec (CommRingCat.of k₀))] [IsAffine X₀] {d : ℕ} (hd : 1 ≤ d)
    [SmoothOfRelativeDimension d (X₀ ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (X₀ ↘ Spec (CommRingCat.of k₀))] {r : ℕ}
    (𝒮 : Fin r → WeilSheaf k₀ l X₀)
    (h𝒮 : ∀ j, ProEtale.IsIrreducibleAdicLocalSystem (𝒮 j).obj.carrier)
    (S : Finset
      (Spec (.of (AlgebraicClosure k₀)) ⟶ (X₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber))
    (hS : S.Nonempty)
    (hS' : ∀ s ∈ S, s ≫ (X₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure = 𝟙 _) :
    ∃ (C : Scheme.{u}) (i : C ⟶ (X₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber),
      IsClosedImmersion i ∧ IsAffine C ∧
      SmoothOfRelativeDimension 1
        (i ≫ (X₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure) ∧
      ConnectedSpace C ∧ (∀ s ∈ S, ∃ c, c ≫ i = s) ∧
      (∀ j, ProEtale.IsIrreducibleAdicLocalSystem
        ((i)^*ᵃ[l].obj (𝒮 j).obj.carrier)) ∧
      ∃ m : ℕ, 0 < m ∧ ∃ φ : C ≅ C,
        φ.hom ≫ i = i ≫ ((X₀ ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).hom := by
  sorry

/-- Every constructible `ι`-real Weil sheaf on a separated finite-type `k₀`-scheme is `ι`-mixed
(blueprint: `sk-i-dl-general-real`, `thm-zl-real-mixed-by-curves`). -/
theorem WeilSheaf.IsReal.isMixed {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] {ι : PadicAlgCl l →+* ℂ} {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] {F : WeilSheaf k₀ l X} (hF : F.IsReal ι) :
    F.IsMixed ι :=
  sorry

end AlgebraicGeometry
