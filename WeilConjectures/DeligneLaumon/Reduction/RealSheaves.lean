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

A constructible Weil sheaf is `ι`-*real* (`AlgebraicGeometry.LAdicWeilSheaf.IsReal`) if the
realization under `ι` of every local Frobenius characteristic polynomial has real coefficients. Over
a curve this forces purity on a dense open, which is the content of the blueprint section
`sec-purity-real-sheaves`; this file states the extension of that statement to an arbitrary
separated finite-type `k₀`-scheme, which is the input the Deligne–Laumon reduction needs in order
to turn the reality of a local `L`-factor into a weight bound.

## Implementation notes

A Noetherian induction reduces to a lisse real sheaf on a smooth affine irreducible stratum, where
an irreducibility-preserving Bertini theorem produces a family of smooth geometrically irreducible
curve sections on which each constituent becomes pure of a weight independent of the curve;
mixedness then descends along finite constant extensions and is spliced back along the open–closed
sequence.

With the present scaffold every Weil sheaf is zero (`AlgebraicGeometry.LAdicWeilSheaf.isZero`), and
`AlgebraicGeometry.LAdicWeilSheaf.IsReal.isMixed` is proved by the filtration of length zero. The
geometric and group-theoretic inputs of the reduction are stated and proved separately:
`AlgebraicGeometry.Scheme.Hom.exists_isClosedImmersion_connectedSpace_pullback` (Bertini),
`Representation.exists_forall_isIrreducible_baseChange_of_congr` (finite matrix witnesses) and
`Representation.exists_filtration_isIrreducible_restrict` (geometric constituents), and curve
testing for geometric irreducibility below.

## Main statements

- `AlgebraicGeometry.LAdicWeilSheaf.exists_isClosedImmersion_isIrreducibleLocalSystem_upperStar`:
  blueprint `lem-zl-curve-testing-irreducibility`.
- `AlgebraicGeometry.LAdicWeilSheaf.IsReal.isMixed`: blueprint `sk-i-dl-general-real` and
  `thm-zl-real-mixed-by-curves`.

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

/-- **Curve testing for geometric irreducibility**
(blueprint: `lem-zl-curve-testing-irreducibility`). Let `X₀` be a smooth geometrically connected
affine scheme of dimension `d ≥ 1` over a finite field `k₀`, with geometric fiber `X`, let
`𝒮₁, …, 𝒮ᵣ` be Weil sheaves on `X₀` whose geometric restrictions are irreducible local systems,
and let `S` be a nonempty finite set of `k̄`-points of `X`. There is a closed immersion
`i : C ⟶ X` of a smooth connected affine curve over `k̄` through `S`, defined over a finite
extension of `k₀` (stable under a power of the geometric Galois Frobenius of `X`), on which
every `𝒮ⱼ` remains geometrically irreducible.

With the present scaffold every Weil sheaf is zero, so the restrictions of the `𝒮ⱼ` are never
irreducible and only `r = 0` is not vacuous; the curve is then provided by
`AlgebraicGeometry.Scheme.Hom.exists_isClosedImmersion_connectedSpace_pullback` for `d ≥ 2`,
and is `X` itself for `d = 1`. -/
theorem LAdicWeilSheaf.exists_isClosedImmersion_isIrreducibleLocalSystem_upperStar {k₀ : Type u}
    [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] {X₀ : Scheme.{u}}
    [X₀.Over (Spec (CommRingCat.of k₀))] [IsAffine X₀] {d : ℕ} (hd : 1 ≤ d)
    [SmoothOfRelativeDimension d (X₀ ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (X₀ ↘ Spec (CommRingCat.of k₀))] {r : ℕ}
    (𝒮 : Fin r → LAdicWeilSheaf k₀ l X₀)
    (h𝒮 : ∀ j, Scheme.IsIrreducibleLocalSystem (𝒮 j).obj.carrier)
    (S : Finset
      (Spec (.of (AlgebraicClosure k₀)) ⟶ (X₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber))
    (hS : S.Nonempty)
    (hS' : ∀ s ∈ S, s ≫ (X₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure = 𝟙 _) :
    ∃ (C : Scheme.{u}) (i : C ⟶ (X₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber),
      IsClosedImmersion i ∧ IsAffine C ∧
      SmoothOfRelativeDimension 1
        (i ≫ (X₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure) ∧
      ConnectedSpace C ∧ (∀ s ∈ S, ∃ c, c ≫ i = s) ∧
      (∀ j, Scheme.IsIrreducibleLocalSystem
        ((Etale.upperStar (WeilCoefficients.{u} l) i).obj (𝒮 j).obj.carrier)) ∧
      ∃ m : ℕ, 0 < m ∧ ∃ φ : C ≅ C,
        φ.hom ≫ i = i ≫ ((X₀ ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).hom := by
  -- the geometric restrictions are zero, so no `𝒮ⱼ` is irreducible
  obtain rfl | hr := Nat.eq_zero_or_pos r
  swap
  · exact absurd (𝒮 ⟨0, hr⟩).isZero_carrier (h𝒮 ⟨0, hr⟩).2.1
  have : ConnectedSpace (X₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
    pullback_of_geometrically GeometricallyConnected.geometrically_connectedSpace _ _
  have : IsAffine (X₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
    isAffine_of_isAffineHom (X₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberProj
  obtain rfl | hd := hd.eq_or_lt
  · refine ⟨_, 𝟙 _, inferInstance, inferInstance, ?_, inferInstance,
      fun s _ ↦ ⟨s, Category.comp_id s⟩, fun j ↦ j.elim0, 1, one_pos,
      (X₀ ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius, by
        rw [pow_one, Category.comp_id, Category.id_comp]⟩
    rw [Category.id_comp]
    exact (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback _ _) ‹_›
  · obtain ⟨C, i, hi, hC, hsm, hconn, hCS, -, m, hm, φ, hφ⟩ :=
      (X₀ ↘ Spec (CommRingCat.of k₀)).exists_isClosedImmersion_connectedSpace_pullback hd (𝟙 _)
        S hS hS'
    exact ⟨C, i, hi, hC, hsm, hconn, hCS, fun j ↦ j.elim0, m, hm, φ, hφ⟩

-- with the present scaffold every Weil sheaf is zero, and the proof needs no hypothesis
set_option linter.unusedVariables false in
/-- Every constructible `ι`-real Weil sheaf on a separated finite-type `k₀`-scheme is `ι`-mixed
(blueprint: `sk-i-dl-general-real`, `thm-zl-real-mixed-by-curves`).

With the present scaffold every Weil sheaf is zero (`AlgebraicGeometry.LAdicWeilSheaf.isZero`), and
the filtration of length zero exhibits `F` as mixed; the reduction of the blueprint to lisse
sheaves on curves through `Representation.exists_filtration_isIrreducible_restrict` and
`AlgebraicGeometry.LAdicWeilSheaf.exists_isClosedImmersion_isIrreducibleLocalSystem_upperStar` is
not needed. -/
theorem LAdicWeilSheaf.IsReal.isMixed {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] {ι : PadicAlgCl l →+* ℂ} {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] {F : LAdicWeilSheaf k₀ l X} (hF : F.IsReal ι) :
    F.IsMixed ι :=
  (LAdicWeilSheaf.isMixedOfWeightsAtMost_of_isZero F.isZero 0).isMixed

end AlgebraicGeometry
