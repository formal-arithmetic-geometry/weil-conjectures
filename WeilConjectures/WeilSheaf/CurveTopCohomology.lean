/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.WeilSheaf.Cohomology
public import WeilConjectures.WeilSheaf.Dual
public import WeilConjectures.WeilSheaf.GeometricCoinvariants

/-!
# Top compactly supported cohomology of a lisse Weil sheaf on an affine curve

On a smooth geometrically connected affine curve `U₀` over a finite field `k₀ = 𝔽_q`, the top
compactly supported cohomology `H_c²(U, F)` of a lisse Weil sheaf `F` is the geometric
coinvariants `V_{π₁(U)}` of its generic fibre `V`, Tate-twisted by `(-1)`: by global Verdier
duality on the smooth curve `U`, `H_c²(U, F)` is dual to `H⁰(U, F^∨(1))`, and the global sections
of the lisse sheaf `F^∨` are the invariants of `π₁(U)` on `V^∨`.

The geometric coinvariants are `AlgebraicGeometry.WeilSheaf.geometricCoinvariants`, the dual
`Γ(U, F^∨)^∨` of the global sections of the dual sheaf.

## Main statements

- `AlgebraicGeometry.WeilSheaf.nonempty_equiv_compactlySupportedCohomology_two`
  (`lem-a1-affine-hc2`), stated with `sorry`: Verdier duality for Weil complexes is not
  available yet.
- `AlgebraicGeometry.isPureOfWeightOver_compactlySupportedCohomology_two_of_isAffine`
  (`lem-zl-affine-curve-hc2-purity`, from `sec-deligne-laumon-general`), stated with `sorry`:
  purity of `H_c²` on a smooth affine curve which need not be geometrically connected. It is
  stated here, below `WeilConjectures.DeligneLaumon.AffineLine.Endpoints`, which uses it.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {U : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]

/-- Blueprint `lem-a1-affine-hc2`: Description of `H_c²` on an affine curve.

Let `U₀` be a smooth geometrically connected affine curve over `k₀ = 𝔽_q` and `F` a lisse Weil
sheaf on `U₀`, with local generic fibre `V`. There is a Frobenius-equivariant isomorphism
`H_c²(U, F) ≃ V_{π₁(U)}(-1)`, where the geometric coinvariants `V_{π₁(U)} = Γ(U, F^∨)^∨` carry the
Frobenius induced by the Weil structure and the Tate twist `(-1)` multiplies it by `q`. -/
theorem nonempty_equiv_compactlySupportedCohomology_two [IsAffine U]
    [SmoothOfRelativeDimension 1 (U ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (U ↘ Spec (CommRingCat.of k₀))] (F : WeilSheaf k₀ l U)
    (hF : F.IsLisse) :
    Nonempty ((F.compactlySupportedCohomology 2).Equiv
      ((F.geometricCoinvariants hF).tateTwist (Nat.card k₀) (-1))) := by
  sorry

/-- Blueprint `lem-a1-affine-hc2-pure`: Purity of `H_c²` on an affine curve.

Let `U₀` be a smooth geometrically connected affine curve and `F` a lisse Weil sheaf on `U₀`,
punctually `ι`-pure of weight `w`. Then `H_c²(U, F)` is `ι`-pure of weight `w + 2` (possibly
zero): it is the Tate twist `(-1)` of the geometric coinvariants
(`AlgebraicGeometry.WeilSheaf.nonempty_equiv_compactlySupportedCohomology_two`), which are pure
of weight `w` (`AlgebraicGeometry.WeilSheaf.isPureOfWeightOver_geometricCoinvariants`), and the
twist `(-1)` raises weights by two. -/
theorem isPureOfWeightOver_compactlySupportedCohomology_two [IsAffine U]
    [SmoothOfRelativeDimension 1 (U ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (U ↘ Spec (CommRingCat.of k₀))] (ι : PadicAlgCl l →+* ℂ)
    (F : WeilSheaf k₀ l U) (hF : F.IsLisse) {w : ℝ} (hw : F.IsPunctuallyPureOfWeight ι w) :
    (F.compactlySupportedCohomology 2).IsPureOfWeightOver k₀ ι (w + 2) := by
  obtain ⟨e⟩ := nonempty_equiv_compactlySupportedCohomology_two F hF
  have h := (isPureOfWeightOver_geometricCoinvariants ι F hF hw).tateTwist Nat.card_pos (-1)
  have hw2 : w - 2 * ((-1 : ℤ) : ℝ) = w + 2 := by push_cast; ring
  rw [hw2] at h
  exact FrobeniusModule.IsPureOfWeight.of_equiv e h

end WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

variable (ι : PadicAlgCl l →+* ℂ) in
/-- **Purity of the top affine-curve factor.** Let `C` be a smooth affine curve over `k₀` and let
`E` be a lisse Weil sheaf on `C`, punctually `ι`-pure of weight `0`. Then `H_c^2(C, E)` is
`ι`-pure of weight `2`: on each geometrically connected component, defined over a finite
extension of `k₀`, this is the degree-two endpoint estimate, and purity descends along the
finite constant extension (blueprint: `lem-zl-affine-curve-hc2-purity`). -/
theorem isPureOfWeightOver_compactlySupportedCohomology_two_of_isAffine {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k₀))] [IsAffine C]
    [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))] (E : WeilSheaf k₀ l C)
    (hE : E.IsLisse) (hpure : E.IsPunctuallyPureOfWeight ι 0) :
    -- `C ↘ Spec k₀` is locally of finite type, being smooth
    haveI := SmoothOfRelativeDimension.smooth 1 (C ↘ Spec (CommRingCat.of k₀))
    (E.compactlySupportedCohomology 2).IsPureOfWeightOver k₀ ι 2 :=
  -- TODO(adic): needs the endpoint lemma on each geometric component and descent of weights
  sorry

end AlgebraicGeometry
