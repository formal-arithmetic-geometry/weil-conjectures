/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.CurveEndpoints

/-!
# The extreme degrees on an affine curve

For a dense open immersion `j : U₀ ↪ C₀` into a smooth geometrically connected affine curve over
a finite field and a lisse Weil sheaf `F` on `U₀`, the compactly supported cohomology of `j_*F`
is concentrated in degrees one and two, its degree two part is the geometric coinvariants of `F`
Tate-twisted by `(-1)`, and it is pure of weight `w + 2` if `F` is pure of weight `w`. This
bundles the three clauses proved in `WeilConjectures.WeilSheaf.CurveEndpoints`.

## Main statements

- `AlgebraicGeometry.compactlySupportedCohomology_directImage_extremeDegrees`: blueprint
  `lemma-extreme-degrees-affine-curve`.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k₀))] [IsAffine C]
  [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))]
  [GeometricallyConnected (C ↘ Spec (CommRingCat.of k₀))]
  {U : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ C) [IsOpenImmersion j]
  [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))] [IsDominant j]
  (F : WeilSheaf k₀ l U)

/-- A smooth affine curve `C₀` is locally of finite type over `k₀`, being smooth over `k₀`. -/
local instance : LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₀)) :=
  have := SmoothOfRelativeDimension.smooth 1 (C ↘ Spec (CommRingCat.of k₀))
  inferInstance

/-- Blueprint `lemma-extreme-degrees-affine-curve`: the extreme degrees on an affine curve.

Let `j : U₀ ↪ C₀` be a dense open in a smooth geometrically connected affine curve over a finite
field `k₀`, and let `F` be a lisse Weil sheaf on `U₀`. Then
1. `H_c^r(C, j_*F) = 0` for `r ≠ 1, 2`
   (`AlgebraicGeometry.subsingleton_compactlySupportedCohomology_directImage` and
   `AlgebraicGeometry.subsingleton_compactlySupportedCohomology_directImage_zero`, blueprint
   `lemma-extreme-degrees-affine-curve--1`);
2. `H_c^2(C, j_*F) ≃ V_{π₁(U)}(-1)`, Frobenius-equivariantly, where `V_{π₁(U)}` are the geometric
   coinvariants of `F`
   (`AlgebraicGeometry.nonempty_equiv_compactlySupportedCohomology_directImage_two`, blueprint
   `lemma-extreme-degrees-affine-curve--2`);
3. if `F` is punctually `ι`-pure of weight `w`, then `H_c^2(C, j_*F)` is `ι`-pure of weight
   `w + 2` (`AlgebraicGeometry.isPureOfWeightOver_compactlySupportedCohomology_directImage_two`,
   blueprint `lemma-extreme-degrees-affine-curve--3`). -/
theorem compactlySupportedCohomology_directImage_extremeDegrees
    [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))] (hF : F.IsLisse) :
    (∀ r : ℤ, r ≠ 1 → r ≠ 2 →
      Subsingleton (((WeilSheaf.directImage j).obj F).compactlySupportedCohomology r).carrier) ∧
    Nonempty ((((WeilSheaf.directImage j).obj F).compactlySupportedCohomology 2).Equiv
      ((F.geometricCoinvariants hF).tateTwist (Nat.card k₀) (-1))) ∧
    ∀ (ι : PadicAlgCl l →+* ℂ) (w : ℝ), F.IsPunctuallyPureOfWeight ι w →
      (((WeilSheaf.directImage j).obj F).compactlySupportedCohomology 2).IsPureOfWeightOver
        k₀ ι (w + 2) := by
  refine ⟨fun r hr1 hr2 ↦ ?_, nonempty_equiv_compactlySupportedCohomology_directImage_two j F hF,
    fun ι w hw ↦ isPureOfWeightOver_compactlySupportedCohomology_directImage_two j F ι hF hw⟩
  rcases eq_or_ne r 0 with rfl | hr0
  · exact subsingleton_compactlySupportedCohomology_directImage_zero j F hF
  · exact subsingleton_compactlySupportedCohomology_directImage j F hF (by omega)

end AlgebraicGeometry
