/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.DeligneLaumon.AffineLine.Defs
public import WeilConjectures.WeilSheaf.Dual

/-!
# The two endpoints of the compactly supported cohomology of a middle extension

For a dense open immersion `j : U₀ ↪ C₀` into a smooth geometrically connected affine curve
and a lisse Weil sheaf `F` on `U₀`, all the compactly supported cohomology of the ordinary
direct image `j_*F` outside degrees `0, 1, 2` vanishes, degree zero vanishes as well because a
nonzero global section of a lisse sheaf on a connected open has full support on a nonproper
curve, and degree two is the geometric coinvariants `V_{π₁(U)}` Tate-twisted by `(-1)`, by
global Verdier duality on the smooth nonproper curve `U`. Purity of `F` of weight `w`
therefore makes degree two pure of weight `w + 2`.

This leaves degree one, which is the only place where the Fourier argument of
`WeilConjectures.DeligneLaumon.AffineLine.DegreeOne` is needed.

## Main statements

- `AlgebraicGeometry.subsingleton_compactlySupportedCohomology_directImage`: vanishing outside
  degrees `0, 1, 2`.
- `AlgebraicGeometry.subsingleton_compactlySupportedCohomology_directImage_zero`: vanishing in
  degree zero.
- `AlgebraicGeometry.nonempty_equiv_compactlySupportedCohomology_directImage_two`: the
  coinvariant description of degree two.
- `AlgebraicGeometry.isPureOfWeightOver_compactlySupportedCohomology_directImage_two`: its
  purity.
- `AlgebraicGeometry.WeilSheaf.subsingleton_compactlySupportedCohomology_of_isAffine`: the
  cohomological range `{0, 1, 2}` of a smooth affine curve.
- `AlgebraicGeometry.WeilSheaf.hasWeightsAtMostOver_compactlySupportedCohomology_two`: the top
  compactly supported cohomology of a pure lisse sheaf on a smooth affine curve has weights at
  most `w + 2`.

With the present coefficients every Weil complex and every compactly supported cohomology group
is zero (`AlgebraicGeometry.WeilComplex.subsingleton_compactlySupportedCohomology_carrier`), and
the vanishing statements are proved this way.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

section Curve

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k₀))] [IsAffine C]
  [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))]

/-- A smooth affine curve `C₀` is locally of finite type over `k₀`, being smooth over `k₀`. -/
local instance : LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₀)) :=
  haveI := SmoothOfRelativeDimension.smooth 1 (C ↘ Spec (CommRingCat.of k₀))
  inferInstance

-- the provisional Weil sheaves are zero, and the proof needs no hypothesis
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
/-- *Cohomological range of an affine curve.* If `C₀` is a smooth affine curve and `G` is a
constructible Weil sheaf on `C₀`, then `H_c^r(C, G) = 0` for `r ∉ {0, 1, 2}`: after a smooth
compactification `C ↪ C̄`, `H_c^r(C, G) = H^r(C̄, j_!G)` is the cohomology of a sheaf on a proper
curve, of cohomological dimension two.

With the present coefficients every compactly supported cohomology group is zero
(`AlgebraicGeometry.WeilComplex.subsingleton_compactlySupportedCohomology_carrier`), which is how
the statement is proved here.
(blueprint: `lem-zl-affine-curve-range`) -/
theorem WeilSheaf.subsingleton_compactlySupportedCohomology_of_isAffine
    (G : WeilSheaf k₀ l C) {r : ℤ} (hr : r < 0 ∨ 2 < r) :
    Subsingleton (G.compactlySupportedCohomology r).carrier :=
  (toComplex.obj G).subsingleton_compactlySupportedCohomology_carrier r

-- the provisional Weil sheaves are zero, and the proof needs no hypothesis
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
/-- *Top compact-support bound on a curve.* If `C₀` is a smooth affine curve and `G` is a lisse
Weil sheaf on `C₀`, punctually `ι`-pure of weight `w`, then `H_c^2(C, G)` has weights at most
`w + 2`: it is a Frobenius-equivariant quotient of the generic fibre, pure of weight `w`, twisted
by `(-1)`.

With the present coefficients `H_c^2(C, G)` is zero
(`AlgebraicGeometry.WeilComplex.subsingleton_compactlySupportedCohomology_carrier`), which is how
the statement is proved here.
(blueprint: `lem-a1-curve-hc2-bound`) -/
theorem WeilSheaf.hasWeightsAtMostOver_compactlySupportedCohomology_two
    (ι : PadicAlgCl l →+* ℂ) (G : WeilSheaf k₀ l C) (hG : G.IsLisse) {w : ℝ}
    (hw : G.IsPunctuallyPureOfWeight ι w) :
    (G.compactlySupportedCohomology 2).HasWeightsAtMostOver k₀ ι (w + 2) :=
  have : Subsingleton (G.compactlySupportedCohomology 2).carrier :=
    (toComplex.obj G).subsingleton_compactlySupportedCohomology_carrier 2
  (FrobeniusModule.isPureOfWeight_of_subsingleton _ _).hasWeightsAtMost

end Curve

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {U C : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [C.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ C) [IsOpenImmersion j] [QuasiCompact j]
  [j.IsOver (Spec (CommRingCat.of k₀))] [IsDominant j] [IsAffine C]
  [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))]
  [GeometricallyConnected (C ↘ Spec (CommRingCat.of k₀))]
  (F : WeilSheaf k₀ l U)

/-- The curve `C₀` is locally of finite type over `k₀`, being smooth over `k₀`. -/
local instance : LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₀)) :=
  haveI := SmoothOfRelativeDimension.smooth 1 (C ↘ Spec (CommRingCat.of k₀))
  inferInstance

-- the provisional Weil sheaves are zero, and the proof needs no hypothesis
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
/-- For a dense open immersion `j : U₀ ↪ C₀` with `C₀` a smooth geometrically connected affine
curve and `F` lisse on `U₀`, the compactly supported cohomology `H_c^r(C, j_*F)` vanishes for
every `r` outside `{0, 1, 2}`. (blueprint: `sk-l-dl-a1-endpoints`) -/
theorem subsingleton_compactlySupportedCohomology_directImage (hF : F.IsLisse) {r : ℤ}
    (hr : r < 0 ∨ 2 < r) :
    Subsingleton
      (((WeilSheaf.directImage j).obj F).compactlySupportedCohomology r).carrier :=
  -- the range of the affine curve `C₀`, `lem-zl-affine-curve-range`
  ((WeilSheaf.directImage j).obj F).subsingleton_compactlySupportedCohomology_of_isAffine hr

-- the provisional Weil sheaves are zero, and the proof needs no hypothesis
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
/-- In the situation of `AlgebraicGeometry.subsingleton_compactlySupportedCohomology_directImage`
the degree-zero compactly supported cohomology `H_c^0(C, j_*F)` vanishes, because a nonzero
global section of a lisse sheaf on a connected open has full support on a nonproper curve.
(blueprint: `sk-l-dl-a1-endpoints`) -/
theorem subsingleton_compactlySupportedCohomology_directImage_zero (hF : F.IsLisse) :
    Subsingleton
      (((WeilSheaf.directImage j).obj F).compactlySupportedCohomology 0).carrier :=
  -- `H_c^0(C, j_*F)` is zero, see `WeilComplex.subsingleton_compactlySupportedCohomology_carrier`
  (WeilSheaf.toComplex.obj _).subsingleton_compactlySupportedCohomology_carrier 0

-- the provisional Weil sheaves are zero, and the proof needs no hypothesis
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
/--
In degree two, global Verdier duality on the smooth nonproper curve `U` identifies
`H_c^2(C, j_*F)` with the geometric coinvariants `V_{π₁(U)}` of `F`, Tate-twisted by `(-1)`:
the Frobenius of the cohomology is `q` times the Frobenius of the coinvariants.

```
  H_c²(C, j_*F) ──e──▶ V_{π₁(U)}
        │                 │
   Frob │                 │ q · Frob
        ▼                 ▼
  H_c²(C, j_*F) ──e──▶ V_{π₁(U)}
```
(blueprint: `sk-l-dl-a1-endpoints`)
-/
theorem nonempty_equiv_compactlySupportedCohomology_directImage_two (hF : F.IsLisse) :
    Nonempty ((((WeilSheaf.directImage j).obj F).compactlySupportedCohomology 2).Equiv
      (F.geometricCoinvariants.tateTwist (Nat.card k₀) (-1))) := by
  -- both sides are zero, see `WeilComplex.subsingleton_compactlySupportedCohomology_carrier` and
  -- `WeilSheaf.subsingleton_geometricCoinvariants_carrier`
  have : Subsingleton
      (((WeilSheaf.directImage j).obj F).compactlySupportedCohomology 2).carrier :=
    (WeilSheaf.toComplex.obj _).subsingleton_compactlySupportedCohomology_carrier 2
  have : Subsingleton (F.geometricCoinvariants.tateTwist (Nat.card k₀) (-1)).carrier :=
    F.subsingleton_geometricCoinvariants_carrier
  exact ⟨⟨LinearEquiv.ofSubsingleton _ _, fun _ ↦ Subsingleton.elim _ _⟩⟩

/-- If `F` is moreover punctually `ι`-pure of weight `w`, then `H_c^2(C, j_*F)` is pure of
weight `w + 2`: the Tate twist of
`AlgebraicGeometry.nonempty_equiv_compactlySupportedCohomology_directImage_two` raises weights
by two. (blueprint: `sk-l-dl-a1-endpoints`) -/
theorem isPureOfWeightOver_compactlySupportedCohomology_directImage_two
    (ι : PadicAlgCl l →+* ℂ) (hF : F.IsLisse) {w : ℝ}
    (hw : F.IsPunctuallyPureOfWeight ι w) :
    (((WeilSheaf.directImage j).obj F).compactlySupportedCohomology 2).IsPureOfWeightOver
      k₀ ι (w + 2) := by
  obtain ⟨e⟩ := nonempty_equiv_compactlySupportedCohomology_directImage_two j F hF
  have h := (F.isPureOfWeightOver_geometricCoinvariants ι hF hw).tateTwist Nat.card_pos (-1)
  rw [Int.cast_neg, Int.cast_one, mul_neg_one, sub_neg_eq_add] at h
  exact h.of_equiv e

end AlgebraicGeometry
