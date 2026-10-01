/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.DeligneLaumon.AffineLine.Defs

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
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {U C : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [C.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ C) [IsOpenImmersion j] [QuasiCompact j]
  [j.IsOver (Spec (CommRingCat.of k₀))] [IsDominant j] [IsAffine C]
  [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))]
  [GeometricallyConnected (C ↘ Spec (CommRingCat.of k₀))]
  (F : WeilSheaf k₀ l U)

/-- For a dense open immersion `j : U₀ ↪ C₀` with `C₀` a smooth geometrically connected affine
curve and `F` lisse on `U₀`, the compactly supported cohomology `H_c^r(C, j_*F)` vanishes for
every `r` outside `{0, 1, 2}`. (blueprint: `sk-l-dl-a1-endpoints`) -/
theorem subsingleton_compactlySupportedCohomology_directImage (hF : F.IsLisse) {r : ℤ}
    (hr : r < 0 ∨ 2 < r) :
    Subsingleton
      (((WeilSheaf.directImage j).obj F).compactlySupportedCohomology r).carrier := by
  sorry

/-- In the situation of `AlgebraicGeometry.subsingleton_compactlySupportedCohomology_directImage`
the degree-zero compactly supported cohomology `H_c^0(C, j_*F)` vanishes, because a nonzero
global section of a lisse sheaf on a connected open has full support on a nonproper curve.
(blueprint: `sk-l-dl-a1-endpoints`) -/
theorem subsingleton_compactlySupportedCohomology_directImage_zero (hF : F.IsLisse) :
    Subsingleton
      (((WeilSheaf.directImage j).obj F).compactlySupportedCohomology 0).carrier := by
  sorry

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
  sorry

/-- If `F` is moreover punctually `ι`-pure of weight `w`, then `H_c^2(C, j_*F)` is pure of
weight `w + 2`: the Tate twist of
`AlgebraicGeometry.nonempty_equiv_compactlySupportedCohomology_directImage_two` raises weights
by two. (blueprint: `sk-l-dl-a1-endpoints`) -/
theorem isPureOfWeightOver_compactlySupportedCohomology_directImage_two
    (ι : PadicAlgCl l →+* ℂ) (hF : F.IsLisse) {w : ℝ}
    (hw : F.IsPunctuallyPureOfWeight ι w) :
    (((WeilSheaf.directImage j).obj F).compactlySupportedCohomology 2).IsPureOfWeightOver
      k₀ ι (w + 2) := by
  sorry

end AlgebraicGeometry
