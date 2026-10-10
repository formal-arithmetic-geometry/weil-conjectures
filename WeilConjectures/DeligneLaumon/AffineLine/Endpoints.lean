/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.DeligneLaumon.AffineLine.Defs
public import WeilConjectures.WeilSheaf.GeometricCoinvariants

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
- `AlgebraicGeometry.WeilSheaf.hasWeightsAtMostOver_compactlySupportedCohomology_two`: the top
  compactly supported cohomology of a pure lisse sheaf on a smooth affine curve has weights at
  most `w + 2`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k₀))] [IsAffine C]
  [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))]

/-- A smooth affine curve `C₀` is locally of finite type over `k₀`, being smooth over `k₀`. -/
local instance : LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₀)) :=
  haveI := SmoothOfRelativeDimension.smooth 1 (C ↘ Spec (CommRingCat.of k₀))
  inferInstance

/-- *Top compact-support bound on a curve.* If `C₀` is a smooth affine curve and `G` is a lisse
Weil sheaf on `C₀`, punctually `ι`-pure of weight `w`, then `H_c^2(C, G)` has weights at most
`w + 2`: it is a Frobenius-equivariant quotient of the generic fibre, pure of weight `w`, twisted
by `(-1)`.
(blueprint: `lem-a1-curve-hc2-bound`) -/
theorem WeilSheaf.hasWeightsAtMostOver_compactlySupportedCohomology_two
    (ι : PadicAlgCl l →+* ℂ) (G : WeilSheaf k₀ l C) (hG : G.IsLisse) {w : ℝ}
    (hw : G.IsPunctuallyPureOfWeight ι w) :
    (G.compactlySupportedCohomology 2).HasWeightsAtMostOver k₀ ι (w + 2) := by
  -- TODO(adic): prove once Weil sheaves carry genuine `ℓ`-adic coefficients
  sorry

variable {U : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ C) [IsOpenImmersion j]
  [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))] [IsDominant j]
  [GeometricallyConnected (C ↘ Spec (CommRingCat.of k₀))]
  (F : WeilSheaf k₀ l U)

/-- For a dense open immersion `j : U₀ ↪ C₀` with `C₀` a smooth geometrically connected affine
curve and `F` lisse on `U₀`, the compactly supported cohomology `H_c^r(C, j_*F)` vanishes for
every `r` outside `{0, 1, 2}`. (blueprint: `sk-l-dl-a1-endpoints`) -/
theorem subsingleton_compactlySupportedCohomology_directImage (hF : F.IsLisse) {r : ℤ}
    (hr : r < 0 ∨ 2 < r) :
    Subsingleton
      (((WeilSheaf.directImage j).obj F).compactlySupportedCohomology r).carrier := by
  -- TODO(adic): prove once Weil sheaves carry genuine `ℓ`-adic coefficients
  sorry

/-- In the situation of `AlgebraicGeometry.subsingleton_compactlySupportedCohomology_directImage`
the degree-zero compactly supported cohomology `H_c^0(C, j_*F)` vanishes, because a nonzero
global section of a lisse sheaf on a connected open has full support on a nonproper curve.
(blueprint: `sk-l-dl-a1-endpoints`) -/
theorem subsingleton_compactlySupportedCohomology_directImage_zero (hF : F.IsLisse) :
    Subsingleton
      (((WeilSheaf.directImage j).obj F).compactlySupportedCohomology 0).carrier := by
  -- TODO(adic): prove once Weil sheaves carry genuine `ℓ`-adic coefficients
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
theorem nonempty_equiv_compactlySupportedCohomology_directImage_two
    [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))] (hF : F.IsLisse) :
    Nonempty ((((WeilSheaf.directImage j).obj F).compactlySupportedCohomology 2).Equiv
      ((F.geometricCoinvariants hF).tateTwist (Nat.card k₀) (-1))) := by
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
  have : QuasiCompact (C ↘ Spec (CommRingCat.of k₀)) := inferInstance
  have : QuasiCompact (U ↘ Spec (CommRingCat.of k₀)) := by
    rw [← CategoryTheory.comp_over j (Spec (CommRingCat.of k₀))]; infer_instance
  have : LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀)) := by
    rw [← CategoryTheory.comp_over j (Spec (CommRingCat.of k₀))]; infer_instance
  obtain ⟨e⟩ := nonempty_equiv_compactlySupportedCohomology_directImage_two j F hF
  have h := (WeilSheaf.isPureOfWeightOver_geometricCoinvariants ι F hF hw).tateTwist
    Nat.card_pos (-1)
  have h' : w - 2 * ((-1 : ℤ) : ℝ) = w + 2 := by push_cast; ring
  rw [h'] at h
  exact FrobeniusModule.IsPureOfWeight.of_equiv e h

end AlgebraicGeometry
