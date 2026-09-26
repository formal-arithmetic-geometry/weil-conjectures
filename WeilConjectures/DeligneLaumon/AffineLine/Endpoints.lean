/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.DeligneLaumon.AffineLine.Setup

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

- `AlgebraicGeometry.compactlySupportedCohomology_directImage_endpoints`: vanishing outside
  `0, 1, 2`, vanishing in degree zero, the coinvariant description of degree two, and its
  purity.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]

/-- Blueprint `sk-l-dl-a1-endpoints`: Degree zero and degree two. Let `j : U₀ ↪ C₀` be a dense
open immersion with `C₀` a smooth geometrically connected affine curve and let `F` be lisse on
`U₀`, with generic geometric representation `V`. Then `H_c^r(C, j_*F)` vanishes for `r` outside
`{0, 1, 2}` and in degree zero; `H_c^2(C, j_*F)` is the coinvariant module `V_{π₁(U)}` twisted
by `(-1)`, so that its geometric Frobenius is `q` times the one on the coinvariants; and if `F`
is punctually `ι`-pure of weight `w`, then `H_c^2(C, j_*F)` is pure of weight `w + 2`. -/
theorem compactlySupportedCohomology_directImage_endpoints (ι : PadicAlgCl l →+* ℂ)
    {U C : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))] [C.Over (Spec (CommRingCat.of k₀))]
    (j : U ⟶ C) [IsOpenImmersion j] [j.IsOver (Spec (CommRingCat.of k₀))] [IsDominant j]
    [IsAffine C] [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (C ↘ Spec (CommRingCat.of k₀))]
    (F : WeilSheaf k₀ l U) (hF : F.IsLisse) (J : WeilSheaf k₀ l C)
    (hJ : J = (WeilSheaf.directImage j).obj F) (w : ℝ) :
    (∀ r : ℤ, r < 0 ∨ 2 < r → Subsingleton (J.compactlySupportedCohomology r).carrier) ∧
      Subsingleton (J.compactlySupportedCohomology 0).carrier ∧
      (∃ e : (J.compactlySupportedCohomology 2).carrier ≃ₗ[PadicAlgCl l]
          F.geometricCoinvariants.carrier,
        ∀ v, e ((J.compactlySupportedCohomology 2).frobenius v) =
          (Nat.card k₀ : PadicAlgCl l) • F.geometricCoinvariants.frobenius (e v)) ∧
      (F.IsPunctuallyPureOfWeight ι w →
        (J.compactlySupportedCohomology 2).IsPureOfWeight ι (Nat.card k₀) (w + 2)) := by
  sorry

end AlgebraicGeometry
