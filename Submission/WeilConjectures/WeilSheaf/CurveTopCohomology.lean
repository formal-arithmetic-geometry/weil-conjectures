/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Submission.WeilConjectures.WeilSheaf.Cohomology
public import Submission.WeilConjectures.WeilSheaf.CohomologyZero
public import Submission.WeilConjectures.WeilSheaf.Dual
public import Submission.WeilConjectures.WeilSheaf.GeometricCoinvariants
public import Submission.WeilConjectures.WeilSheaf.LissePoincarePairing

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

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
  (`lem-a1-affine-hc2`), from the lisse Poincaré pairing
  `AlgebraicGeometry.WeilSheaf.exists_isPerfPair_compactlySupportedCohomology_dual_mul` (from the
  lisse case of `thm-pod-degreewise-perfectness-over-a-field`).
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
  obtain ⟨P, hP, hPF⟩ :=
    exists_isPerfPair_compactlySupportedCohomology_dual_mul 1 F hF 2 0 (by norm_num)
  have hq : (Nat.card k₀ : PadicAlgCl l) ^ (-(-1 : ℤ)) ≠ 0 :=
    zpow_ne_zero _ (Nat.cast_ne_zero.2 Nat.card_pos.ne')
  exact ⟨(FrobeniusModule.Equiv.ofIsPerfPair P hq fun x y ↦ by
    rw [hPF, neg_neg, zpow_one, pow_one]).trans
      ((cohomologyZeroEquiv (F.dual hF)).dual.rescale _)⟩

end WeilSheaf

end AlgebraicGeometry
