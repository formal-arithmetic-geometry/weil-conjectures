/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.WeilSheaf.Cohomology

/-!
# Compactly supported cohomology of a lisse Weil sheaf on an affine curve

On a smooth geometrically connected affine curve `U₀` over a finite field, a lisse Weil sheaf
has no compactly supported cohomology in degree zero: a compactly supported global section of a
lisse sheaf is locally constant, so its support is open and closed, hence empty or all of the
connected curve `U`, which is not proper.

## Main statements

- `AlgebraicGeometry.WeilSheaf.subsingleton_compactlySupportedCohomology_zero`
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

-- TODO(adic): prove once Weil sheaves carry genuine `ℓ`-adic coefficients
/-- Blueprint `lem-a1-affine-hc0`: Vanishing of `H_c⁰` on a nonproper curve.

Let `U₀` be a smooth geometrically connected affine curve and `ℱ` a lisse Weil sheaf on `U₀`.
Then `H_c⁰ (U, ℱ) = 0`.

A class in `H_c⁰` is a global section of `ℱ` whose support is proper over the base field. By
lissity a global section of `ℱ` is locally constant, so on the connected curve `U` it vanishes
as soon as it vanishes at one geometric point; the support of a nonzero section is therefore
all of `U`, which is not proper. -/
theorem subsingleton_compactlySupportedCohomology_zero [IsAffine U]
    [SmoothOfRelativeDimension 1 (U ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (U ↘ Spec (CommRingCat.of k₀))] (F : WeilSheaf k₀ l U)
    (hF : F.IsLisse) :
    Subsingleton (F.compactlySupportedCohomology 0).carrier := by
  sorry

end WeilSheaf

end AlgebraicGeometry
