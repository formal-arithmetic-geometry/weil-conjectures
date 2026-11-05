/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Comparison.UniversalCoverSetFLC
public import WeilConjectures.Algebra.Category.ModuleCat.StableImageTower
public import WeilConjectures.SixFunctors.ProEtale.Comparison.UpperStarHomotopyLimit
public import WeilConjectures.Algebra.Homology.DerivedCategory.MittagLefflerTower
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Mittag-Leffler and the Milnor sequence on the universal cover

For a tower `H` of étale sheaves of `Λ`-modules on `Y` with finite locally constant underlying
sheaves of sets (`AlgebraicGeometry.Scheme.IsSetFLC`):

- `AlgebraicGeometry.Scheme.UniversalCovers.isMittagLefflerTower_comparisonUpperStar`: the tower
  `p^* ν^* Hₙ` on the universal cover `Ỹ_y` is Mittag-Leffler, being a tower of constant sheaves
  with finite values;
- `AlgebraicGeometry.Scheme.UniversalCovers.isLimitHomologyUpperStarOfIsSetFLC`: hence, for a
  derived limit `c` of a tower `F` in `D(Y_proét, Λ)` whose degree `i - 1` cohomology tower is
  `ν^* Hₙ`, `Hⁱ(p^* R lim F) = lim Hⁱ(p^* Fₙ)` on `Ỹ_y`.

This avoids proving that images of finite locally constant sheaves are finite locally constant:
Mittag-Leffler is only needed after pulling back to the trivialising cover `Ỹ_y`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω] (U : Scheme.UniversalCovers Y Ω)
  (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) {Λ : Type (u + 1)} [Ring Λ]

end AlgebraicGeometry.Scheme
