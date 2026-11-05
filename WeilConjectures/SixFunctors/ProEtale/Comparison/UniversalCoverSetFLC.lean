/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.SetLocallyConstant
public import WeilConjectures.SixFunctors.ProEtale.Adic.UniversalCoverTowerLimit
public import Mathlib.Algebra.Group.Shrink

/-!
# Locally constant sheaves with finite stalks on the universal cover, for any coefficients

The results of `WeilConjectures.SixFunctors.ProEtale.Comparison.UniversalCoverConstant` for
sheaves of `Λ`-modules over an arbitrary ring `Λ` whose underlying sheaves of sets are finite
locally constant (`AlgebraicGeometry.Scheme.IsSetFLC`), e.g. abelian sheaves with finite stalks
via `Λ = ULift ℤ`:

- `AlgebraicGeometry.Scheme.IsSetFLC.upperStar`: stability under pullback;
- `AlgebraicGeometry.Scheme.UniversalCovers.bijective_sectionsGerm'_upperStar`,
  `UniversalCovers.upperStarIsoConstantSheaf'`,
  `UniversalCovers.comparisonUpperStarIsoConstantSheaf'`,
  `UniversalCovers.towerComparisonUpperStarIsoConstantSheaf'`: such sheaves (and towers of them)
  become constant with value the stalk at `y` on the universal cover `Ỹ_y`, naturally;
- `AlgebraicGeometry.Scheme.UniversalCovers.exists_isLimit_towerComparisonUpperStar'`: the
  abelian tower underlying `p^* ν^* Hₙ` has limit `C(-, lim_n (Hₙ)_y)`, the finite stalks being
  made discrete groups in `Type` (`DiscreteShrink`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

section Pullback

variable {X Z : Scheme.{u}} (g : Z ⟶ X) {Λ : Type (u + 1)} [Ring Λ]
  {H : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (hH : IsSetFLC H) (P : X.FiniteEtale)
  (ι : (FiniteEtale.toFLC X).obj P ≅ hH.toFLC)

end Pullback

section Sections

variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω] (U : Scheme.UniversalCovers Y Ω)
  (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) {Λ : Type (u + 1)} [Ring Λ]
  {H : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (hH : IsSetFLC H)

end Sections

section Constant

variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω] (U : Scheme.UniversalCovers Y Ω)
  (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) (Λ : Type (u + 1)) [Ring Λ]

end Constant

end AlgebraicGeometry.Scheme

namespace DiscreteShrink

variable (α : Type*) [Small.{0} α]

end DiscreteShrink

namespace AlgebraicGeometry.Scheme

variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω] (U : Scheme.UniversalCovers Y Ω)
  (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) {Λ : Type (u + 1)} [Ring Λ]

end AlgebraicGeometry.Scheme
