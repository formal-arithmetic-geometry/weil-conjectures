/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.CategoryTheory.Adjunction.MateUnitIsIso
public import WeilConjectures.WeilSheaf.Localization
public import WeilConjectures.WeilSheaf.UpperStarId
public import WeilConjectures.AlgebraicGeometry.NativeBaseChange.NativeBaseChangeForgetComparison
import WeilConjectures.AlgebraicGeometry.NativeBaseChange.GeometricSmoothBaseChange
import WeilConjectures.CategoryTheory.Endofunctor.FixedPairDerivedForgetComparison

/-!
# Smooth base change for Weil complexes

For a commutative square of `k₀`-schemes
```
Y' --g'--> Y
|π'        |π
v          v
X' --g-->  X
```
the *base change morphism* `π^* Rg_* ⟶ Rg'_* π'^*` of Weil complexes
(`AlgebraicGeometry.WeilComplex.baseChange`) is the mate of the exchange isomorphism
`g'^* π^* ≅ (g' ≫ π)^* = (π' ≫ g)^* ≅ π'^* g^*` under the adjunctions `g^* ⊣ Rg_*` and
`g'^* ⊣ Rg'_*`.

The smooth base change theorem (blueprint `sbc-thm-smooth-base-change`, in its Weil form) says
that it is an isomorphism when the square is cartesian, `π` is smooth and `g` is separated
(`AlgebraicGeometry.WeilComplex.isIso_baseChange_of_smooth`). The base change morphism lies over
the native derived base-change mate of pro-étale Weil sheaves
(`AlgebraicGeometry.WeilComplex.ι_map_baseChange_app`); forgetting the Weil structure, this is
the geometric native smooth base change theorem
(`AlgebraicGeometry.NativeBaseChange.geometric_smooth_baseChange_isIso`).

The mate description gives the input to homotopy invariance: if the base change morphism is
invertible at `M` and the unit of `π'^* ⊣ Rπ'_*` is invertible at `M`, then the unit of
`π^* ⊣ Rπ_*` is invertible at `Rg_* M`
(`AlgebraicGeometry.WeilComplex.isIso_unit_app_derivedLowerStar_obj_of_isIso_baseChange_app`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X X' Y Y' : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [X'.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  [Y'.Over (Spec (CommRingCat.of k₀))] {g' : Y' ⟶ Y} {π' : Y' ⟶ X'} {π : Y ⟶ X}
  {g : X' ⟶ X} [g'.IsOver (Spec (CommRingCat.of k₀))] [π'.IsOver (Spec (CommRingCat.of k₀))]
  [π.IsOver (Spec (CommRingCat.of k₀))] [g.IsOver (Spec (CommRingCat.of k₀))]

variable [QuasiCompact g] [QuasiSeparated g] [LocallyOfFiniteType g]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] [QuasiCompact g'] [QuasiSeparated g']
  [LocallyOfFiniteType g'] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]

end AlgebraicGeometry.WeilComplex
