/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.BaseChange.GeometricFrobenius
public import WeilConjectures.WeilSheaf.Category

/-!
# The derived pushforward of Weil complexes

For a morphism `φ : X ⟶ Y` of `k₀`-schemes, the total right derived pushforward `Rφ̄_*` along
its base change `φ̄ : X̄ ⟶ Ȳ` to the geometric fibers commutes with the Frobenius pullbacks
(`Etale.rightDerivedLowerStarGeometricFiberMapCompFrobeniusIso`), so it carries Weil complexes
on `X` to Weil complexes on `Y`. No compactification is involved.

## Main definitions

- `AlgebraicGeometry.WeilComplex.rightDerivedLowerStar`: `Rφ_*` on Weil complexes.
-/

@[expose] public section

universe u

open CategoryTheory Endofunctor

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]

variable (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]

/-- The derived pushforward `Rφ_*` of Weil complexes along a morphism `φ : X ⟶ Y` of
`k₀`-schemes: the total right derived pushforward along the base change `φ̄ : X̄ ⟶ Ȳ`, with
the Weil structure transported along
`Etale.rightDerivedLowerStarGeometricFiberMapCompFrobeniusIso`. -/
noncomputable def WeilComplex.rightDerivedLowerStar :
    WeilComplex k₀ l X ⥤ WeilComplex k₀ l Y :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ IsoAlgebra.mapOfNatIso
      (Etale.rightDerivedLowerStarGeometricFiberMapCompFrobeniusIso _ φ (comp_over φ _)))
    fun _ ↦ sorry

instance : (WeilComplex.rightDerivedLowerStar (k₀ := k₀) (l := l) φ).Additive :=
  IsoAlgebra.additive_lift_mapOfNatIso (P := WeilComplex.objectProperty k₀ l X)
    (Q := WeilComplex.objectProperty k₀ l Y) _ _

end AlgebraicGeometry
