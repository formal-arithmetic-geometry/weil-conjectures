/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.GeometricFrobenius
public import WeilConjectures.WeilSheaf.Category

/-!
# The pushforward of Weil sheaves and Weil complexes

For a morphism `φ : X ⟶ Y` of `k₀`-schemes, the pushforward `φ̄_*` and the total right derived
pushforward `Rφ̄_*` along its base change `φ̄ : X̄ ⟶ Ȳ` to the geometric fibers commute with the
Frobenius pullbacks (`Etale.lowerStarGeometricFiberMapCompFrobeniusIso`,
`Etale.rightDerivedLowerStarGeometricFiberMapCompFrobeniusIso`), so they carry Weil sheaves and
Weil complexes on `X` to Weil sheaves and Weil complexes on `Y`. This mirrors the pullbacks
`WeilSheaf.upperStar` and `WeilComplex.upperStar`. No compactification is involved.

That the results are again constructible, respectively bounded constructible, is the finiteness
theorem (SGA 4½, *Th. finitude*). It needs `φ` quasi-compact, quasi-separated and of finite
type, which are hypotheses of the definitions below, and `X` and `Y` of finite type over `k₀`,
which the scaffold `WeilSheaf` does not record. These constructibility statements are left as
`sorry`.

## Main definitions

- `AlgebraicGeometry.WeilSheaf.lowerStar`: `φ_*` on Weil sheaves.
- `AlgebraicGeometry.WeilComplex.derivedLowerStar`: `Rφ_*` on Weil complexes.
- `AlgebraicGeometry.WeilSheaf.higherLowerStar`: the higher direct images `Rⁱφ_*` of Weil
  sheaves, the cohomology sheaves of `Rφ_*`.
-/

@[expose] public section

universe u

open CategoryTheory Endofunctor

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Etale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]

-- The finiteness hypotheses of the next declarations only enter the `sorry`ed constructibility
-- statements, so they are spelled out rather than taken from a `variable` block, which would
-- drop them.

/-- The pushforward `φ_*` of Weil sheaves along a morphism `φ : X ⟶ Y` of `k₀`-schemes: the
pushforward along the base change `φ̄ : X̄ ⟶ Ȳ`, with the Weil structure transported along
`Etale.lowerStarGeometricFiberMapCompFrobeniusIso`. -/
noncomputable def WeilSheaf.lowerStar (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]
    [QuasiCompact φ] [QuasiSeparated φ] [LocallyOfFiniteType φ] :
    WeilSheaf k₀ l X ⥤ WeilSheaf k₀ l Y :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ IsoAlgebra.mapOfNatIso
      (Etale.lowerStarGeometricFiberMapCompFrobeniusIso _ φ (comp_over φ _)))
    -- TODO: the finiteness theorem for `φ̄_*` (SGA 4½, Th. finitude).
    fun _ ↦ sorry

/-- The derived pushforward `Rφ_*` of Weil complexes along a morphism `φ : X ⟶ Y` of
`k₀`-schemes: the total right derived pushforward along the base change `φ̄ : X̄ ⟶ Ȳ`, with
the Weil structure transported along
`Etale.rightDerivedLowerStarGeometricFiberMapCompFrobeniusIso`. -/
noncomputable def WeilComplex.derivedLowerStar (φ : X ⟶ Y)
    [φ.IsOver (Spec (CommRingCat.of k₀))] [QuasiCompact φ] [QuasiSeparated φ]
    [LocallyOfFiniteType φ] :
    WeilComplex k₀ l X ⥤ WeilComplex k₀ l Y :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ IsoAlgebra.mapOfNatIso
      (Etale.rightDerivedLowerStarGeometricFiberMapCompFrobeniusIso _ φ (comp_over φ _)))
    -- TODO: the finiteness theorem for `Rφ̄_*` (SGA 4½, Th. finitude).
    fun _ ↦ sorry

/-- The higher direct image `Rⁱφ_*` of Weil sheaves along a morphism `φ : X ⟶ Y` of
`k₀`-schemes: the cohomology sheaf `𝓗ⁱ` (indexed by `ℤ`, with `i : ℕ` coerced) of the derived
pushforward `Rφ_*` of a Weil sheaf placed in degree zero. -/
noncomputable def WeilSheaf.higherLowerStar (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]
    [QuasiCompact φ] [QuasiSeparated φ] [LocallyOfFiniteType φ] (i : ℕ) :
    WeilSheaf k₀ l X ⥤ WeilSheaf k₀ l Y :=
  toComplex ⋙ WeilComplex.derivedLowerStar φ ⋙ WeilComplex.homologySheaf i

variable (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))] [QuasiCompact φ] [QuasiSeparated φ]
  [LocallyOfFiniteType φ]

namespace WeilSheaf

@[simp]
lemma lowerStar_obj_obj_carrier (F : WeilSheaf k₀ l X) :
    ((lowerStar φ).obj F).obj.carrier =
      (Scheme.Hom.geometricFiberMap φ (comp_over φ _))_*[_].obj F.obj.carrier :=
  rfl

@[simp]
lemma lowerStar_obj_obj_str (F : WeilSheaf k₀ l X) :
    ((lowerStar φ).obj F).obj.str =
      (Etale.lowerStarGeometricFiberMapCompFrobeniusIso _ φ (comp_over φ _)).app
          F.obj.carrier ≪≫
        (Scheme.Hom.geometricFiberMap φ (comp_over φ _))_*[_].mapIso F.obj.str :=
  IsoAlgebra.mapOfNatIso_obj_str _ _

@[simp]
lemma lowerStar_map_hom_hom_f {F G : WeilSheaf k₀ l X} (α : F ⟶ G) :
    ((lowerStar φ).map α).hom.hom.f =
      (Scheme.Hom.geometricFiberMap φ (comp_over φ _))_*[_].map α.hom.hom.f :=
  rfl

instance : (lowerStar (k₀ := k₀) (l := l) φ).Additive :=
  IsoAlgebra.additive_lift_mapOfNatIso (P := WeilSheaf.objectProperty k₀ l X)
    (Q := WeilSheaf.objectProperty k₀ l Y) _ _

end WeilSheaf

instance : (WeilComplex.derivedLowerStar (k₀ := k₀) (l := l) φ).Additive :=
  IsoAlgebra.additive_lift_mapOfNatIso (P := WeilComplex.objectProperty k₀ l X)
    (Q := WeilComplex.objectProperty k₀ l Y) _ _

end AlgebraicGeometry
