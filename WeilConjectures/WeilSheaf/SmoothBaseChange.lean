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
that it is an isomorphism when the square is cartesian and `π` is smooth
(`AlgebraicGeometry.WeilComplex.isIso_baseChange_of_smooth`).

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

variable (k₀ l) in
/-- The exchange isomorphism `g'^* π^* ≅ π'^* g^*` of pullbacks of Weil complexes along a
commutative square `g' ≫ π = π' ≫ g`. -/
noncomputable def upperStarCompUpperStarIso (h : g' ≫ π = π' ≫ g) :
    upperStar π ⋙ upperStar g' ≅ upperStar (k₀ := k₀) (l := l) g ⋙ upperStar π' :=
  (upperStarCompIso g' π).symm ≪≫ upperStarCongrIso h ≪≫ upperStarCompIso π' g

variable [QuasiCompact g] [QuasiSeparated g] [LocallyOfFiniteType g]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] [QuasiCompact g'] [QuasiSeparated g']
  [LocallyOfFiniteType g'] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]

variable (k₀ l) in
/-- The base change morphism `π^* Rg_* ⟶ Rg'_* π'^*` of Weil complexes along a commutative square
`g' ≫ π = π' ≫ g`: the mate of the exchange isomorphism `g'^* π^* ≅ π'^* g^*`
(`AlgebraicGeometry.WeilComplex.upperStarCompUpperStarIso`). -/
noncomputable def baseChange (h : g' ≫ π = π' ≫ g) :
    derivedLowerStar g ⋙ upperStar π ⟶ upperStar π' ⋙ derivedLowerStar (k₀ := k₀) (l := l) g' :=
  mateEquiv (upperStarDerivedLowerStarAdjunction g) (upperStarDerivedLowerStarAdjunction g')
    (upperStarCompUpperStarIso k₀ l h).hom

/-- Blueprint `sbc-thm-smooth-base-change` (Weil form): **smooth base change for Weil
complexes**. For a cartesian square of `k₀`-schemes `g' ≫ π = π' ≫ g` with `π` smooth and `g`
quasi-compact, quasi-separated and of finite type, the base change morphism
`π^* Rg_* ⟶ Rg'_* π'^*` of Weil complexes is an isomorphism.

On the geometric fibres and with `ℚ̄_ℓ`-coefficients in the condensed model this is
`ProEtale.CondensedRing.isIso_baseChangeMap_app_leftDerivedUpperStar_padicAlgCl_of_smooth`.
Its passage to Weil complexes (the comparison of the condensed model with `ℓ`-adic pro-étale
sheaves, of the two base change morphisms, and the compatibility with the Frobenius structures)
belongs to the chapter on smooth base change and is not formalized; it is stated here with
`sorry`. -/
theorem isIso_baseChange_of_smooth (h : IsPullback g' π' π g) [Smooth π] :
    IsIso (baseChange k₀ l h.w) :=
  sorry

/-- If the base change morphism `π^* Rg_* M ⟶ Rg'_* π'^* M` is invertible and the unit
`M ⟶ Rπ'_* π'^* M` is invertible, then so is the unit `Rg_* M ⟶ Rπ_* π^* Rg_* M`. -/
theorem isIso_unit_app_derivedLowerStar_obj_of_isIso_baseChange_app (h : g' ≫ π = π' ≫ g)
    [QuasiCompact π] [QuasiSeparated π] [LocallyOfFiniteType π] [QuasiCompact π']
    [QuasiSeparated π'] [LocallyOfFiniteType π']
    [LocallyOfFiniteType (X' ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X' ↘ Spec (CommRingCat.of k₀))] (M : WeilComplex k₀ l X')
    [IsIso ((baseChange k₀ l h).app M)]
    [IsIso ((upperStarDerivedLowerStarAdjunction (k₀ := k₀) (l := l) π').unit.app M)] :
    IsIso ((upperStarDerivedLowerStarAdjunction (k₀ := k₀) (l := l) π).unit.app
      ((derivedLowerStar g).obj M)) :=
  have : IsIso ((mateEquiv (upperStarDerivedLowerStarAdjunction g)
      (upperStarDerivedLowerStarAdjunction g') (upperStarCompUpperStarIso k₀ l h).hom).app M) :=
    inferInstanceAs (IsIso ((baseChange k₀ l h).app M))
  isIso_unit_app_of_isIso_mateEquiv_app (upperStarDerivedLowerStarAdjunction g)
    (upperStarDerivedLowerStarAdjunction g') (upperStarDerivedLowerStarAdjunction π)
    (upperStarDerivedLowerStarAdjunction π') (upperStarCompUpperStarIso k₀ l h).hom M

end AlgebraicGeometry.WeilComplex
