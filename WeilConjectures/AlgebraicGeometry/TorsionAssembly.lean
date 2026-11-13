/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.TorsionEtaleSheaf
public import WeilConjectures.SixFunctors.BaseChange.Derived
import WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine
import WeilConjectures.SixFunctors.BaseChange.DerivedForget
import WeilConjectures.SixFunctors.Etale.Gabber

/-!
# Torsion coefficient assembly for proper base change

## References

* [Stacks Project, Tag 095T](https://stacks.math.columbia.edu/tag/095T)
* [Stacks Project, Tag 0A4B](https://stacks.math.columbia.edu/tag/0A4B)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- For a cartesian square with `f` proper and arbitrary `g`, the specified derived
exchange on a torsion abelian sheaf placed in degree zero is an isomorphism, as is its
map on every cohomology sheaf. Exactness of inverse image identifies the latter map with
`g⁻¹ Rᵖf_* F → Rᵖf'_* g'⁻¹ F`; higher direct images mean cohomology of derived direct image. -/
theorem isIso_derivedBaseChangeMapPlus_torsion_assembly
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} [IsProper f] (sq : IsPullback g' f' f g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : Scheme.IsTorsionAbelianSheaf F) :
    IsIso ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app
      ((DerivedCategory.Plus.singleFunctor
        (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F)) ∧
    ∀ p : ℤ, IsIso ((DerivedCategory.Plus.homologyFunctor
      (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}) p).map
      ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app
        ((DerivedCategory.Plus.singleFunctor
          (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F))) := by
  let Φ := sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})
  let F' := Φ.objPreimage F
  let e : Φ.obj F' ≅ F := Φ.objObjPreimageIso F
  have : Scheme.IsTorsionSheaf F :=
    (Scheme.isTorsionSheaf_iff_isTorsion F).2
      ((Scheme.isTorsionAbelianSheaf_characterizations F).1.mp hF)
  have : Scheme.IsTorsionSheaf (Φ.obj F') := Scheme.IsTorsionSheaf.of_iso e.symm
  have : Scheme.IsTorsionModuleSheaf F' :=
    (Scheme.isTorsionModuleSheaf_iff_isTorsion F').2
      ((Scheme.isTorsionSheaf_iff_isTorsion (Φ.obj F')).1 inferInstance)
  let K' := (DerivedCategory.Plus.singleFunctor _ 0).obj F'
  let eK : Φ.mapDerivedCategoryPlus.obj K' ≅
      (DerivedCategory.Plus.singleFunctor _ 0).obj F :=
    (Φ.mapDerivedCategoryPlusSingleFunctor 0).app F' ≪≫
      (DerivedCategory.Plus.singleFunctor _ 0).mapIso e
  have hK' : IsIso
      ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
        sq.toCommSq).app K') :=
    hasTorsionBaseChange_of_isProper (ULift.{u + 1} ℤ) f sq K'
      (DerivedCategory.Plus.moduleTorsionHomology_singleFunctor_obj _ X F')
  have hK : IsIso ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) := by
    rw [← NatTrans.isIso_app_iff_of_iso _ eK,
      isIso_derivedBaseChangeMapPlus_app_forget₂_iff]
    exact hK'
  exact ⟨hK, fun p ↦ inferInstance⟩

end AlgebraicGeometry.Etale
