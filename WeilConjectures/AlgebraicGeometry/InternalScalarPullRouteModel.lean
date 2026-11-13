/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.InternalScalarTensorPullModels
import all WeilConjectures.AlgebraicGeometry.IntegralResidueScalarCounitModel
import WeilConjectures.AlgebraicGeometry.InternalScalarOrdinaryTensorPullModel
import WeilConjectures.AlgebraicGeometry.InternalScalarPullTensorCounit
import all WeilConjectures.AlgebraicGeometry.InternalScalarRestrictionMateNormalization

/-! # The scalar route in the common tensor model

## References

* Stacks, Tags 06YY, 0G7E and 07A6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.QuotientChange
set_option allowUnsafeReducibility true
attribute [local reducible] D
variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']

private theorem scalar_restriction_counit (a : Λ ⟶ Λ') [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (lam : D a Y ⋙ L Λ' f ≅ L Λ f ⋙ D a X)
    (hlam : PullNormalized a f lam)
    (P : HomotopyCategory (Modules Λ Y) (.up ℤ)) :
    let FP := ((CondensedRing.upperStar Λ f).mapHomotopyCategory (.up ℤ)).obj P
    let TP := ((extension a Y).mapHomotopyCategory (.up ℤ)).obj P
    let ph := (NatTrans.mapHomotopyCategory (CondensedRing.pullIso a f).inv (.up ℤ)).app P
    let qh := (NatTrans.mapHomotopyCategory
      (CondensedRing.comapUpperStarIso a f).inv (.up ℤ)).app TP
    (scalarTensorRestrictPullIso a f).hom.app ((D a Y).obj (DerivedCategory.Qh.obj P)) ≫
      (V a X).map (lam.hom.app (DerivedCategory.Qh.obj P)) ≫
      (V a X).map ((D a X).map ((pullCounit (Λ := Λ) f).app P)) ≫
      (V a X).map ((scalarCounit a X).app FP) ≫
      (V₀ a X).mapDerivedCategoryFactorsh.hom.app
        (((extension a X).mapHomotopyCategory (.up ℤ)).obj FP) =
    (L Λ f).map ((V a Y).map ((scalarCounit a Y).app P) ≫
      (V₀ a Y).mapDerivedCategoryFactorsh.hom.app TP) ≫
      (pullCounit (Λ := Λ) f).app (((V₀ a Y).mapHomotopyCategory (.up ℤ)).obj TP) ≫
      DerivedCategory.Qh.map (qh ≫ ((V₀ a X).mapHomotopyCategory (.up ℤ)).map ph) := by
  dsimp only
  have hmi := hlam P
  simp only [Functor.mapHomotopyCategoryCompIso_refl_hom_app, map_comp_iso_eq,
    Iso.symm_hom] at hmi
  erw [DerivedCategory.Qh.map_id, Category.comp_id] at hmi
  have ho := (V₀ a X).mapDerivedCategoryFactorsh.hom.naturality
    ((NatTrans.mapHomotopyCategory (CondensedRing.pullIso a f).inv (.up ℤ)).app P)
  have hq := restriction_pull_fac a f
    (((extension a Y).mapHomotopyCategory (.up ℤ)).obj P)
  change (scalarTensorRestrictPullIso a f).hom.app _ ≫ _ ≫ _ = _ at hq
  have hn := (scalarTensorRestrictPullIso a f).hom.naturality
    ((scalarCounit a Y).app P)
  dsimp only [Functor.comp_map] at hn ho
  simp only [← Functor.map_comp_assoc]
  rw [hmi]
  simp only [Functor.map_comp, Category.assoc]
  erw [ho]
  erw [← reassoc_of% hn]
  erw [reassoc_of% hq]

set_option maxHeartbeats 500000 in
-- The counit calculation contains several nested derived functor comparisons.
/-- The scalar route computes the ordinary balanced pullback map
(Stacks, Tags 06YY, 0G7E and 07A6). -/
theorem scalar_pull_route_model (a : Λ ⟶ Λ') [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (tX : TensorNormalization a X)
    (lam : D a Y ⋙ L Λ' f ≅ L Λ f ⋙ D a X)
    (hX : TensorNormalized a X tX) (hlam : PullNormalized a f lam)
    (P : HomotopyCategory (Modules Λ Y) (.up ℤ)) :
    (scalarTensorRestrictPullIso a f).hom.app ((D a Y).obj (DerivedCategory.Qh.obj P)) ≫
        (V a X).map (lam.hom.app (DerivedCategory.Qh.obj P)) ≫
        tX.derived.hom.app ((L Λ f).obj (DerivedCategory.Qh.obj P)) ≫
        scalarTensorPullModelTarget a f P = scalarTensorPullModelMap a f P := by
  rw [scalar_pull_tensor_counit a f tX hX P]
  have h := scalar_restriction_counit a f lam hlam P
  have ho := scalar_ordinary_tensor_pull_model a f P
  unfold scalarTensorPullModelMap Functor.tensorModelMapWith
  erw [IntegralResidueScalarCounitModel.tensorPresentation_app (coefficientMap a Y) P]
  simp only [Functor.map_comp]
  dsimp only at h ho
  erw [reassoc_of% h]
  simp only [← DerivedCategory.Qh.map_comp, Category.assoc]
  have ho' := congrArg DerivedCategory.Qh.map ho
  erw [ho']
  have hn := (pullCounit (Λ := Λ) f).naturality
    ((Mod.tensorPresentationHomotopyIso (coefficientMap a Y)).hom.app P)
  dsimp only [Functor.comp_map] at hn
  simp only [Functor.map_comp, Category.assoc]
  erw [← reassoc_of% hn]
  unfold scalarCounit
  dsimp only [id]

end AlgebraicGeometry.ProEtale.QuotientChange
