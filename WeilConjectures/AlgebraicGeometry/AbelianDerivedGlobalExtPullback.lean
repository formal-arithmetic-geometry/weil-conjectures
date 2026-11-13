/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.DerivedUnitClassicalPullback
import WeilConjectures.AlgebraicGeometry.SheafHRightDerivedPullback

/-! # Ext comparison for pullback on derived global sections

Source: Stacks Project, Cohomology on Sites, Section 21.2, and Tag 01F8.
-/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry
open Scheme Etale

/-- The derived-unit pullback on global cohomology of a degree-zero abelian sheaf
agrees with the Ext definition of cohomology pullback.

Source: Stacks Project, sites-cohomology.tex, Section 21.2 (definition of cohomology)
and Tag 08J6; cohomology.tex, Tag 01F8 and equations 01F9 and 01FA. -/
theorem Etale.exists_addEquiv_derivedGlobal_ext_pullback
    {X X' : Scheme.{u}} (g' : X' ⟶ X)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    let K := (DerivedCategory.Plus.singleFunctor _ 0).obj G
    let P := (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus
    let P' := (Sheaf.Γ X'.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus
    let U := (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj (P.obj K)
    let V := (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
      (P'.obj (((g')^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlus.obj K))
    let p := (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
      (P.map ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g').derivedPlus.unit.app K) ≫
        (@Functor.rightDerivedFunctorPlusCompIso' _ _ _ _ _ _ _ _ _ _ _ _ _ _
          (lowerStar AddCommGrpCat.{u + 1} g')
          (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}) _ _ _ _
          (Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
            (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g'))
          (lowerStarCompGlobalSectionsIso AddCommGrpCat.{u + 1} g')).hom.app
            (((g')^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlus.obj K))
    ∃ (b₁ : U ≃+ Sheaf.H G q)
      (b₂ : V ≃+ Sheaf.H ((g')^*[AddCommGrpCat.{u + 1}].obj G) q),
      ∀ x, b₂ (p.hom x) = Etale.cohomologyMap g' G q (b₁ x) := by
  let Γ := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}
  let Γ' := Sheaf.Γ X'.smallEtaleTopology AddCommGrpCat.{u + 1}
  let L := upperStar AddCommGrpCat.{u + 1} g'
  let c := Γ.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso q
  let c' := Γ'.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso q
  let a := (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).mapIso
    (Γ'.rightDerivedFunctorPlus.mapIso ((L.mapDerivedCategoryPlusSingleFunctor 0).app G))
  obtain ⟨r, r', he⟩ := sheafHRightDerivedIso_pullback g' G q
  let b₁ := Iso.addCommGroupIsoToAddEquiv (c.app G ≪≫ r.symm)
  let b₂ := Iso.addCommGroupIsoToAddEquiv (a ≪≫ c'.app (L.obj G) ≪≫
    r'.symm)
  refine ⟨b₁, b₂, ?_⟩
  intro x
  have hd := derivedUnit_classicalPullback g' G q
  dsimp only at hd he
  have he' := congrArg
    (fun f ↦ r.inv ≫ f ≫
      r'.inv) he
  simp only [Category.assoc, Iso.inv_hom_id_assoc] at he'
  have hp := congrArg
    (fun f ↦ f ≫ r'.inv) hd
  simp only [Category.assoc] at hp
  rw [he'] at hp
  simp only [Iso.hom_inv_id, Category.comp_id] at hp
  convert congrArg (fun f ↦ f.hom x) hp using 1 <;> rfl

end AlgebraicGeometry
