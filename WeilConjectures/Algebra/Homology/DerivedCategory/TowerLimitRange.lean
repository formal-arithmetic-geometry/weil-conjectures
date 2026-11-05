/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
public import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Tower

/-!
# Cohomological range of homotopy limits of towers
-/

@[expose] public section

open CategoryTheory Category Limits Opposite Pretriangulated

namespace CategoryTheory.ShortComplex

variable {C : Type*} [Category* C] [Abelian C] {J : Type*} [Category* J]
  [HasLimitsOfShape J C] [HasExactLimitsOfShape J C]

/-- If limits of shape `J` are exact, the homology of short complexes commutes with limits of
shape `J`. -/
instance preservesLimitsOfShape_homologyFunctor :
    PreservesLimitsOfShape J (homologyFunctor C) where
  preservesLimit {F} := by
    let S := (functorEquivalence J C).inverse.obj F
    let τ (j : J) : (lim : (J ⥤ C) ⥤ C) ⟶ (evaluation J C).obj j :=
      { app G := limit.π G j }
    have hτ (j : J) : homologyMap ((limitCone F).π.app j) =
        (S.mapHomologyIso lim).hom ≫ limit.π S.homology j ≫
          (S.mapHomologyIso ((evaluation J C).obj j)).inv := by
      refine Eq.trans ?_ (congrArg (fun x ↦ (S.mapHomologyIso lim).hom ≫ x ≫
        (S.mapHomologyIso ((evaluation J C).obj j)).inv) (NatTrans.app_homology (τ j) S)).symm
      simp only [Iso.hom_inv_id_assoc, assoc, Iso.hom_inv_id, comp_id]
      rfl
    let e : S.homology ≅ F ⋙ homologyFunctor C :=
      NatIso.ofComponents (fun j ↦ (S.mapHomologyIso ((evaluation J C).obj j)).symm)
        (fun {j j'} f ↦ by
          have h := NatTrans.app_homology ((evaluation J C).map f) S
          dsimp at h ⊢
          rw [h]
          simp only [assoc, Iso.hom_inv_id, comp_id]
          rfl)
    refine preservesLimit_of_preserves_limit_cone (isLimitLimitCone F)
      (IsLimit.ofIsoLimit ((IsLimit.postcomposeHomEquiv e _).symm (limit.isLimit _))
        (Cone.ext (S.mapHomologyIso lim).symm fun j ↦ ?_))
    simp only [Functor.mapCone_π_app, homologyFunctor_map, hτ, Iso.symm_hom,
      Iso.inv_hom_id_assoc]
    rfl

end CategoryTheory.ShortComplex

namespace DerivedCategory

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  [Abelian.HasKInjectiveResolutions C]

/-- If products of shape `J` are exact, the cohomology functors of the derived category commute
with products of shape `J`: products in `D(C)` are computed termwise on complexes. -/
instance preservesLimitsOfShape_discrete_homologyFunctor (J : Type*)
    [HasLimitsOfShape (Discrete J) C] [HasExactLimitsOfShape (Discrete J) C] (n : ℤ) :
    PreservesLimitsOfShape (Discrete J) (homologyFunctor C n) where
  preservesLimit {G} := by
    let K : Discrete J ⥤ CochainComplex C ℤ :=
      Discrete.functor fun j ↦ Q.objPreimage (G.obj ⟨j⟩)
    let e : K ⋙ Q ≅ G := Discrete.natIso fun j ↦ Q.objObjPreimageIso (G.obj j)
    have : PreservesLimit K (Q ⋙ homologyFunctor C n) :=
      preservesLimit_of_natIso _ (homologyFunctorFactors C n).symm
    have : PreservesLimit (K ⋙ Q) (homologyFunctor C n) :=
      preservesLimit_of_preserves_limit_cone (isLimitOfPreserves Q (limit.isLimit K))
        (isLimitOfPreserves (Q ⋙ homologyFunctor C n) (limit.isLimit K))
    exact preservesLimit_of_iso_diagram _ e

variable [HasLimitsOfShape (Discrete ℕ) C] [HasExactLimitsOfShape (Discrete ℕ) C]
  {F : ℕᵒᵖ ⥤ DerivedCategory C} {c : Cone F}

end DerivedCategory
