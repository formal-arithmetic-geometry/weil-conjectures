/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NativeCompleteProjectionDescent.NativeProjectionDescentMaps
public import WeilConjectures.AlgebraicGeometry.QuotientTensorFlatModel.QuotientTensorPullCounit
public import WeilConjectures.PoincareDuality.ProperProjectionComp

/-! # The tensorator of the native derived pullback on cochain representatives

Source: Stacks Project, Tags 07A4 and 0G7E; current Weil blueprint, sec-smooth-purity,
`sk-prop-sp-integral-adjunction-direct-image.proof.md`, paragraph (3)
(blueprint: lem-sp-complete-projection-reduction-square, proof step 1).

The tensorator `δ` of `CondensedRing.monoidal_leftDerivedUpperStar` is computed by the
degreewise ordinary tensorator of the pullback, through `pullComplexComparison`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed CategoryTheory.Sheaf.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Mod.extendScalars CategoryTheory.Mod.comap
  AlgebraicGeometry.ProEtale.CondensedRing.upperStar
  AlgebraicGeometry.ProEtale.CondensedRing.monoidal_upperStar

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.NativeCompleteProjectionDescent

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The degreewise ordinary tensorator of the inverse image, on cochain complexes. -/
abbrev pullTensorChain {X Y : Scheme.{u}} (f : X ⟶ Y) (P Q : CochainComplex (Modules l E Y) ℤ) :
    ((ordinaryPull l E f).mapHomologicalComplex (.up ℤ)).obj (P ⊗ Q) ⟶
      ((ordinaryPull l E f).mapHomologicalComplex (.up ℤ)).obj P ⊗
        ((ordinaryPull l E f).mapHomologicalComplex (.up ℤ)).obj Q :=
  QuotientTensorFlatModel.totalPull f (spIntegralCondensed l E) P Q

private theorem exact_computation
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (LG : DerivedCategory C ⥤ DerivedCategory D)
    (c : DerivedCategory.Qh ⋙ LG ⟶ G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (e : LG ≅ G.mapDerivedCategory)
    (he : Functor.whiskerLeft DerivedCategory.Qh e.hom ≫
      G.mapDerivedCategoryFactorsh.hom = c) (P : CochainComplex C ℤ) :
    LG.map ((DerivedCategory.quotientCompQhIso C).inv.app P) ≫
        c.app ((HomotopyCategory.quotient _ _).obj P) ≫
        DerivedCategory.Qh.map ((G.mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
        (DerivedCategory.quotientCompQhIso D).hom.app
          ((G.mapHomologicalComplex (.up ℤ)).obj P) =
      e.hom.app (DerivedCategory.Q.obj P) ≫ G.mapDerivedCategoryFactors.hom.app P := by
  rw [← he]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.mapDerivedCategoryFactorsh_hom_app, Category.assoc]
  erw [e.hom.naturality_assoc]
  simp only [← G.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [← Category.assoc, ← DerivedCategory.Qh.map_comp,
    Iso.inv_hom_id_app]
  erw [DerivedCategory.Qh.map_id]
  simp only [DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Quotient.lift.isLift_inv, Quotient.lift.isLift_hom]
  simp only [Category.assoc]
  erw [Category.id_comp, Category.id_comp, Category.comp_id]

private theorem computePull_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (Modules l E Y) ℤ) :
    IntegralQuotient.computePull f P = (by
      unfold QuotientChange.L CondensedRing.moduleObjectDerivedPullback
      exact (pullComplexComparison l E f P).hom) := by
  unfold IntegralQuotient.computePull QuotientChange.pullCounit QuotientChange.L
    CondensedRing.moduleObjectDerivedPullback pullComplexComparison
    CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
  dsimp only [id]
  exact exact_computation _ _ _ _
    (CondensedRing.upperStar (spIntegralCondensed l E) f
      ).leftDerivedFunctorIsoMapDerivedCategory_hom_fac P

/-- The tensorator of the native derived pullback is the native tensor comparison. -/
theorem ringedPull_δ_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (A B : Integral l E Y) :
    Functor.OplaxMonoidal.δ (ringedPull l E f) A B =
      ((CondensedRing.leftDerivedUpperStarTensor (spIntegralCondensed l E) f).app A).app B :=
  CondensedRing.δ_leftDerivedUpperStar _ f A B

/-- The tensorator of the native derived pullback, computed on cochain representatives.
Source: Stacks 07A4, 0G7E
(blueprint: lem-sp-complete-projection-reduction-square, proof step 1). -/
theorem ringedPull_δ_Q {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : CochainComplex (Modules l E Y) ℤ) :
    (ringedPull l E f).map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
        (pullComplexComparison l E f (P ⊗ Q)).hom ≫
        DerivedCategory.Q.map (pullTensorChain l E f P Q) =
      Functor.OplaxMonoidal.δ (ringedPull l E f) (DerivedCategory.Q.obj P)
          (DerivedCategory.Q.obj Q) ≫
        ((pullComplexComparison l E f P).hom ⊗ₘ (pullComplexComparison l E f Q).hom) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q
          (((ordinaryPull l E f).mapHomologicalComplex (.up ℤ)).obj P)
          (((ordinaryPull l E f).mapHomologicalComplex (.up ℤ)).obj Q) := by
  have h := QuotientTensorFlatModel.pull_tensor_counit (R := spIntegralCondensed l E) f P Q
  rw [computePull_eq, computePull_eq, computePull_eq] at h
  unfold QuotientChange.L CondensedRing.moduleObjectDerivedPullback at h
  rw [ringedPull_δ_eq]
  dsimp only [id] at h
  convert h using 3

end AlgebraicGeometry.ProEtale.NativeCompleteProjectionDescent
