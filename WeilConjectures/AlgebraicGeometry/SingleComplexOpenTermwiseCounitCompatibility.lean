/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenTensorRestrictionIso
import WeilConjectures.AlgebraicGeometry.OpenPinnedCounitHomotopyRestriction
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization

/-! # Compatibility of open restriction with the pinned pullback counits

## References

* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 08FE](https://stacks.math.columbia.edu/tag/08FE)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 0DJ9](https://stacks.math.columbia.edu/tag/0DJ9)
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace AlgebraicGeometry
open SingleComplexBaseChange
set_option synthInstance.maxSize 2048
attribute [local instance_reducible] Scheme.Modules TopCat.Sheaf
attribute [local implicit_reducible] DerivedCategory HomotopyCategory
  DerivedCategory.Q DerivedCategory.Qh

private theorem cancel_counit_factors
    {C : Type*} [Category C] {A B D E F G : C}
    (a : A ≅ B) (t : A ⟶ D) (e : D ⟶ E) (b : E ≅ F) (c : F ≅ G)
    (d : B ⟶ G) (h : t ≫ e ≫ b.hom ≫ c.hom = a.hom ≫ d) :
    a.inv ≫ t ≫ e = d ≫ c.inv ≫ b.inv := by
  have h' := congrArg (fun k => a.inv ≫ k ≫ c.inv ≫ b.inv) h
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id, Category.id_comp, Category.comp_id] using h'

private theorem termwise_exact_factors
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (P : CochainComplex C ℤ) :
    F.mapDerivedCategoryFactorsh.app ((HomotopyCategory.quotient C (.up ℤ)).obj P) =
      F.mapDerivedCategoryFactors.app P := by
  apply Iso.ext
  change F.mapDerivedCategoryFactorsh.hom.app
    ((HomotopyCategory.quotient C (.up ℤ)).obj P) = F.mapDerivedCategoryFactors.hom.app P
  rw [Functor.mapDerivedCategoryFactorsh_hom_app]
  change F.mapDerivedCategory.map (𝟙 _) ≫ F.mapDerivedCategoryFactors.hom.app P ≫
    𝟙 _ ≫ DerivedCategory.Qh.map (𝟙 _) = _
  erw [F.mapDerivedCategory.map_id, DerivedCategory.Qh.map_id]
  simp only [Category.id_comp]
  exact Category.comp_id _

@[reassoc] private theorem termwise_counit_transport
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
    (F : C ⥤ D) [F.Additive] (L : DerivedCategory C ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ L ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (P : CochainComplex C ℤ) :
    L.map ((DerivedCategory.quotientCompQhIso C).inv.app P) ≫
      ε.app ((HomotopyCategory.quotient C (.up ℤ)).obj P) ≫
      DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
      (DerivedCategory.quotientCompQhIso D).hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj P) =
      ε.app ((HomotopyCategory.quotient C (.up ℤ)).obj P) := by
  change L.map (𝟙 _) ≫ ε.app _ ≫ DerivedCategory.Qh.map (𝟙 _) ≫ 𝟙 _ = _
  erw [L.map_id, DerivedCategory.Qh.map_id]
  change 𝟙 _ ≫ ε.app ((HomotopyCategory.quotient C (.up ℤ)).obj P) ≫ 𝟙 _ ≫ 𝟙 _ = _
  simp only [Category.id_comp, Category.comp_id]

private theorem termwise_homotopy_square_inv
    {C D B E : Type*} [Category C] [Category D] [Category B] [Category E]
    [Preadditive C] [Preadditive D] [Preadditive B] [Abelian E]
    [HasDerivedCategory.{w} E]
    {F : C ⥤ D} {G : D ⥤ E} {R : C ⥤ B} {J : B ⥤ E}
    [F.Additive] [G.Additive] [R.Additive] [J.Additive]
    (e : F ⋙ G ≅ R ⋙ J) (P : CochainComplex C ℤ) :
    DerivedCategory.Qh.map
      ((Functor.mapHomotopyCategoryCompIso e (.up ℤ) ≪≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (R ⋙ J)) (.up ℤ)).symm).inv.app
          ((HomotopyCategory.quotient C (.up ℤ)).obj P)) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.inv (.up ℤ)).app P) := by
  change DerivedCategory.Qh.map
    ((Functor.mapHomotopyCategoryCompIso (Iso.refl (R ⋙ J)) (.up ℤ)).hom.app _ ≫
      (Functor.mapHomotopyCategoryCompIso e (.up ℤ)).inv.app _) = _
  rw [Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.id_comp]
  rfl

set_option maxHeartbeats 600000 in
-- Reusing the abstract exact-factor normalization keeps the proof within the original budget.
/-- The derived open coefficient on an actual restricted complex is compatible
with ordinary tensor pullback and the pinned counits. This is an equality before
stalks and cohomology; it needs neither a base-change square nor K-flatness. -/
theorem singleComplexOpen_termwise_counit_compatibility
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' : Scheme.{u}} (g' : X' ⟶ X)
    (U : X.Opens) (U' : X'.Opens) (j : U'.toScheme ⟶ U.toScheme)
    (hj : j ≫ U.ι = U'.ι ≫ g')
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    letI : (schemeOpenRestriction X U).Additive := schemeOpenRestriction_additive X U
    letI : (schemeOpenRestriction X' U').Additive := schemeOpenRestriction_additive X' U'
    let K := DerivedCategory.Q.obj P
    let Q := ((schemeOpenRestriction X U).mapHomologicalComplex (.up ℤ)).obj P
    let a := (schemeOpenRestriction X U).mapDerivedCategoryFactors.symm.app P
    let θ := singleComplexRestrictedCoefficient g' K ((derivedPullback g').obj K) (𝟙 _)
      U U' j hj
    (derivedPullback j).map a.hom ≫ θ ≫
        (schemeOpenRestriction X' U').mapDerivedCategory.map
          ((derivedPullback g').map ((DerivedCategory.quotientCompQhIso _).inv.app P) ≫
            (counit g').app ((HomotopyCategory.quotient
              (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)).obj P) ≫
            DerivedCategory.Qh.map
              (((Scheme.Modules.tensorPullback g').mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
            (DerivedCategory.quotientCompQhIso
              (SheafOfModules.{u} (moduleRings X'.toRingedSpace))).hom.app
              (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P)) =
      (derivedPullback j).map ((DerivedCategory.quotientCompQhIso _).inv.app Q) ≫
        (counit j).app ((HomotopyCategory.quotient _ (.up ℤ)).obj Q) ≫
        DerivedCategory.Qh.map
          (((Scheme.Modules.tensorPullback j).mapHomotopyCategoryFactors (.up ℤ)).hom.app Q) ≫
        (DerivedCategory.quotientCompQhIso
          (SheafOfModules.{u} (moduleRings U'.toScheme.toRingedSpace))).hom.app
          (((Scheme.Modules.tensorPullback j).mapHomologicalComplex (.up ℤ)).obj Q) ≫
        singleComplexOpenTensorRestrictionMap g' U U' j hj P := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  have : ∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z),
      (Scheme.Modules.tensorPullback k).Additive := fun k => tensorPullbackAdditive k
  let := schemeOpenRestriction_additive X U
  let := schemeOpenRestriction_additive X' U'
  let := tensorPullbackAdditive g'
  let := tensorPullbackAdditive j
  let : (schemeOpenRestriction X U ⋙ Scheme.Modules.tensorPullback j).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  let : (Scheme.Modules.tensorPullback g' ⋙ schemeOpenRestriction X' U').PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  have h := open_pinned_counit_homotopy_restriction g' U U' j hj
    ((HomotopyCategory.quotient
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)).obj P)
  dsimp only [singleComplexOpenTensorRestrictionMap]
  erw [termwise_counit_transport (Scheme.Modules.tensorPullback g')
    (derivedPullback g') (counit g') P,
    termwise_counit_transport_assoc (Scheme.Modules.tensorPullback j)
      (derivedPullback j) (counit j)
      (((schemeOpenRestriction X U).mapHomologicalComplex (.up ℤ)).obj P)]
  have hf : (schemeOpenRestriction X U).mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)).obj P) =
      (schemeOpenRestriction X U).mapDerivedCategoryFactors.hom.app P := by
    exact congrArg Iso.hom (termwise_exact_factors (schemeOpenRestriction X U) P)
  rw [hf] at h
  have h' := cancel_counit_factors
    ((derivedPullback j).mapIso ((schemeOpenRestriction X U).mapDerivedCategoryFactors.app P))
    (singleComplexRestrictedCoefficient g' (DerivedCategory.Q.obj P)
      ((derivedPullback g').obj (DerivedCategory.Q.obj P)) (𝟙 _) U U' j hj)
    ((schemeOpenRestriction X' U').mapDerivedCategory.map
      ((counit g').app ((HomotopyCategory.quotient
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)).obj P)))
    ((schemeOpenRestriction X' U').mapDerivedCategoryFactorsh.app
      (((Scheme.Modules.tensorPullback g').mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)).obj P)))
    (DerivedCategory.Qh.mapIso
      ((openPinnedHomotopyTensorRestrictionIso g' U U' j hj).app
        ((HomotopyCategory.quotient
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)).obj P)))
    ((counit j).app ((HomotopyCategory.quotient _ (.up ℤ)).obj
      (((schemeOpenRestriction X U).mapHomologicalComplex (.up ℤ)).obj P)))
    (by
      change _ = _ at h
      exact h)
  have htarget := congrArg Iso.inv
    (termwise_exact_factors (schemeOpenRestriction X' U')
      (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P))
  simp only [Iso.app_inv] at htarget
  have hβ : DerivedCategory.Qh.map
      ((openPinnedHomotopyTensorRestrictionIso g' U U' j hj).inv.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (openPinnedTensorRestrictionIso g' U U' j hj).inv (.up ℤ)).app P) := by
    exact termwise_homotopy_square_inv (openPinnedTensorRestrictionIso g' U U' j hj) P
  simp only [Functor.mapIso_inv, Iso.app_inv] at h'
  exact h'.trans (congrArg₂ (fun x y =>
    (counit j).app ((HomotopyCategory.quotient _ (.up ℤ)).obj
      (((schemeOpenRestriction X U).mapHomologicalComplex (.up ℤ)).obj P)) ≫ x ≫ y)
    hβ htarget)

end AlgebraicGeometry
