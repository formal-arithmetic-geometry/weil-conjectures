/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ClopenScalar.ProEtaleClopenDerivedScalarData
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # The homotopy form of the scalar representative square

Source: Stacks Project, sites-cohomology.tex, Tag 06YY.
(blueprint: lem-pur-clopen-scalar-homotopy-representative)
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules.SuccessiveDerivedQuotient
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.modulesAbelian
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.hasDerived
attribute [local irreducible] DerivedCategory.Q Functor.mapDerivedCategory
  Functor.mapDerivedCategoryFactors HasDerivedCategory.standard DerivedCategory.Qh
  DerivedCategory.quotientCompQhIso Functor.mapDerivedCategoryFactorsh
  Functor.mapHomotopyCategoryFactors SheafOfModules.monoidalCategory
namespace AlgebraicGeometry.Scheme.ProEt.ClopenScalar

section QuotientFormulas

variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C] [HasDerivedCategory D]

omit [HasDerivedCategory A] [HasDerivedCategory B] in
private theorem homotopyFactors_hom (F : A ⥤ B) [F.Additive]
    (P : CochainComplex A ℤ) :
    (F.mapHomotopyCategoryFactors (.up ℤ)).hom.app P = 𝟙 _ := by
  unfold Functor.mapHomotopyCategoryFactors
  rfl

omit [HasDerivedCategory A] [HasDerivedCategory B] in
private theorem homotopyFactors_inv (F : A ⥤ B) [F.Additive]
    (P : CochainComplex A ℤ) :
    (F.mapHomotopyCategoryFactors (.up ℤ)).inv.app P = 𝟙 _ := by
  unfold Functor.mapHomotopyCategoryFactors
  rfl

private theorem factorsh_quotient (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (P : CochainComplex A ℤ) :
    F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ _).obj P) =
      F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso A).hom.app P) ≫
        F.mapDerivedCategoryFactors.hom.app P ≫
        (DerivedCategory.quotientCompQhIso B).inv.app
          ((F.mapHomologicalComplex (.up ℤ)).obj P) := by
  rw [F.mapDerivedCategoryFactorsh_hom_app, homotopyFactors_inv]
  dsimp only [Functor.comp_obj, Functor.mapHomotopyCategory_obj,
    HomotopyCategory.quotient_obj_as]
  rw [DerivedCategory.Qh.map_id, Category.comp_id]

/-- The canonical cochain computation associated to a homotopy computation counit.
Source: Stacks 06YY, cochain/homotopy quotient comparison
(blueprint: lem-pur-clopen-scalar-homotopy-representative). -/
def cochainComputation (E : A ⥤ B) [E.Additive]
    (T : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Qh ⋙ T ⟶ E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (P : CochainComplex A ℤ) :
    T.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((E.mapHomologicalComplex (.up ℤ)).obj P) :=
  T.map ((DerivedCategory.quotientCompQhIso A).inv.app P) ≫
    ε.app ((HomotopyCategory.quotient _ _).obj P) ≫
    DerivedCategory.Qh.map ((E.mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
    (DerivedCategory.quotientCompQhIso B).hom.app
      ((E.mapHomologicalComplex (.up ℤ)).obj P)

private theorem computation_eq (E : A ⥤ B) [E.Additive]
    (T : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Qh ⋙ T ⟶ E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (P : CochainComplex A ℤ) :
    cochainComputation E T ε P =
      T.map ((DerivedCategory.quotientCompQhIso A).inv.app P) ≫
        ε.app ((HomotopyCategory.quotient _ _).obj P) ≫
        (DerivedCategory.quotientCompQhIso B).hom.app
          ((E.mapHomologicalComplex (.up ℤ)).obj P) := by
  rw [cochainComputation, homotopyFactors_hom]
  dsimp only [Functor.comp_obj, Functor.mapHomotopyCategory_obj,
    HomotopyCategory.quotient_obj_as]
  rw [DerivedCategory.Qh.map_id, Category.id_comp]

set_option maxHeartbeats 800000 in
-- The quotient square has several dependent localization and coefficient functor types.
/-- Convert the cochain representative square to its homotopy quotient square, independently
of the coefficient model. In the current purity route the four abelian categories may be
module objects for condensed coefficients; scalar extension and exact clopen restriction
supply the functors below. Only the representative equation at the input complex is needed.
Source: Stacks Project, sites-cohomology.tex, Tag 06YY
(blueprint: lem-pur-clopen-scalar-homotopy-representative).

Proof: the homotopy lift of the ordinary comparison is the quotient of its degreewise
cochain lift. Expand the exact-functor homotopy factorization and both cochain computations.
Precompose with the restricted derived image of the inverse source quotient comparison and
postcompose with the target quotient comparison. Naturality of the derived comparison and
of the quotient comparison turns the equation into the assumed cochain square. Cancel the
added isomorphisms. This uses no flatness, boundedness, nonzero, or geometric hypothesis. -/
theorem clopen_scalar_homotopy_representative
    (L : A ⥤ C) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (N : B ⥤ D) [N.Additive] [PreservesFiniteLimits N] [PreservesFiniteColimits N]
    (E : A ⥤ B) [E.Additive] (F : C ⥤ D) [F.Additive]
    (T : DerivedCategory A ⥤ DerivedCategory B)
    (U : DerivedCategory C ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ T ⟶ E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (δ : DerivedCategory.Qh ⋙ U ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (c : E ⋙ N ≅ L ⋙ F) (e : T ⋙ N.mapDerivedCategory ≅ L.mapDerivedCategory ⋙ U)
    (P : CochainComplex A ℤ)
    (hr : e.hom.app (DerivedCategory.Q.obj P) ≫
        U.map (L.mapDerivedCategoryFactors.hom.app P) ≫
        cochainComputation F U δ ((L.mapHomologicalComplex (.up ℤ)).obj P) =
      N.mapDerivedCategory.map (cochainComputation E T ε P) ≫
        N.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex c (.up ℤ)).hom.app P)) :
    N.mapDerivedCategory.map (ε.app ((HomotopyCategory.quotient _ _).obj P)) ≫
        N.mapDerivedCategoryFactorsh.hom.app
          ((E.mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj P)) ≫
        DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso c (.up ℤ) ≪≫
            (Functor.mapHomotopyCategoryCompIso (Iso.refl _) (.up ℤ)).symm).hom.app
              ((HomotopyCategory.quotient _ _).obj P)) =
      e.hom.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P)) ≫
        U.map (L.mapDerivedCategoryFactorsh.hom.app
          ((HomotopyCategory.quotient _ _).obj P)) ≫
        δ.app ((L.mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient _ _).obj P)) := by
  have hh : (Functor.mapHomotopyCategoryCompIso c (.up ℤ) ≪≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl _) (.up ℤ)).symm).hom.app
      ((HomotopyCategory.quotient _ _).obj P) =
      (HomotopyCategory.quotient _ _).map
        ((NatIso.mapHomologicalComplex c (.up ℤ)).hom.app P) := by
    change (HomotopyCategory.quotient D (.up ℤ)).map
        ((NatIso.mapHomologicalComplex c (.up ℤ)).hom.app P) ≫
      (HomotopyCategory.quotient D (.up ℤ)).map (𝟙 _) = _
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
  rw [hh]
  erw [factorsh_quotient N ((E.mapHomologicalComplex (.up ℤ)).obj P),
    factorsh_quotient L P]
  apply (cancel_epi (N.mapDerivedCategory.map (T.map
    ((DerivedCategory.quotientCompQhIso A).inv.app P)))).1
  apply (cancel_mono ((DerivedCategory.quotientCompQhIso D).hom.app
    ((F.mapHomologicalComplex (.up ℤ)).obj
      ((L.mapHomologicalComplex (.up ℤ)).obj P)))).1
  have hn := e.hom.naturality ((DerivedCategory.quotientCompQhIso A).inv.app P)
  simp only [Functor.comp_map] at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn]
  erw [DerivedCategory.quotientCompQhIso_hom_naturality
    ((NatIso.mapHomologicalComplex c (.up ℤ)).hom.app P)]
  erw [Iso.inv_hom_id_app_assoc]
  have hcancel := (U.mapIso
    (L.mapDerivedCategory.mapIso ((DerivedCategory.quotientCompQhIso A).app P))).inv_hom_id
  erw [reassoc_of% hcancel]
  simp only [computation_eq, Functor.map_comp, Category.assoc] at hr
  exact hr.symm

end QuotientFormulas

attribute [local irreducible] computation

end AlgebraicGeometry.Scheme.ProEt.ClopenScalar
