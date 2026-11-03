/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCoefficientArrows
public import WeilConjectures.CategoryTheory.Exact.ExactDegreeZeroAdjoint

/-! # Adjunction insertion for the scalar single map

Source: smooth-purity reduction compatibilities (3), root-line normalization.
(blueprint: lem-pur-scalar-single-map-adjoint-insertion).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local instance 10000] SheafExactDegreeZero.scalarWeakSheafify
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.mapDerivedCategory
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

private theorem single_adjunct
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (S : C ⥤ D) (R : D ⥤ C) (Q : E ⥤ F) (V : F ⥤ E)
    (i : C ⥤ E) (j : D ⥤ F) (a : S ⊣ R) (b : Q ⊣ V)
    (c : j ⋙ V ≅ R ⋙ i) (M : C) (P : D) (g : S.obj M ⟶ P) :
    AlgebraicGeometry.Etale.purityAdjunctionSingleMap
        S R Q V i j a b c M ≫ j.map g =
      (b.homEquiv _ _).symm (i.map (a.homEquiv _ _ g) ≫ c.inv.app P) := by
  unfold AlgebraicGeometry.Etale.purityAdjunctionSingleMap
  rw [← b.homEquiv_naturality_right_symm]
  congr 1
  rw [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  simpa only [Functor.comp_map, Category.assoc] using
    congrArg (i.map (a.unit.app M) ≫ ·) (c.inv.naturality g).symm

private theorem single_insertion_abstract
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (E : C ⥤ D) (U : D ⥤ C) [E.Additive] [U.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (a : E ⊣ U) {L : DerivedCategory C ⥤ DerivedCategory D}
    (ad : L ⊣ U.mapDerivedCategory) (M : C) (P : D) (g : E.obj M ⟶ P) :
    AlgebraicGeometry.Etale.purityAdjunctionSingleMap E U L
        U.mapDerivedCategory (DerivedCategory.singleFunctor C 0)
        (DerivedCategory.singleFunctor D 0) a ad (U.mapDerivedCategorySingleFunctor 0) M ≫
      (DerivedCategory.singleFunctor D 0).map g =
    SheafExactDegreeZero.adjointInsertion U ad (a.homEquiv _ _ g) := by
  unfold SheafExactDegreeZero.adjointInsertion
  exact single_adjunct _ _ _ _ _ _ _ _ _ _ _ _

/-- Scalar extension on a single sheaf followed by a single morphism is the
exact adjunction insertion of its ordinary adjunct.
Source: Stacks 06YY; naturality of the exact restriction/single comparison.
(blueprint: lem-pur-scalar-single-map-adjoint-insertion).
Proof: move the single morphism through the derived adjunction Hom equivalence.
Expand the ordinary adjunct as unit followed by restriction of that morphism.
Naturality of the exact-single comparison identifies the transposes. -/
theorem scalarSingleMap_eq_scalarInsertion
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (phi : A →+* B) (T : Scheme.{u})
    (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (P : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B))
    (g : (ProEtale.etaleSheafExtendScalars phi T).obj M ⟶ P) :
    scalarSingleMap phi T M ≫ (DerivedCategory.singleFunctor _ 0).map g =
    SheafExactDegreeZero.scalarAdjointInsertion T.smallEtaleTopology phi
      ((ProEtale.etaleSheafExtendScalarsAdjunction phi T).homEquiv _ _ g) := by
  unfold SheafExactDegreeZero.scalarAdjointInsertion
  exact single_insertion_abstract
    (ProEtale.etaleSheafExtendScalars phi T)
    (Sheaf.restrictScalars T.smallEtaleTopology phi)
    (ProEtale.etaleSheafExtendScalarsAdjunction phi T)
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars T.smallEtaleTopology phi))
    M P g

end AlgebraicGeometry.Etale.FiniteSmoothPurity
