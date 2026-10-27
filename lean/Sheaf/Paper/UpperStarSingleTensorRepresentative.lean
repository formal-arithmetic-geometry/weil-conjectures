/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q5
-/
module

public import Sheaf.Paper.ScalarPullbackRepresentativeData
public import Sheaf.Paper.ScalarSheafTensorPullback
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison

/-!
# The tensor comparison with a coefficient sheaf in degree zero

Source: Stacks Project, sites-cohomology.tex, Tags 07A4 and 0FPH
(blueprint: lem-pur-upper-star-single-tensor-representative).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.mapDerivedCategory upperStar lowerStar

/-- The canonical localization comparison for tensoring with a sheaf in degree zero.
Source: Stacks 0G7E (blueprint: lem-pur-upper-star-single-tensor-representative). -/
def tensorSingleRepresentative
    {C : Type w} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{v} C] [Abelian.HasFunctorialFlatResolution C]
    (M : C) (P : CochainComplex C ℤ) :
    (scalarTensorModelFunctor M).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj (((tensorRight M).mapHomologicalComplex (.up ℤ)).obj P) :=
  Functor.LaxMonoidal.μ DerivedCategory.Q P
      ((HomologicalComplex.single _ (.up ℤ) 0).obj M) ≫
    DerivedCategory.Q.map
      ((CochainComplex.map₂HomologicalComplexFlipObjSingleIso
        (curriedTensor _) M).hom.app P)

/-- Exact pullback on a sheaf in degree zero followed by a specified coefficient iso.
Source: Stacks 07A4 (blueprint: lem-pur-upper-star-single-tensor-representative). -/
def upperStarSingleCoefficientIso
    (A : Type (u + 1)) [CommRing A] {Z W : Scheme.{u}} (f : Z ⟶ W)
    {M : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)}
    {N : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (k : (upperStar (ModuleCat.{u + 1} A) f).obj M ≅ N) :
    L(upperStar (ModuleCat.{u + 1} A) f).obj
        ((DerivedCategory.singleFunctor _ 0).obj M) ≅
      (DerivedCategory.singleFunctor _ 0).obj N :=
  (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).app _ ≪≫
    ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategorySingleFunctor 0).app M ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso k

/-- Ordinary pullback commutes with tensoring by a sheaf, including a coefficient iso.
Source: Stacks 07A4 (blueprint: lem-pur-upper-star-single-tensor-representative). -/
def upperStarTensorSingleIso
    (A : Type (u + 1)) [CommRing A] {Z W : Scheme.{u}} (f : Z ⟶ W)
    {M : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)}
    {N : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (k : (upperStar (ModuleCat.{u + 1} A) f).obj M ≅ N) :
    tensorRight M ⋙ upperStar (ModuleCat.{u + 1} A) f ≅
      upperStar (ModuleCat.{u + 1} A) f ⋙ tensorRight N :=
  NatIso.ofComponents
    (fun X ↦ asIso (Functor.OplaxMonoidal.δ (upperStar (ModuleCat.{u + 1} A) f) X M) ≪≫
      (tensorLeft _).mapIso k)
    (by
      intro X Y a
      change (upperStar (ModuleCat.{u + 1} A) f).map (a ▷ M) ≫
          Functor.OplaxMonoidal.δ (upperStar (ModuleCat.{u + 1} A) f) Y M ≫
          ((upperStar (ModuleCat.{u + 1} A) f).obj Y ◁ k.hom) =
        (Functor.OplaxMonoidal.δ (upperStar (ModuleCat.{u + 1} A) f) X M ≫
          ((upperStar (ModuleCat.{u + 1} A) f).obj X ◁ k.hom)) ≫
          ((upperStar (ModuleCat.{u + 1} A) f).map a ▷ N)
      rw [← Functor.OplaxMonoidal.δ_natural_left_assoc, Category.assoc]
      exact congrArg (fun z ↦ Functor.OplaxMonoidal.δ
        (upperStar (ModuleCat.{u + 1} A) f) X M ≫ z)
        (whisker_exchange _ _).symm)

/-- Specializing the derived pullback tensor square to a sheaf in degree zero agrees
with the ordinary tensor square on every cochain complex.

Source: Stacks Project, sites-cohomology.tex, Tags 07A4 and 0FPH; step 2 of
lem-pur-scalar-tensor-pullback-normalization
(blueprint: lem-pur-upper-star-single-tensor-representative).

Proof: use the counit square defining leftDerivedUpperStarTensorComparison on P
and the complex concentrated in degree zero at M. The geometric counit on the
second complex equals exact inverse image on the single sheaf, by the defining
exact-derived comparison and the mapDerivedCategorySingleFunctor square. Compose
with the localization of the total-tensor/single-complex isomorphism. Its degree n
component is the degree n tensor comparison with M: only the summand (n,0) occurs,
so no permutation of degrees or sign occurs. Naturality with respect to k gives
the displayed square. No K-flat assumption is needed for this counit equation. -/
theorem upperStar_single_tensor_representative
    (A : Type (u + 1)) [CommRing A] {Z W : Scheme.{u}} (f : Z ⟶ W)
    {M : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)}
    {N : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (k : (upperStar (ModuleCat.{u + 1} A) f).obj M ≅ N)
    (P : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    ((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) f).app
          (DerivedCategory.Q.obj P)).app ((DerivedCategory.singleFunctor _ 0).obj M) ≫
        ((derivedTensor (ModuleCat.{u + 1} A) Z).obj
          (L(upperStar (ModuleCat.{u + 1} A) f).obj (DerivedCategory.Q.obj P))).map
          (upperStarSingleCoefficientIso A f k).hom ≫
        (scalarTensorModelFunctor N).map (scalarGeometricRepresentative A f P) ≫
        tensorSingleRepresentative N
          (((upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).obj P) =
      L(upperStar (ModuleCat.{u + 1} A) f).map (tensorSingleRepresentative M P) ≫
        scalarGeometricRepresentative A f
          (((tensorRight M).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso (upperStarTensorSingleIso A f k) (.up ℤ) ≪≫
            (Functor.mapHomologicalComplexCompIso (Iso.refl
              (upperStar (ModuleCat.{u + 1} A) f ⋙ tensorRight N)) (.up ℤ)).symm).hom.app P) := by
  sorry

/-- The scalar coefficient comparison is the single-sheaf comparison for its
ordinary coefficient iso. Source: Stacks 07A4
(blueprint: lem-pur-upper-star-single-tensor-representative).
Proof: both constructions apply the exact-derived and single-complex comparison,
then the single functor to the restriction/pullback iso on the unit and its unit iso. -/
theorem scalarCoefficientSinglePullbackIso_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {Z W : Scheme.{u}} (f : Z ⟶ W) :
    upperStarSingleCoefficientIso A f (scalarCoefficientSheafPullbackIso φ f) =
      scalarCoefficientPullbackIso φ f := by
  rfl


end AlgebraicGeometry.Etale
