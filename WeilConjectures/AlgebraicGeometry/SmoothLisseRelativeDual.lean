/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Perfect.Dual
import WeilConjectures.CategoryTheory.Monoidal.Closed.InvertibleDualizing
import WeilConjectures.CategoryTheory.Monoidal.Dualizable
import WeilConjectures.SixFunctors.Etale.Derived.LisseFieldDual
import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion

/-! Relative coefficient-dual finiteness and biduality. -/

@[expose] public section

universe u uA

open CategoryTheory Limits Opposite MonoidalCategory MonoidalClosed
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme _root_.AlgebraicGeometry.Etale.DerivedCategory

attribute [local instance high] SymmetricCategory.toBraidedCategory in
attribute [local instance 20000] Etale.sheafBraidedCategory in
/-- Dualizability in the derived monoidal structure, at generic coefficients. -/
def smoothRelativeDualizable
    (A : Type uA) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) (N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) : Prop :=
  IsDualizable N

/-- The explicitly constructed relative internal dual. -/
@[irreducible]
noncomputable def smoothRelativeDual
    (A : Type uA) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) (K W : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    _root_.DerivedCategory (Sheaf X.smallEtaleTopology A) :=
  ((derivedHom A X).obj (op K)).obj W

/-- The relative-dual construction is the derived internal Hom. -/
theorem smoothRelativeDual_eq
    (A : Type uA) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) (K W : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    smoothRelativeDual A X K W = ((derivedHom A X).obj (op K)).obj W := by
  unfold smoothRelativeDual
  rfl

/-- The canonical relative bidual map: transpose evaluation using the braiding. -/
noncomputable def smoothRelativeBidualMap
    (A : Type uA) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) (W K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    K ⟶ ((derivedHom A X).obj (op (smoothRelativeDual A X K W))).obj W := by
  let e := eqToIso (smoothRelativeDual_eq A X K W)
  let := _root_.DerivedCategory.braidedCategory' (Sheaf X.smallEtaleTopology A)
  exact MonoidalClosed.toIhomIhom W K ≫ (((derivedHom A X).mapIso e.op).app W).hom

attribute [local instance 2000] ModuleCat.hasColimitsOfShape
  ModuleCat.hasColimitsOfSize in
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint in
/-- Relative dual of a finite local system over any finite field, against an invertible
finite-Tor coefficient. -/
theorem finiteLisseRelativeDual
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (hfield : IsField Λ) (X : Scheme.{u})
    (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hL : IsFiniteLocallyConstantSheaf L)
    (W : DerivedCategoryModule Λ X)
    (hW : DerivedCategory.isInvertible Λ X W)
    (hWc : DerivedCategory.boundedConstructibleFiniteTor
      Λ X W) :
    let K := (_root_.DerivedCategory.singleFunctor _ 0).obj L
    let N := smoothRelativeDual (ModuleCat Λ) X K W
    smoothRelativeDualizable (ModuleCat Λ) X N ∧
      DerivedCategory.boundedConstructibleFiniteTor Λ X N ∧
      IsIso (smoothRelativeBidualMap
        (ModuleCat Λ) X W K) := by
  classical
  have := hL
  let K := (_root_.DerivedCategory.singleFunctor _ 0).obj L
  have hflat := flat_of_isField hfield L
  have hLs : IsDualizable L := by
    let := exactPairingIhomUnitOfIsFiniteLocallyConstantSheaf L hflat
    exact ⟨{ rightDual := (ihom L).obj (𝟙_ _)
             exact := BraidedCategory.exactPairing_swap _ _ }⟩
  have hK : IsDualizable K := by
    let Q := (HomologicalComplex.single (Sheaf X.smallEtaleTopology (ModuleCat Λ))
      (ComplexShape.up ℤ) 0).obj L
    have hQ (n : ℤ) : IsDualizable (Q.X n) := by
      by_cases hn : n = 0
      · exact hLs.of_iso (HomologicalComplex.singleObjXIsoOfEq _ 0 L n hn).symm
      · exact CategoryTheory.IsZero.isDualizable
          (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn)
    exact (_root_.DerivedCategory.isDualizable_Q_obj Q 0 0 hQ).of_iso
      ((_root_.DerivedCategory.singleFunctorIsoCompQ _ 0).app L).symm
  let := _root_.DerivedCategory.braidedCategory' (Sheaf X.smallEtaleTopology (ModuleCat Λ))
  have hWi : IsInvertible W := hW
  have hN : IsDualizable (smoothRelativeDual (ModuleCat Λ) X K W) := by
    rw [smoothRelativeDual_eq]
    exact MonoidalClosed.isDualizable_ihom_obj (Iso.refl W) hWi hK
  have hbi : IsIso (smoothRelativeBidualMap (ModuleCat Λ) X W K) := by
    unfold smoothRelativeBidualMap
    have := MonoidalClosed.isIso_toIhomIhom_of_isDualizable (Iso.refl W) hWi hK
    infer_instance
  have hdualSheaf : IsFiniteLocallyConstantSheaf ((ihom L).obj (𝟙_ _)) :=
    isFiniteLocallyConstantSheaf_ihom_unit_of_flat L hflat
  have : IsConstructibleSheaf ((ihom L).obj (𝟙_ _)) :=
    IsFiniteLocallyConstantSheaf.isConstructibleSheaf hdualSheaf
  obtain ⟨⟨eD⟩, -⟩ := dual_singleFunctor
    (dualizableSheafClass_isFiniteLocallyConstantSheaf hfield) L hL 0
  have hDc : DerivedCategory.boundedConstructibleFiniteTor Λ X
      ((_root_.DerivedCategory.singleFunctor _ 0).obj ((ihom L).obj (𝟙_ _))) :=
    ⟨DerivedCategory.boundedConstructible_singleFunctor_obj _ 0,
      ⟨0, 0, _root_.DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat
        (flat_of_isField hfield _)⟩⟩
  have hDc' : DerivedCategory.boundedConstructibleFiniteTor Λ X
      ((DerivedCategory.coefficientDual (ModuleCat Λ) X).obj (op K)) := by
    exact ⟨(DerivedCategory.boundedConstructible _ X).prop_of_iso eD.symm hDc.1,
      (DerivedCategory.finiteTorAmplitude _ X).prop_of_iso eD.symm hDc.2⟩
  have hNc := constructibleFiniteTor_tensor Λ X hDc' hWc
  let eN := DerivedCategory.derivedHomIsoCoefficientDualTensor K hWi
  have hNc' : DerivedCategory.boundedConstructibleFiniteTor Λ X
      (smoothRelativeDual (ModuleCat Λ) X K W) := by
    rw [smoothRelativeDual_eq]
    exact ⟨(DerivedCategory.boundedConstructible _ X).prop_of_iso eN.symm hNc.1,
      (DerivedCategory.finiteTorAmplitude _ X).prop_of_iso eN.symm hNc.2⟩
  exact ⟨hN, hNc', hbi⟩

end AlgebraicGeometry.Etale
