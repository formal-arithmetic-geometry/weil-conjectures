/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N7
-/
module

public import Sheaf.Paper.BoundaryProEtaleProjectionComparison
public import Sheaf.Paper.DualityPairing

public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
/-! # Boundary q and evaluation under site comparison

Source: blueprint boundary-duality discharge, final paragraph
(blueprint: def-weil-boundary-q-foundation).
The pro-etale transpose is computed in comparison coordinates using the recorded Hom
transport. This uses the actual finite exceptional functor, not an ambient pro-etale adjoint.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace AlgebraicGeometry.ProEtale.BoundaryComparisonOfCoefficients
open BoundaryComparison

section Coefficients

variable (C : Type v) [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
  [Etale.UpperStarPreservesFlat C] [ProEtale.UpperStarPreservesFlat C]
  [∀ W : Scheme.{u}, (comparisonUpperStar C W).PreservesFlat]

/-- The canonical etale signed symmetry, characterized component by component.
This is normalized data: the hom of the isomorphism is fixed to the actual descended
Koszul braiding, not an arbitrary morphism with the same endpoints.
Source: blueprint q formula (blueprint: def-weil-boundary-q-foundation). -/
structure EtaleSignedSymmetry (X : Scheme.{u}) where
  iso : Etale.derivedTensor C X ≅ (Etale.derivedTensor C X).flip
  hom_eq : ∀ K L : DerivedCategory (Sheaf X.smallEtaleTopology C),
    HEq ((iso.hom.app K).app L)
      (DerivedMonoidal.braiding' (DerivedCategory.Qh (C := Sheaf X.smallEtaleTopology C))
        (HomotopyCategory.quasiIso (Sheaf X.smallEtaleTopology C) (ComplexShape.up ℤ)) K L).hom

/-- The identical normalized signed symmetry on the pro-etale site.
Source: blueprint q formula (blueprint: def-weil-boundary-q-foundation). -/
structure ProSignedSymmetry (X : Scheme.{u}) where
  iso : ProEtale.derivedTensor C X ≅ (ProEtale.derivedTensor C X).flip
  hom_eq : ∀ K L : DerivedCategory (Sheaf (Scheme.ProEt.topology X) C),
    HEq ((iso.hom.app K).app L)
      (DerivedMonoidal.braiding'
        (DerivedCategory.Qh (C := Sheaf (Scheme.ProEt.topology X) C))
        (HomotopyCategory.quasiIso (Sheaf (Scheme.ProEt.topology X) C)
          (ComplexShape.up ℤ)) K L).hom

/-- Component of the fixed etale signed symmetry.
Source: blueprint q formula (blueprint: def-weil-boundary-q-foundation). -/
def etaleSwap (X : Scheme.{u}) (s : EtaleSignedSymmetry C X)
    (K L : DerivedCategory (Sheaf X.smallEtaleTopology C)) :
    ((Etale.derivedTensor C X).obj K).obj L ≅
      ((Etale.derivedTensor C X).obj L).obj K :=
  (s.iso.app K).app L

/-- Component of the fixed pro-etale signed symmetry.
Source: blueprint q formula (blueprint: def-weil-boundary-q-foundation). -/
def proSwap (X : Scheme.{u}) (s : ProSignedSymmetry C X)
    (K L : DerivedCategory (Sheaf (Scheme.ProEt.topology X) C)) :
    ((ProEtale.derivedTensor C X).obj K).obj L ≅
      ((ProEtale.derivedTensor C X).obj L).obj K :=
  (s.iso.app K).app L

/-- Etale q for the specified exceptional adjunction. The projection is the recorded
counit-defined map, and its inverse and both braidings have no free choices.
Source: blueprint q formula (blueprint: def-weil-boundary-q-foundation). -/
def etaleQForAdjunction {Z T : Scheme.{u}} (i : Z ⟶ T)
    (σZ : EtaleSignedSymmetry C Z) (σT : EtaleSignedSymmetry C T)
    (G : DerivedCategory (Sheaf T.smallEtaleTopology C) ⥤
      DerivedCategory (Sheaf Z.smallEtaleTopology C))
    (adj : etaleImage C i ⊣ G)
    (M N : DerivedCategory (Sheaf T.smallEtaleTopology C))
    [IsIso (etaleProjection C i (G.obj N) M)] :
    ((Etale.derivedTensor C Z).obj
      ((Etale.upperStar C i).leftDerivedFunctor.obj M)).obj (G.obj N) ⟶
        G.obj (((Etale.derivedTensor C T).obj M).obj N) :=
  adj.homEquiv _ _
    ((etaleImage C i).map (etaleSwap C Z σZ _ _).hom ≫
      inv (etaleProjection C i (G.obj N) M) ≫
      (etaleSwap C T σT _ _).hom ≫
      ((Etale.derivedTensor C T).obj M).map (adj.counit.app N))

/-- The pro-etale t before transposing. Its first variable is an actual exceptional
value when used below; μ is the normalized exceptional counit.
Source: blueprint q formula (blueprint: def-weil-boundary-q-foundation). -/
def proT {Z T : Scheme.{u}} (i : Z ⟶ T)
    (σZ : ProSignedSymmetry C Z) (σT : ProSignedSymmetry C T)
    (M N : DerivedCategory (Sheaf (Scheme.ProEt.topology T) C))
    (B : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) C))
    (μ : (proetaleImage C i).obj B ⟶ N)
    [IsIso (((ProEtale.rightDerivedLowerStarProjectionMap C i).app B).app M)] :
    (proetaleImage C i).obj
      (((ProEtale.derivedTensor C Z).obj
        ((upperStar C i).leftDerivedFunctor.obj M)).obj B) ⟶
      ((ProEtale.derivedTensor C T).obj M).obj N :=
  (proetaleImage C i).map (proSwap C Z σZ _ _).hom ≫
    inv (((ProEtale.rightDerivedLowerStarProjectionMap C i).app B).app M) ≫
    (proSwap C T σT _ _).hom ≫ ((ProEtale.derivedTensor C T).obj M).map μ

/-- Canonical comparison of the q source, before tensoring with theta_N.
Source: blueprint q comparison (blueprint: def-weil-boundary-q-foundation). -/
def qSourceIso {Z T : Scheme.{u}} (i : Z ⟶ T)
    (M : DerivedCategory (Sheaf T.smallEtaleTopology C))
    (B : DerivedCategory (Sheaf Z.smallEtaleTopology C)) :
    (comparison C Z).obj
      (((Etale.derivedTensor C Z).obj
        ((Etale.upperStar C i).leftDerivedFunctor.obj M)).obj B) ≅
      ((ProEtale.derivedTensor C Z).obj
        ((upperStar C i).leftDerivedFunctor.obj ((comparison C T).obj M))).obj
          ((comparison C Z).obj B) :=
  tensorComparison C Z _ _ ≪≫
    ((ProEtale.derivedTensor C Z).mapIso ((pullbackSquare C i).symm.app M)).app _

/-- Apply the specified exceptional Hom transport before specializing its source.
The universal transport argument prevents Lean from unfolding finite exceptional
values while checking tensor-source instances; all actual arrows are unchanged.
Source: blueprint q comparison, proof steps 1--2
(blueprint: def-weil-boundary-q-foundation). -/
def assembleProQ {Z T : Scheme.{u}} (i : Z ⟶ T)
    (σZ : ProSignedSymmetry C Z) (σT : ProSignedSymmetry C T)
    (Ge : DerivedCategory (Sheaf T.smallEtaleTopology C) ⥤
      DerivedCategory (Sheaf Z.smallEtaleTopology C))
    (Gp : DerivedCategory (Sheaf (Scheme.ProEt.topology T) C) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology Z) C))
    (tr : ∀ (H : DerivedCategory (Sheaf Z.smallEtaleTopology C))
      (L : DerivedCategory (Sheaf (Scheme.ProEt.topology T) C)),
      ((proetaleImage C i).obj ((comparison C Z).obj H) ⟶ L) →
        ((comparison C Z).obj H ⟶ Gp.obj L))
    (M N : DerivedCategory (Sheaf T.smallEtaleTopology C))
    (θ : (comparison C Z).obj (Ge.obj N) ⟶ Gp.obj ((comparison C T).obj N))
    (μ : (proetaleImage C i).obj (Gp.obj ((comparison C T).obj N)) ⟶
      (comparison C T).obj N)
    [IsIso (((ProEtale.rightDerivedLowerStarProjectionMap C i).app
      (Gp.obj ((comparison C T).obj N))).app ((comparison C T).obj M))] :
    (comparison C Z).obj (((Etale.derivedTensor C Z).obj
      ((Etale.upperStar C i).leftDerivedFunctor.obj M)).obj (Ge.obj N)) ⟶
      Gp.obj ((comparison C T).obj (((Etale.derivedTensor C T).obj M).obj N)) :=
  tr _ _ ((proetaleImage C i).map
      ((qSourceIso C i M (Ge.obj N)).hom ≫
        ((ProEtale.derivedTensor C Z).obj
          ((upperStar C i).leftDerivedFunctor.obj ((comparison C T).obj M))).map θ) ≫
    proT C i σZ σT ((comparison C T).obj M) ((comparison C T).obj N)
      (Gp.obj ((comparison C T).obj N)) μ ≫ (tensorComparison C T M N).inv)

/-- Apply comparison to q and then the target exceptional comparison, leaving
specialization of the tensor target inside this generic coefficient interface.
Source: blueprint q comparison, proof step 2
(blueprint: def-weil-boundary-q-foundation). -/
def comparedEtaleQ {Z T : Scheme.{u}} (i : Z ⟶ T)
    (σZ : EtaleSignedSymmetry C Z) (σT : EtaleSignedSymmetry C T)
    (Ge : DerivedCategory (Sheaf T.smallEtaleTopology C) ⥤
      DerivedCategory (Sheaf Z.smallEtaleTopology C))
    (Gp : DerivedCategory (Sheaf (Scheme.ProEt.topology T) C) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology Z) C))
    (adj : etaleImage C i ⊣ Ge)
    (θ : ∀ N : DerivedCategory (Sheaf T.smallEtaleTopology C),
      (comparison C Z).obj (Ge.obj N) ⟶ Gp.obj ((comparison C T).obj N))
    (M N : DerivedCategory (Sheaf T.smallEtaleTopology C))
    [IsIso (etaleProjection C i (Ge.obj N) M)] :
    (comparison C Z).obj (((Etale.derivedTensor C Z).obj
      ((Etale.upperStar C i).leftDerivedFunctor.obj M)).obj (Ge.obj N)) ⟶
      Gp.obj ((comparison C T).obj (((Etale.derivedTensor C T).obj M).obj N)) :=
  (comparison C Z).map (etaleQForAdjunction C i σZ σT Ge adj M N) ≫
    θ (((Etale.derivedTensor C T).obj M).obj N)

end Coefficients

end AlgebraicGeometry.ProEtale.BoundaryComparisonOfCoefficients
