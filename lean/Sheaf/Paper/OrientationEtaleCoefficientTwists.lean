/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q23
-/
module

public import Sheaf.Paper.SixFunctorDatum
public import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
public import WeilConjectures.SixFunctors.Etale.Derived.Invertible
public import WeilConjectures.SixFunctors.Etale.Derived.Shift

/-! # Ordinary etale shifted root comparisons
Source: main-20261015 def-sf-orientation, clauses 1--3.
(blueprint: def-sf-orientation-etale-line-comparisons).
This is the generic coordinate interface; the owning orientation datum below
pins every comparison to its actual coefficient construction.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
set_option genInjectivity false
universe u v w v' w'
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- The ordinary etale shifted root line, with its specified coefficient ring.
Source: the finite etale components in clause 3
(blueprint: def-sf-orientation-etale-line-comparisons). -/
def sfOrientationEtaleLine (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (X : Scheme.{u}) (d : ℕ) :
    Etale.DerivedCategoryModule A X :=
  ((DerivedCategory.singleFunctor _ 0).obj (finiteEtaleTateSheaf A N X hA d))⟦2 * (d : ℤ)⟧

/-- The root-normalized derived pullback of the shifted finite line.
Source: clauses 1 and 3 (blueprint: def-sf-orientation-etale-line-comparisons). -/
def sfOrientationEtaleLinePullback (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : IsUnit (N : Γ(X, ⊤))) (hY : IsUnit (N : Γ(Y, ⊤))) (d : ℕ) :
    ((Etale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor).obj
      (sfOrientationEtaleLine A N hA Y d) ≅ sfOrientationEtaleLine A N hA X d :=
  (((Etale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor).commShiftIso
      (2 * (d : ℤ))).app _ ≪≫
    (shiftFunctor _ (2 * (d : ℤ))).mapIso
      ((Etale.singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) f).app _ ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso
          ((finiteEtaleTwistPullbackData A N hN hA).c f hY hX d))

/-- Flatness needed only to compute a derived tensor of degree-zero root lines.
Source: the locally free finite Tate line in clause 3
(blueprint: def-sf-orientation-etale-line-comparisons).
Proof: the recorded finite-etale twist pullback theorem trivializes each signed
line on an etale cover. It is the coefficient unit on that cover, hence flat.
Flatness is local for sheaves of modules and descends along the cover. -/
theorem sfOrientationEtaleLine_flat (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (X : Scheme.{u}) (hX : IsUnit (N : Γ(X, ⊤))) (d : ℕ) :
    ObjectProperty.flat (finiteEtaleTateSheaf A N X hA d) := by
  sorry

/-- The flat single-tensor calculation in the public derived-tensor coordinates.
Keeping the coefficient category generic prevents repeated expansion of the concrete
module-sheaf monoidal structure. Source: the ordinary derived tensor calculation
used in clause 2 (blueprint: def-sf-orientation-etale-line-comparisons). -/
def sfOrientationSingleTensorIso
    {A : Type v} [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A] {X : Scheme.{u}}
    (L F : Sheaf X.smallEtaleTopology A) (hL : ObjectProperty.flat L) :
    ((Etale.derivedTensor A X).obj ((DerivedCategory.singleFunctor _ 0).obj L)).obj
      ((DerivedCategory.singleFunctor _ 0).obj F) ≅
        (DerivedCategory.singleFunctor _ 0).obj (L ⊗ F) :=
  Etale.singleFunctorObjTensorIso L F hL

/-- Canonical multiplication of shifted ordinary root lines.
Source: the first comparison in clause 2 (blueprint: def-sf-orientation-etale-line-comparisons). -/
def sfOrientationEtaleProduct (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (X : Scheme.{u}) (hX : IsUnit (N : Γ(X, ⊤))) (d e : ℕ) :
    ((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj
      (sfOrientationEtaleLine A N hA X d)).obj (sfOrientationEtaleLine A N hA X e) ≅
        sfOrientationEtaleLine A N hA X (d + e) :=
  Etale.derivedTensorShiftIso (ModuleCat.{u + 1} A) _ _ _ _ ≪≫
    (shiftFunctor _ (2 * (d : ℤ) + 2 * (e : ℤ))).mapIso
      (sfOrientationSingleTensorIso _ _
          (sfOrientationEtaleLine_flat A N hN hA X hX d) ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso
          ((finiteEtaleTwistPullbackData A N hN hA).p X hX d e)) ≪≫
    eqToIso (by simp only [sfOrientationEtaleLine, Nat.cast_add, mul_add])



end WeilConjectures
