/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.Sites.FiniteFreeCoefficientExtensionData
import all WeilConjectures.SixFunctors.FiniteFreeCoefficients.CoefficientMapClosedGeometry
import all WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
import all WeilConjectures.CategoryTheory.ProperBaseChange.ExchangeMateCube
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Exceptional geometric compatibility from the compact-support cube -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Etale
open scoped CategoryTheory.Functor
namespace WeilConjectures.FiniteFreeCoefficients

local instance compact_pull_additive (A : Type (u + 1)) [CommRing A]
    {Y X : Scheme.{u}} (g : Y ⟶ X) : (Sites.pull A g).Additive := by
  dsimp only [Sites.pull]
  infer_instance

local instance compact_pull_equivalence (A : Type (u + 1)) [CommRing A]
    {Y X : Scheme.{u}} (g : Y ⟶ X) [IsIso g] : (Sites.pull A g).IsEquivalence := by
  dsimp only [Sites.pull]
  infer_instance

private def compactCoefficient
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X S : Scheme.{u}} (f : X ⟶ S) [HasCompactification f]
    (N : Cat A X) :=
  ExceptionalCoefficients.compactSupportMap φ (HasCompactification.compactification f) N

private def compactCoefficientInv
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X S : Scheme.{u}} (f : X ⟶ S) [HasCompactification f]
    (N : Cat A X) := Sites.inverseOnDomain (compactCoefficient φ f N)

private theorem compact_cube_hs0
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X S : Scheme.{u}} (f : X ⟶ S) [HasCompactification f]
    [QuasiCompact f] (S' : Scheme.{u}) (e : S' ≅ S)
    (hc : ∀ N : Cat A X,
      (Sites.pull B e.hom).map
          (ExceptionalCoefficients.compactSupportMap φ
            (HasCompactification.compactification f) N) ≫
        (rightDerivedLowerShriekBaseChangeMap B
          (IsPullback.of_hasPullback f e.hom)).app ((scalarExtension φ X).obj N) ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} B)
          (pullback.snd f e.hom)).map
          ((Sites.scalarPull φ (pullback.fst f e.hom)).hom.app N) =
      (Sites.scalarPull φ e.hom).hom.app
          ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj N) ≫
        (scalarExtension φ S').map
          ((rightDerivedLowerShriekBaseChangeMap A
            (IsPullback.of_hasPullback f e.hom)).app N) ≫
        ExceptionalCoefficients.compactSupportMap φ
          (HasCompactification.compactification (pullback.snd f e.hom))
          ((Sites.pull A (pullback.fst f e.hom)).obj N))
    (N : Cat A X) :
    (Sites.pull B e.hom).map (compactCoefficient φ f N) ≫
      (rightDerivedLowerShriekBaseChangeMap B (IsPullback.of_hasPullback f e.hom)).app
        ((scalarExtension φ X).obj N) ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} B) (pullback.snd f e.hom)).map
          ((Sites.scalarPull φ (pullback.fst f e.hom)).hom.app N) =
    (Sites.scalarPull φ e.hom).hom.app
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj N) ≫
      (scalarExtension φ S').map
        ((rightDerivedLowerShriekBaseChangeMap A (IsPullback.of_hasPullback f e.hom)).app N) ≫
      compactCoefficient φ (pullback.snd f e.hom)
        ((Sites.pull A (pullback.fst f e.hom)).obj N)
    := hc N

private theorem compact_cube_hs
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X S : Scheme.{u}} (f : X ⟶ S) [HasCompactification f]
    [QuasiCompact f] (S' : Scheme.{u}) (e : S' ≅ S)
    (N : Cat A X)
    [IsIso (rightDerivedLowerShriekBaseChangeMap A (IsPullback.of_hasPullback f e.hom))]
    [IsIso (rightDerivedLowerShriekBaseChangeMap B (IsPullback.of_hasPullback f e.hom))]
    (hs0 :
    (Sites.pull B e.hom).map (compactCoefficient φ f N) ≫
      (rightDerivedLowerShriekBaseChangeMap B (IsPullback.of_hasPullback f e.hom)).app
        ((scalarExtension φ X).obj N) ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} B) (pullback.snd f e.hom)).map
          ((Sites.scalarPull φ (pullback.fst f e.hom)).hom.app N) =
    (Sites.scalarPull φ e.hom).hom.app
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj N) ≫
      (scalarExtension φ S').map
        ((rightDerivedLowerShriekBaseChangeMap A (IsPullback.of_hasPullback f e.hom)).app N) ≫
      compactCoefficient φ (pullback.snd f e.hom)
        ((Sites.pull A (pullback.fst f e.hom)).obj N)) :
    (Sites.pull B e.hom).map (compactCoefficient φ f N) ≫
      ((asIso (rightDerivedLowerShriekBaseChangeMap B (IsPullback.of_hasPullback f e.hom))).app
        ((scalarExtension φ X).obj N) ≪≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} B) (pullback.snd f e.hom)).mapIso
          ((Sites.scalarPull φ (pullback.fst f e.hom)).app N)).hom =
    ((Sites.scalarPull φ e.hom).app
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj N) ≪≫
      (scalarExtension φ S').mapIso
        ((asIso (rightDerivedLowerShriekBaseChangeMap A
          (IsPullback.of_hasPullback f e.hom))).app N)).hom ≫
      compactCoefficient φ (pullback.snd f e.hom)
        ((Sites.pull A (pullback.fst f e.hom)).obj N) := by
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, asIso_hom, Category.assoc]
  exact hs0

private theorem compact_cube_hc'
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X S : Scheme.{u}} (f : X ⟶ S) [HasCompactification f]
    [QuasiCompact f] (S' : Scheme.{u}) (e : S' ≅ S)
    (hc : ∀ N : Cat A X,
      (Sites.pull B e.hom).map
          (ExceptionalCoefficients.compactSupportMap φ
            (HasCompactification.compactification f) N) ≫
        (rightDerivedLowerShriekBaseChangeMap B
          (IsPullback.of_hasPullback f e.hom)).app ((scalarExtension φ X).obj N) ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} B)
          (pullback.snd f e.hom)).map
          ((Sites.scalarPull φ (pullback.fst f e.hom)).hom.app N) =
      (Sites.scalarPull φ e.hom).hom.app
          ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj N) ≫
        (scalarExtension φ S').map
          ((rightDerivedLowerShriekBaseChangeMap A
            (IsPullback.of_hasPullback f e.hom)).app N) ≫
        ExceptionalCoefficients.compactSupportMap φ
          (HasCompactification.compactification (pullback.snd f e.hom))
          ((Sites.pull A (pullback.fst f e.hom)).obj N))
    (N : Cat A X)
    [IsIso (rightDerivedLowerShriekBaseChangeMap A (IsPullback.of_hasPullback f e.hom))]
    [IsIso (rightDerivedLowerShriekBaseChangeMap B (IsPullback.of_hasPullback f e.hom))] :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} B) (pullback.snd f e.hom)).map
        ((Sites.scalarPull φ (pullback.fst f e.hom)).inv.app N) ≫
      (asIso (rightDerivedLowerShriekBaseChangeMap B
        (IsPullback.of_hasPullback f e.hom))).inv.app ((scalarExtension φ X).obj N) ≫
      (Sites.pull B e.hom).map (compactCoefficientInv φ f N) =
    compactCoefficientInv φ (pullback.snd f e.hom)
        ((Sites.pull A (pullback.fst f e.hom)).obj N) ≫
      (scalarExtension φ S').map ((asIso (rightDerivedLowerShriekBaseChangeMap A
        (IsPullback.of_hasPullback f e.hom))).inv.app N) ≫
      (Sites.scalarPull φ e.hom).inv.app
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj N) := by
  have q := inverseOnDomain_equivalence_square (Sites.pull B e.hom)
    (compactCoefficient φ f N)
    (compactCoefficient φ (pullback.snd f e.hom) ((Sites.pull A (pullback.fst f e.hom)).obj N))
    _ _ (compact_cube_hs φ f S' e N (compact_cube_hs0 φ f S' e hc N))
  rw [← Iso.eq_comp_inv, Category.assoc, ← Iso.inv_comp_eq] at q
  simp only [Iso.trans_inv, Iso.app_inv, Functor.mapIso_inv, Category.assoc] at q
  exact q

end WeilConjectures.FiniteFreeCoefficients
