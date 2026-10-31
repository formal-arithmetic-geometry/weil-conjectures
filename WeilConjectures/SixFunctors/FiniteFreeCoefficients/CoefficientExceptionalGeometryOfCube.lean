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
import WeilConjectures.CategoryTheory.SixFunctors.PointwiseExchangeMateCube

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

private theorem compactCoefficient_naturality
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X S : Scheme.{u}} (f : X ⟶ S) [HasCompactification f]
    {N M : Cat A X} (a : N ⟶ M) :
    (scalarExtension φ S).map
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map a) ≫
        compactCoefficient φ f M =
      compactCoefficient φ f N ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} B) f).map
          ((scalarExtension φ X).map a) := by
  exact (compactScalarMap φ (HasCompactification.compactification f)).naturality a

private theorem compactCoefficientInv_naturality_iso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X S : Scheme.{u}} (f : X ⟶ S) [HasCompactification f]
    {N M : Cat A X} (a : N ⟶ M) (ha : IsIso a) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} B) f).map
        ((scalarExtension φ X).map a) ≫ compactCoefficientInv φ f M =
      compactCoefficientInv φ f N ≫ (scalarExtension φ S).map
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map a) := by
  have := ha
  exact (inverseOnDomain_equivalence_square (𝟭 _) (compactCoefficient φ f N)
    (compactCoefficient φ f M)
    ((scalarExtension φ S).mapIso
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).mapIso (asIso a)))
    ((rightDerivedLowerShriek (ModuleCat.{u + 1} B) f).mapIso
      ((scalarExtension φ X).mapIso (asIso a)))
    (compactCoefficient_naturality φ f a).symm).symm

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


/-- The forward compact-support cube suffices for the exceptional coefficient square.
Source: blueprint latest, coefficient extension proof, geometric compatibility.
(blueprint: lem-sf-coefficient-exceptional-geometry-of-cube).
Proof: base change is invertible for compact support. The forward cube conjugates
coefficient arrows under the geometric equivalence. Invert that square on its
isomorphism domain and extend by zero on the other domain. The resulting family
is natural along isomorphisms. Apply pointwiseExchangeMate_cube to the four
exceptional adjunctions, using that the geometric mate of an invertible square
along equivalences is invertible. Normalize its counit transpose to the prescribed
smoothExceptionalBaseChangeMap and cancel the scalar/geometric isomorphisms. -/
theorem coefficient_exceptional_geometry_of_compact_cube
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
    (M : Cat A S) : ExceptionalCoefficients.BaseChangeCompatibility φ f e.hom M := by
  let h := pullback.fst f e.hom
  let j := pullback.snd f e.hom
  let sq := IsPullback.of_hasPullback f e.hom
  have := isIso_rightDerivedLowerShriekBaseChangeMap A sq
  have := isIso_rightDerivedLowerShriekBaseChangeMap B sq
  let exA := asIso (rightDerivedLowerShriekBaseChangeMap A sq)
  let exB := asIso (rightDerivedLowerShriekBaseChangeMap B sq)
  let RA := rightDerivedLowerShriek (ModuleCat.{u + 1} A) f
  let RB' := rightDerivedLowerShriek (ModuleCat.{u + 1} B) j
  let Q := scalarExtension φ S'
  let lg := Sites.scalarPull φ e.hom
  let lh := Sites.scalarPull φ h
  have hc' (N : Cat A X) := compact_cube_hc' φ f S' e hc N
  let a := rightDerivedUpperShriekAdjunction A f
  let b := rightDerivedUpperShriekAdjunction B f
  let a' := rightDerivedUpperShriekAdjunction A j
  let b' := rightDerivedUpperShriekAdjunction B j
  have : IsIso (mateEquiv a a' (TwoSquare.mk _ _ _ _ exA.inv)).natTrans :=
    isIso_mateEquiv_of_isEquivalence a a' _
  have q := pointwiseExchangeMate_cube a b a' b'
    (Sites.pull A h) (Sites.pull A e.hom) (Sites.pull B h) (Sites.pull B e.hom)
    exA (Sites.scalarPull φ h) (Sites.scalarPull φ e.hom) exB
    (compactCoefficientInv φ f) (compactCoefficientInv φ j) hc'
    (fun a ha ↦ compactCoefficientInv_naturality_iso φ j a ha) M (inferInstance)
  have q' := congrArg (fun z ↦
    lh.inv.app ((rightDerivedUpperShriek A f).obj M) ≫ z ≫
      (rightDerivedUpperShriek B j).map (lg.inv.app M)) q
  simp only [Category.assoc, ← Functor.map_comp] at q'
  simpa only [ExceptionalCoefficients.BaseChangeCompatibility,
    ExceptionalCoefficients.mateMap, ExceptionalCoefficients.comparisonInverse,
    smoothExceptionalBaseChangeMap, compactCoefficientInv, compactCoefficient,
    Sites.inverseOnDomain, pointwiseExchangeMate, mate_app_eq_adjunct,
    a, b, a', b', exA, exB, asIso_inv, NatIso.inv_hom_app,
    lh, lg, h, j, sq, Sites.scalarPull, Sites.pull, NatIso.isIso_inv_app,
    Functor.comp_obj, Functor.id_obj, Category.assoc, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id] using q'.symm

end WeilConjectures.FiniteFreeCoefficients
