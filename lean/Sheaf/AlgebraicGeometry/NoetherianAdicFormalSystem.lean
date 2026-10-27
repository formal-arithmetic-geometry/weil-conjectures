/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q51
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import WeilConjectures.Blowup.Gluing
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.RingTheory.ExcellentRing

/-! # Noetherian adic formal schemes in infinitesimal-system coordinates

Source: Temkin, Non-embedded Desingularization, §§2.4.1--2.4.8
(blueprint: def-per-noetherian-adic-formal-system).

An adic formal scheme with a specified ideal of definition is represented by its
increasing system of closed thickenings. On an affine chart these are Spec(B/K^(n+1)),
where B is Noetherian and K-adically complete. Their structure sheaves recover the
completed structure sheaf by inverse limit. All maps below preserve this specified
adic filtration. Blowups over a fixed adic base have its extended ideal of definition.
The formal blowup condition uses the blowup of Spec B, followed by completion; it
never substitutes the blowup of a finite quotient.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AdicFormal

/-- The decreasing powers, viewed covariantly in the opposite lattice of ideals.
Source: Temkin §2.4.1 (blueprint: def-per-noetherian-adic-formal-system). -/
def powerDiagram {X : Scheme.{u}} (I : X.IdealSheafData) :
    ℕ ⥤ (X.IdealSheafData)ᵒᵖ where
  obj n := op (I ^ (n + 1))
  map f := (homOfLE (by
    intro U
    exact Ideal.pow_le_pow_right (Nat.succ_le_succ f.le))).op

/-- The actual infinitesimal thickenings of completion, including their inclusions.
Source: Temkin §2.4.1; the quotient-limit definition of adic completion
(blueprint: def-per-noetherian-adic-formal-system). -/
def completion {X : Scheme.{u}} (I : X.IdealSheafData) : ℕ ⥤ Scheme.{u} :=
  powerDiagram I ⋙ Scheme.IdealSheafData.subschemeFunctor X ⋙ Over.forget X

/-- The inclusion of the nth thickening into the original scheme.
Source: Temkin §2.4.1 (blueprint: def-per-noetherian-adic-formal-system). -/
def inclusion {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ) :
    (completion I).obj n ⟶ X :=
  (I ^ (n + 1)).subschemeι

/-- The ideal on Spec B corresponding to an actual ring ideal K.
Source: Temkin §2.4.1 (blueprint: def-per-noetherian-adic-formal-system). -/
def affineIdeal (B : CommRingCat.{u}) (K : Ideal B) : (Spec B).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop (K.map (Scheme.ΓSpecIso B).inv.hom)

/-- An open formal affine chart, represented at every infinitesimal order.
Source: Temkin §§2.4.1, 2.4.3 (blueprint: def-per-noetherian-adic-formal-system). -/
structure AffineChart (F : ℕ ⥤ Scheme.{u}) where
  ring : CommRingCat.{u}
  ideal : Ideal ring
  noetherian : IsNoetherianRing ring
  complete : IsAdicComplete ideal ring
  map : completion (affineIdeal ring ideal) ⟶ F
  openImmersion : ∀ n : ℕ, IsOpenImmersion (map.app n)
  cartesian : ∀ (n m : ℕ) (h : n ≤ m),
    IsPullback ((completion (affineIdeal ring ideal)).map (homOfLE h)) (map.app n)
      (map.app m) (F.map (homOfLE h))

/-- A finite open formal affine covering. The empty cover represents the empty formal
scheme. The affine charts have complete Noetherian rings, hence finitely generated
ideals of definition. The inverse-limit structure sheaf is encoded by the compatible
quotient schemes, rather than by an unspecified ringed space.
Source: Temkin §§2.4.1--2.4.3 (blueprint: def-per-noetherian-adic-formal-system). -/
def IsNoetherian (F : ℕ ⥤ Scheme.{u}) : Prop :=
  ∃ (r : ℕ) (a : Fin r → AffineChart F),
    ∀ (n : ℕ) (x : F.obj n), ∃ (i : Fin r) (y :
      (completion (affineIdeal (a i).ring (a i).ideal)).obj n), (a i).map.app n y = x

/-- A coherent open ideal is a compatible ideal on every thickening whose closed
subschemes stabilize: from order N onwards they factor through the Nth thickening.
On Noetherian formal affines this is exactly an ideal containing a power of the ideal
of definition, and its quotient is an ordinary closed scheme.
Source: Temkin §§2.4.2, 2.4.7 (blueprint: def-per-noetherian-adic-formal-system). -/
def IsCoherentOpenIdeal (F : ℕ ⥤ Scheme.{u})
    (J : ∀ n : ℕ, (F.obj n).IdealSheafData) : Prop :=
  (∀ (n m : ℕ) (h : n ≤ m), (J m).comap (F.map (homOfLE h)) = J n) ∧
    (∀ n : ℕ, RingedSpace.IsCoherent (F.obj n).toRingedSpace (J n).toModules) ∧
    ∃ N : ℕ, ∀ (n : ℕ) (h : N ≤ n), (F.map (homOfLE h)).ker ≤ J n

/-- A specified order at which an open ideal already defines its entire ordinary
center. Source: Temkin §2.4.2 (blueprint: def-per-noetherian-adic-formal-system). -/
def IsCenterOrder (F : ℕ ⥤ Scheme.{u})
    (J : ∀ n : ℕ, (F.obj n).IdealSheafData) (N : ℕ) : Prop :=
  ∀ (n : ℕ) (h : N ≤ n), (F.map (homOfLE h)).ker ≤ J n

/-- Regularity on complete formal affine chart rings.
Source: Temkin §2.4.9 (blueprint: def-per-noetherian-adic-formal-system). -/
def IsRegular (F : ℕ ⥤ Scheme.{u}) : Prop :=
  ∀ a : AffineChart F, IsRegularRing a.ring

/-- Reducedness on complete formal affine chart rings.
Source: Temkin §2.4.9 (blueprint: def-per-noetherian-adic-formal-system). -/
def IsReduced (F : ℕ ⥤ Scheme.{u}) : Prop :=
  ∀ a : AffineChart F, _root_.IsReduced a.ring

/-- Quasi-excellence on complete formal affine chart rings.
Source: Temkin §2.4.3 (blueprint: def-per-noetherian-adic-formal-system). -/
def IsQuasiExcellent (F : ℕ ⥤ Scheme.{u}) : Prop :=
  ∀ a : AffineChart F, _root_.IsQuasiExcellent a.ring

/-- The completion of an ordinary ideal is its extension to every thickening.
Source: Temkin §§2.4.2, 2.4.6 (blueprint: def-per-noetherian-adic-formal-system). -/
def completedIdeal {X : Scheme.{u}} (I J : X.IdealSheafData) :
    ∀ n : ℕ, ((completion I).obj n).IdealSheafData :=
  fun n => J.comap (inclusion I n)

/-- A formal blowup along an open coherent ideal, retaining that ideal. On every open
formal affine chart, take its ordinary ideal H on Spec B and the actual ordinary
blowup there; its completion is the restriction of the supplied formal morphism.
The last equation specifies the comparison over Spec B at every order.
Source: Temkin §§2.4.4--2.4.8 (blueprint: def-per-noetherian-adic-formal-system). -/
def IsBlowup {F G : ℕ ⥤ Scheme.{u}} (b : G ⟶ F)
    (J : ∀ n : ℕ, (F.obj n).IdealSheafData) : Prop :=
  IsNoetherian F ∧ IsNoetherian G ∧ IsCoherentOpenIdeal F J ∧
    ∀ a : AffineChart F, ∃ H : (Spec a.ring).IdealSheafData,
      RingedSpace.IsCoherent (Spec a.ring).toRingedSpace H.toModules ∧
      (∃ N : ℕ, 0 < N ∧ affineIdeal a.ring a.ideal ^ N ≤ H) ∧
      (∀ n : ℕ, (J n).comap (a.map.app n) =
        H.comap (inclusion (affineIdeal a.ring a.ideal) n)) ∧
      ∃ e : completion ((affineIdeal a.ring a.ideal).comap H.blowupMap) ≅
          pullback b a.map,
        ∀ n : ℕ,
          e.hom.app n ≫ (pullback.snd b a.map).app n ≫
              inclusion (affineIdeal a.ring a.ideal) n =
            inclusion ((affineIdeal a.ring a.ideal).comap H.blowupMap) n ≫ H.blowupMap

end AlgebraicGeometry.AdicFormal
