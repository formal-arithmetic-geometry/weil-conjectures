/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q51
-/
module

public import Sheaf.AlgebraicGeometry.NoetherianAdicFormalSystem
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.OrdinaryResolutionRule
public import Mathlib.AlgebraicGeometry.Properties

/-! # Supported blowup towers with all ordered center ideals

Source: Temkin, Non-embedded Desingularization, §§2.2.1--2.2.2, 2.4.7--2.4.11
(blueprint: def-per-supported-centered-blowup-towers).

The ordinary towers are the project's `OrdinaryBlowupTower`s
(blueprint: def-trf-ordinary-resolution-rule) with a fixed number of centers.
The ordinary and formal towers have the same finite set of stage labels. Their
isomorphisms preserve the base, every arrow and every center ideal. In particular,
identity blowups are retained. A completion comparison consists of the actual
infinitesimal completion isomorphisms, with their equations over the ordinary levels.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AdicFormal

/-- The project's ordinary blowup tower with its ordered centers
(`OrdinaryBlowupTower`, blueprint: def-trf-ordinary-resolution-rule), with its number
of centers fixed to r so that it can be compared stage by stage with a formal tower.
Source: Temkin §§2.2.1--2.2.2 (blueprint: def-per-supported-centered-blowup-towers). -/
structure OrdinaryTowerData (X : Scheme.{u}) (r : ℕ) where
  tower : OrdinaryBlowupTower X
  length_eq : tower.length = r

namespace OrdinaryTowerData

variable {X : Scheme.{u}} {r : ℕ} (T : OrdinaryTowerData X r)

/-- The stage of the underlying tower with label i. Source: Temkin §2.2.1
(blueprint: def-per-supported-centered-blowup-towers). -/
def stage (i : Fin (r + 1)) : Fin (T.tower.length + 1) :=
  Fin.cast (by rw [T.length_eq]) i

/-- The center of the underlying tower with label i. Source: Temkin §2.2.1
(blueprint: def-per-supported-centered-blowup-towers). -/
def centerStage (i : Fin r) : Fin T.tower.length :=
  Fin.cast T.length_eq.symm i

/-- The level with label i; level 0 is identified with X by `tower.initial`.
Source: Temkin §2.2.1 (blueprint: def-per-supported-centered-blowup-towers). -/
def level (i : Fin (r + 1)) : Scheme.{u} :=
  T.tower.level (T.stage i)

/-- The structural map of a level to X. Source: Temkin §2.2.1
(blueprint: def-per-supported-centered-blowup-towers). -/
def over (i : Fin (r + 1)) : T.level i ⟶ X :=
  T.tower.toBase (T.stage i)

/-- The blowup arrow from level i+1 to level i. Source: Temkin §2.2.1
(blueprint: def-per-supported-centered-blowup-towers). -/
def arrow (i : Fin r) : T.level i.succ ⟶ T.level i.castSucc :=
  T.tower.transition (T.stage i.castSucc) (T.stage i.succ)
    (Fin.le_iff_val_le_val.2 (by simp [stage]))

/-- The ordered center ideal on level i. Source: Temkin §2.2.1
(blueprint: def-per-supported-centered-blowup-towers). -/
def center (i : Fin r) : (T.level i.castSucc).IdealSheafData :=
  T.tower.center (T.centerStage i)

end OrdinaryTowerData

/-- A finite ordinary supported blowup tower with coherent centers, over the fixed
base X: an ordinary blowup tower of the project with r centers and r+1 levels,
including r=0, whose centers are coherent and contain a positive power of the
extended ideal I. No regularity, reducedness, nonemptiness or nowhere density is
required of a center.
Source: Temkin §§2.2.1--2.2.2, 2.4.7
(blueprint: def-per-supported-centered-blowup-towers). -/
structure OrdinaryTower {X : Scheme.{u}} (I : X.IdealSheafData) (r : ℕ)
    extends OrdinaryTowerData X r where
  coherent : ∀ i : Fin r,
    RingedSpace.IsCoherent
      ((OrdinaryTowerData.mk tower length_eq).level i.castSucc).toRingedSpace
      ((OrdinaryTowerData.mk tower length_eq).center i).toModules
  supported : ∀ i : Fin r, ∃ N : ℕ, 0 < N ∧
    (I.comap ((OrdinaryTowerData.mk tower length_eq).over i.castSucc)) ^ N ≤
      (OrdinaryTowerData.mk tower length_eq).center i

/-- A finite formal supported blowup tower over the specified completion of X.
The base ideal of definition is extended at each stage, so a single infinitesimal
order n is used throughout. Coherent open center ideals are retained at every stage.
Source: Temkin §§2.4.4--2.4.8
(blueprint: def-per-supported-centered-blowup-towers). -/
structure FormalTower {X : Scheme.{u}} (I : X.IdealSheafData) (r : ℕ) where
  level : Fin (r + 1) → (ℕ ⥤ Scheme.{u})
  noetherian : ∀ i : Fin (r + 1), IsNoetherian (level i)
  over : ∀ i : Fin (r + 1), level i ⟶ completion I
  base : level 0 ≅ completion I
  over_zero : over 0 = base.hom
  arrow : ∀ i : Fin r, level i.succ ⟶ level i.castSucc
  over_arrow : ∀ i : Fin r, arrow i ≫ over i.castSucc = over i.succ
  center : ∀ (i : Fin r) (n : ℕ), ((level i.castSucc).obj n).IdealSheafData
  openIdeal : ∀ i : Fin r, IsCoherentOpenIdeal (level i.castSucc) (center i)
  blowup : ∀ i : Fin r, IsBlowup (arrow i) (center i)

/-- An isomorphism of ordinary towers, preserving all ordered ideals and the base.
Source: Temkin §§2.2.1--2.2.2 (blueprint: def-per-supported-centered-blowup-towers). -/
structure OrdinaryIso {X : Scheme.{u}} {I : X.IdealSheafData} {r : ℕ}
    (T S : OrdinaryTower I r) where
  iso : ∀ i : Fin (r + 1), T.level i ≅ S.level i
  over : ∀ i : Fin (r + 1), (iso i).hom ≫ S.over i = T.over i
  arrows : ∀ i : Fin r,
    (iso i.succ).hom ≫ S.arrow i = T.arrow i ≫ (iso i.castSucc).hom
  centers : ∀ i : Fin r, (S.center i).comap (iso i.castSucc).hom = T.center i

/-- An isomorphism of formal towers preserving every infinitesimal center ideal.
Source: Temkin §§2.4.7--2.4.8 (blueprint: def-per-supported-centered-blowup-towers). -/
structure FormalIso {X : Scheme.{u}} {I : X.IdealSheafData} {r : ℕ}
    (T S : FormalTower I r) where
  iso : ∀ i : Fin (r + 1), T.level i ≅ S.level i
  over : ∀ i : Fin (r + 1), (iso i).hom ≫ S.over i = T.over i
  arrows : ∀ i : Fin r,
    (iso i.succ).hom ≫ S.arrow i = T.arrow i ≫ (iso i.castSucc).hom
  centers : ∀ (i : Fin r) (n : ℕ),
    (S.center i n).comap ((iso i.castSucc).hom.app n) = T.center i n

/-- Completion of the specified ordinary tower to the specified formal tower.
The equations specify every structural map over the ordinary schemes and identify
all completed center ideals. These are actual completion diagrams, with no arbitrary
replacement morphism or unspecified choice of a formal model.
Source: Temkin §2.4.6 and Lemma 2.4.3(i)
(blueprint: def-per-supported-centered-blowup-towers). -/
structure Completion {X : Scheme.{u}} {I : X.IdealSheafData} {r : ℕ}
    (T : OrdinaryTower I r) (F : FormalTower I r) where
  iso : ∀ i : Fin (r + 1), completion (I.comap (T.over i)) ≅ F.level i
  over : ∀ (i : Fin (r + 1)) (n : ℕ),
    (iso i).hom.app n ≫ (F.over i).app n ≫ inclusion I n =
      inclusion (I.comap (T.over i)) n ≫ T.over i
  arrows : ∀ (i : Fin r) (n : ℕ),
    (iso i.succ).hom.app n ≫ (F.arrow i).app n ≫ (iso i.castSucc).inv.app n ≫
        inclusion (I.comap (T.over i.castSucc)) n =
      inclusion (I.comap (T.over i.succ)) n ≫ T.arrow i
  centers : ∀ (i : Fin r) (n : ℕ),
    (F.center i n).comap ((iso i.castSucc).hom.app n) =
      completedIdeal (I.comap (T.over i.castSucc)) (T.center i) n

/-- The structural map from a formal center at a finite order to its ordinary level,
using the supplied completion comparison.
Source: Temkin Lemma 2.4.3(i) (blueprint: def-per-supported-centered-blowup-towers). -/
def Completion.centerToLevel {X : Scheme.{u}} {I : X.IdealSheafData} {r : ℕ}
    {T : OrdinaryTower I r} {F : FormalTower I r} (c : Completion T F)
    (i : Fin r) (n : ℕ) : (F.center i n).subscheme ⟶ T.level i.castSucc :=
  (F.center i n).subschemeι ≫ (c.iso i.castSucc).inv.app n ≫
    inclusion (I.comap (T.over i.castSucc)) n

/-- The canonical scheme identification of each center, at every order at which it
is fully defined, together with its nonemptiness and regularity equivalences.
Uniqueness is over the ordinary level, not just an abstract isomorphism of schemes.
Source: Temkin Lemma 2.4.3(i)--(ii)
(blueprint: def-per-supported-centered-blowup-towers). -/
def Completion.CentersAgree {X : Scheme.{u}} {I : X.IdealSheafData} {r : ℕ}
    {T : OrdinaryTower I r} {F : FormalTower I r} (c : Completion T F) : Prop :=
  ∀ (i : Fin r) (N : ℕ), IsCenterOrder (F.level i.castSucc) (F.center i) N →
    (∃! e : (T.center i).subscheme ≅ (F.center i N).subscheme,
      e.hom ≫ c.centerToLevel i N = (T.center i).subschemeι) ∧
      (Nonempty (T.center i).subscheme ↔ Nonempty (F.center i N).subscheme) ∧
      (IsRegularScheme (T.center i).subscheme ↔ IsRegularScheme (F.center i N).subscheme)

/-- Ordinary centers lie over the nonregular locus of the original base.
Source: Temkin §§2.3.1, 2.4.10
(blueprint: def-per-supported-centered-blowup-towers). -/
def OrdinaryTower.HasSingularCenters {X : Scheme.{u}} {I : X.IdealSheafData} {r : ℕ}
    (T : OrdinaryTower I r) : Prop :=
  ∀ (i : Fin r) (x : T.level i.castSucc), x ∈ (T.center i).support →
    ¬ IsRegularLocalRing (X.presheaf.stalk (T.over i.castSucc x))

/-- Formal centers lie over the completion of the original singular locus.
This is set-theoretic support, exactly as in the ordinary condition. All points are
mapped through the canonical closed thickening of X, so the locus is the completion
of X_sing, not a singular locus chosen independently at an intermediate level.
Source: Temkin §§2.4.9--2.4.10
(blueprint: def-per-supported-centered-blowup-towers). -/
def FormalTower.HasSingularCenters {X : Scheme.{u}} {I : X.IdealSheafData} {r : ℕ}
    (F : FormalTower I r) : Prop :=
  ∀ (i : Fin r) (n : ℕ) (x : (F.level i.castSucc).obj n),
    x ∈ (F.center i n).support →
      ¬ IsRegularLocalRing (X.presheaf.stalk
        (((F.over i.castSucc).app n ≫ inclusion I n) x))

/-- Each ordinary center is nowhere dense in its own level.
Source: the reduced clause following Temkin Lemma 2.4.3(ii)
(blueprint: def-per-supported-centered-blowup-towers). -/
def OrdinaryTower.HasNowhereDenseCenters {X : Scheme.{u}} {I : X.IdealSheafData} {r : ℕ}
    (T : OrdinaryTower I r) : Prop :=
  ∀ i : Fin r, IsNowhereDense ((T.center i).support : Set (T.level i.castSucc))

end AlgebraicGeometry.AdicFormal
