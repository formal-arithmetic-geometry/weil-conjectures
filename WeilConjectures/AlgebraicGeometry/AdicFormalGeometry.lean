/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.Geometry.RingedSpace.SheafedSpace
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import WeilConjectures.RingTheory.GRing
public import WeilConjectures.RingTheory.ExcellentRing

/-!
# Adic formal completions and formal affine charts

Source: Temkin, Functorial desingularization of quasi-excellent schemes in characteristic zero:
the non-embedded case, sections 2.4.1, 2.4.3 and 2.4.12
(blueprint: def-per-adic-formal-geometry).

The completion is the colimit in ringed spaces of the closed infinitesimal thickenings.
The ringed-space colimit computes the structure sheaf as the inverse limit of their sheaves.
On affine opens this is the usual inverse limit of quotient rings.
-/

@[expose] public section

set_option autoImplicit false

universe u

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- The diagram of closed thickenings defined by the powers of an ideal sheaf.
Source: Temkin, section 2.4.1 (blueprint: def-per-adic-formal-geometry). -/
def adicThickeningDiagram {X : Scheme.{u}} (I : X.IdealSheafData) : ℕ ⥤ Scheme.{u} where
  obj n := (I ^ n).subscheme
  map {_n _m} h := Scheme.IdealSheafData.inclusion
    (pow_le_pow_right_of_le_one' (show I ≤ 1 from le_top) h.le)
  map_id _n := Scheme.IdealSheafData.inclusion_id _
  map_comp _h _k := (Scheme.IdealSheafData.inclusion_comp _ _).symm

/-- The adic formal completion, constructed as the ringed-space colimit of the thickenings.
Its underlying space is the support of the ideal; its sheaf is the inverse limit of the
quotient structure sheaves. Source: Temkin, section 2.4.1
(blueprint: def-per-adic-formal-geometry). -/
def adicFormalCompletion {X : Scheme.{u}} (I : X.IdealSheafData) : RingedSpace.{u} :=
  colimit (adicThickeningDiagram I ⋙ Scheme.forgetToLocallyRingedSpace ⋙
    LocallyRingedSpace.forgetToSheafedSpace)

/-- The canonical maps of thickenings associated to an ideal-compatible morphism.
Source: Temkin, Corollary 2.4.5 (blueprint: def-per-adic-formal-geometry). -/
def adicThickeningMap {X Y : Scheme.{u}} (f : Y ⟶ X)
    (I : X.IdealSheafData) (J : Y.IdealSheafData) (h : I.comap f ≤ J) :
    adicThickeningDiagram J ⟶ adicThickeningDiagram I where
  app n := (J ^ n).subschemeMap (I ^ n) f
    (Scheme.IdealSheafData.le_map_iff_comap_le.mpr
      ((Scheme.IdealSheafData.comap_pow f I n).le.trans (pow_le_pow_left' h n)))
  naturality {n m} a := by
    apply (cancel_mono (I ^ m).subschemeι).mp
    simp [adicThickeningDiagram, Category.assoc]

/-- The induced completed morphism, obtained by applying the colimit functor to the canonical
maps of thickenings. Source: Temkin, Corollary 2.4.5
(blueprint: def-per-adic-formal-geometry). -/
def adicFormalCompletionMap {X Y : Scheme.{u}} (f : Y ⟶ X)
    (I : X.IdealSheafData) (J : Y.IdealSheafData) (h : I.comap f ≤ J) :
    adicFormalCompletion J ⟶ adicFormalCompletion I :=
  colimMap (Functor.whiskerRight (adicThickeningMap f I J h)
    (Scheme.forgetToLocallyRingedSpace ⋙ LocallyRingedSpace.forgetToSheafedSpace))

/-- The formal spectrum of a ring with the topology defined by powers of an ideal.
For a complete separated Noetherian ring this is the space of open primes with its completed
structure sheaf. Source: Temkin, section 2.4.1
(blueprint: def-per-adic-formal-geometry). -/
def adicFormalSpec (A : CommRingCat.{u}) (K : Ideal A) : RingedSpace.{u} :=
  adicFormalCompletion (Scheme.IdealSheafData.ofIdealTop
    (K.map (Scheme.ΓSpecIso A).inv.hom))

/-- A formal affine open in a ringed space, with its ring of sections as coordinate ring.
Source: Temkin, sections 2.4.1 and 2.4.14 (blueprint: def-per-adic-formal-geometry). -/
def IsAdicFormalAffineOpen (Z : RingedSpace.{u}) (U : Opens Z) : Prop :=
  ∃ K : Ideal (Z.presheaf.obj (op U)),
    IsNoetherianRing (Z.presheaf.obj (op U)) ∧ K.FG ∧
      IsAdicComplete K (Z.presheaf.obj (op U)) ∧
        Nonempty (Z.restrict U.isOpenEmbedding ≅ adicFormalSpec (Z.presheaf.obj (op U)) K)

/-- A Noetherian adic formal scheme has a finite cover by complete Noetherian formal affines.
Source: Temkin, section 2.4.1 (blueprint: def-per-adic-formal-geometry). -/
def IsNoetherianAdicFormalScheme (Z : RingedSpace.{u}) : Prop :=
  ∃ (n : ℕ) (U : Fin n → Opens Z), (⨆ i, U i) = ⊤ ∧
    ∀ i, IsAdicFormalAffineOpen Z (U i)

/-- Reducedness of the coordinate rings of every formal affine chart.
Source: Temkin, section 2.4.9 (blueprint: def-per-adic-formal-geometry). -/
def IsReducedAdicFormalScheme (Z : RingedSpace.{u}) : Prop :=
  ∀ U : Opens Z, IsAdicFormalAffineOpen Z U → _root_.IsReduced (Z.presheaf.obj (op U))

/-- Quasi-excellence of the coordinate rings of every formal affine chart.
Source: Temkin, section 2.4.3 (blueprint: def-per-adic-formal-geometry). -/
def IsQuasiExcellentAdicFormalScheme (Z : RingedSpace.{u}) : Prop :=
  ∀ U : Opens Z, IsAdicFormalAffineOpen Z U → IsQuasiExcellent (Z.presheaf.obj (op U))

/-- The ring homomorphism on sections for a pair of opens with source mapping into target.
Source: Temkin, Lemma 2.4.6 (blueprint: def-per-adic-formal-geometry). -/
def adicFormalAppLE {Z W : RingedSpace.{u}} (g : W ⟶ Z)
    (U : Opens Z) (V : Opens W) (e : V ≤ (Opens.map g.hom.base).obj U) :
    Z.presheaf.obj (op U) ⟶ W.presheaf.obj (op V) :=
  g.hom.c.app (op U) ≫ W.presheaf.map (homOfLE e).op

/-- Regularity on every pair of formal affine opens, the explicit form of regularity in
Temkin, section 2.4.12 and Lemma 2.4.6 (blueprint: def-per-adic-formal-geometry). -/
def IsRegularOnAdicFormalAffines {Z W : RingedSpace.{u}} (g : W ⟶ Z) : Prop :=
  ∀ (U : Opens Z) (V : Opens W),
    IsAdicFormalAffineOpen Z U → IsAdicFormalAffineOpen W V →
      ∀ e : V ≤ (Opens.map g.hom.base).obj U, (adicFormalAppLE g U V e).hom.IsRegular

end AlgebraicGeometry
