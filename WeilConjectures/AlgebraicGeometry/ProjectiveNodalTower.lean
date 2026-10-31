/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import WeilConjectures.AlgebraicGeometry.PureDimension

/-!
# Projective nodal curves and finite towers

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé IX, Theorem 1.2,
p. 131 (the definition of a nodal curve after (vi)); the finite singular complement
in lem-trf-plurinodal-alteration, proof Step 9.
(blueprint: def-trf-projective-nodal-tower)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- A geometric ordinary double point has completed local ring `Ω[[x,y]]/(xy)`.
The completion is at the maximal ideal of the actual stalk of the geometric fibre.
Source: ILO, Exposé IX, Theorem 1.2, p. 131, ordinary quadratic points; the
completed-local-ring convention of lem-trf-plurinodal-alteration.
(blueprint: def-trf-projective-nodal-tower) -/
def IsGeometricOrdinaryDoublePoint (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (C : Scheme.{u}) (x : C) : Prop :=
  Nonempty
    (AdicCompletion (IsLocalRing.maximalIdeal (C.presheaf.stalk x)) (C.presheaf.stalk x) ≃+*
      (MvPowerSeries (Fin 2) Ω ⧸
        Ideal.span {(MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) :
          MvPowerSeries (Fin 2) Ω)}))

/-- A projective flat nodal curve with geometrically connected, pure one-dimensional
fibres and finite closed nonsmooth complement. Smoothness at a point is expressed by
existence of a smooth open neighbourhood in its geometric fibre. The last clause uses
Mathlib's canonical relative smooth locus, not an arbitrary smooth open.
Source: ILO, Exposé IX, Theorem 1.2, p. 131, and the finite-singular-complement
argument in lem-trf-plurinodal-alteration, proof Step 9.
(blueprint: def-trf-projective-nodal-tower) -/
def IsProjectiveNodalCurve {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  IsHProjective f ∧ Flat f ∧ GeometricallyConnected f ∧
    ∃ hfp : LocallyOfFinitePresentation f,
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
        (pullback f s).IsPureDimension 1 ∧
        ∀ x : ↥(pullback f s),
          (∃ U : (pullback f s).Opens, x ∈ U ∧ Smooth (U.ι ≫ pullback.snd f s)) ∨
            IsGeometricOrdinaryDoublePoint Ω (pullback f s) x) ∧
      ∃ (N : Scheme.{u}) (i : N ⟶ X), IsClosedImmersion i ∧
        Set.range i = ((@Scheme.Hom.smoothLocus _ _ f hfp : X.Opens) : Set X)ᶜ ∧
        IsFinite (i ≫ f)

/-- A finite tower of projective flat nodal curves, allowing the tower of length zero.
The zero constructor allows an isomorphic copy of the base; the successor constructor
appends one projective nodal curve. Thus its displayed morphism is the actual composite
of the stages, including their finite closed nonsmooth complements.
Source: ILO, Exposé IX, Theorem 1.2, p. 131, iterated as in
lem-trf-plurinodal-alteration, proof Steps 4--9.
(blueprint: def-trf-projective-nodal-tower) -/
inductive IsProjectiveNodalTower : {P S : Scheme.{u}} → (P ⟶ S) → Prop where
  /-- The length-zero tower is the base itself, up to its specified isomorphism.
  Source: lem-trf-plurinodal-alteration, Step 4.
  (blueprint: def-trf-projective-nodal-tower) -/
  | zero {P S : Scheme.{u}} (e : P ≅ S) : IsProjectiveNodalTower e.hom
  /-- Append one projective nodal curve to a finite nodal tower.
  Source: ILO, Exposé IX, Theorem 1.2, iterated in the alteration proof Step 6.
  (blueprint: def-trf-projective-nodal-tower) -/
  | succ {P T S : Scheme.{u}} (g : P ⟶ T) (h : T ⟶ S)
      (curve : IsProjectiveNodalCurve g) (tower : IsProjectiveNodalTower h) :
      IsProjectiveNodalTower (g ≫ h)

end AlgebraicGeometry
