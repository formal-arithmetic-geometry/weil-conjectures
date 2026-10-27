/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.AlgebraicGeometry.FormalChartGeometricData

/-! # Noetherianity and closed-point contraction in a toric chart

Source: Stacks 00FN, 04HX, 04GP, 06LJ; ILO VI 1.8.
(blueprint: lem-trf-formal-chart-local-preparation).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry
open FormalChartGeometric

/-- Noetherianity and closed-point contraction in a toric chart.
Source: Stacks 00FN, 04HX, 04GP, 06LJ; ILO VI 1.8.
(blueprint: lem-trf-formal-chart-local-preparation).

Proof: Take a Noetherian affine neighbourhood in W and localize at the image of z.
Pointed-neighbourhood/triple comparison identifies the strict base with the strict
henselization of this Noetherian local ring; strict henselization preserves
Noetherianity. Finitely many generators of Q give a surjection from a polynomial
A-algebra onto the tensor ring. It is Noetherian, as is its localization at q.
The equation for eC over A and the closed-point equation for zA identify contraction
of q with the kernel of the strict-base evaluation into Omega. This kernel is the
maximal ideal, since this is the closed geometric point. No log regularity is used.
-/
theorem formal_chart_local_preparation
    (W : FineSaturatedLogScheme.{u})
    (R Q : Type u) [CommMonoid R] [CommMonoid Q]
    (_hQ : IsFineSaturatedMonoid Q)
    (y : W.scheme ⟶ Spec (.of (MonoidAlgebra ℤ R)))
    (h : R →* Q)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (z : Spec (.of Ω) ⟶ chartScheme y h)
    (zA : Spec (.of Ω) ⟶ pullback (baseMap y h z) (pullback.fst y (toricMap h)))
    (_hzA : zA ≫ pullback.snd (baseMap y h z) (pullback.fst y (toricMap h)) = z)
    (_hzAclosed : zA ≫ pullback.fst (baseMap y h z) (pullback.fst y (toricMap h)) =
      Spec.map (Scheme.strictHenselizationEval (z ≫ pullback.fst y (toricMap h))))
    (eC : Spec (Algebra.monoidChartTensor (alpha y h z) h) ≅
      pullback (baseMap y h z) (pullback.fst y (toricMap h)))
    (_heCA : eC.hom ≫ pullback.fst (baseMap y h z) (pullback.fst y (toricMap h)) =
      Spec.map (CommRingCat.ofHom (Algebra.monoidChartTensorBase (alpha y h z) h)))
    (q : Ideal (Algebra.monoidChartTensor (alpha y h z) h)) [q.IsPrime]
    (_hq : q = (Scheme.SpecToEquivOfField Ω _ (zA ≫ eC.inv)).1.asIdeal)
 :
    IsNoetherianRing (baseRing y h z) ∧
    IsNoetherianRing (Localization.AtPrime q) ∧
    Ideal.comap (Algebra.monoidChartTensorBase (alpha y h z) h) q =
      IsLocalRing.maximalIdeal (baseRing y h z) := by sorry

end AlgebraicGeometry
