/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Z8
-/
module

public import Sheaf.Paper.FinitePerfectAdicScalarCoherence
public import Sheaf.Paper.FinitePerfectAdicOrdinaryScalarModelBase

/-! # Extension of the ordinary scalar comparison from the rank-one quotient

Source: Stacks Project, Tags 093J, 093M and 03CY.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
namespace AlgebraicGeometry.Scheme

/-- A rank-one ordinary scalar comparison extends to every quotient module.

Source: Stacks Project, Tags 093J and 093M; Tag 03CY for finite presentations.
(blueprint: new-s3-finite-perfect-adic-ordinary-scalar-compatibility)

Proof: both ordinary functors are exact and preserve finite coproducts.  A
finite presentation of a quotient module by free modules reduces the desired
square to the rank-one square on its generators; the completed projection
formula identifies the two maps there.  Cokernels and naturality then descend
the equality to the presented module.  The same argument handles zero modules
and empty charts.
-/
theorem finitePerfectAdicOrdinaryScalar_compatibility
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (V : X.Etale) (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U)
    (e : ∀ n : ℕ, finitePerfectAdicOrdinaryScalarSource X d V U W f n ≅
      finitePerfectAdicOrdinaryScalarTarget X d W n)
    (hunit : ∀ (n : ℕ),
      (e (n + 1)).hom.app
          ((ModuleCat.restrictScalars
            (Ideal.Quotient.factorPowSucc d.ideal (n + 1))).obj
            (ModuleCat.of (A ⧸ d.ideal ^ (n + 1))
              (A ⧸ d.ideal ^ (n + 1)))) ≫
        (finitePerfectAdicOrdinaryScalarTargetStep X d W n).hom.app
          (ModuleCat.of (A ⧸ d.ideal ^ (n + 1))
            (A ⧸ d.ideal ^ (n + 1))) =
      (finitePerfectAdicOrdinaryScalarSourceStep X d V U W f n).hom.app
          (ModuleCat.of (A ⧸ d.ideal ^ (n + 1))
            (A ⧸ d.ideal ^ (n + 1))) ≫
        (e n).hom.app
          (ModuleCat.of (A ⧸ d.ideal ^ (n + 1))
            (A ⧸ d.ideal ^ (n + 1)))) :
    ∀ (n : ℕ) (N : ModuleCat.{t} (A ⧸ d.ideal ^ (n + 1))),
      (e (n + 1)).hom.app
          ((ModuleCat.restrictScalars
            (Ideal.Quotient.factorPowSucc d.ideal (n + 1))).obj N) ≫
        (finitePerfectAdicOrdinaryScalarTargetStep X d W n).hom.app N =
      (finitePerfectAdicOrdinaryScalarSourceStep X d V U W f n).hom.app N ≫
        (e n).hom.app N := by
  sorry

end AlgebraicGeometry.Scheme
