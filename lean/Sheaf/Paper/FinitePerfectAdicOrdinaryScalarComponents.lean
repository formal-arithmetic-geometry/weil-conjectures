/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Z8
-/
module

public import Sheaf.Paper.FinitePerfectAdicScalarCoherence
public import Sheaf.Paper.FinitePerfectAdicOrdinaryScalarModelBase

/-! # Rank-one ordinary scalar comparisons

Source: Stacks Project, Tags 093J and 093M.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
namespace AlgebraicGeometry.Scheme

/-- The ordinary comparison has a coherent rank-one quotient component.

Source: Stacks Project, Tags 093J and 093M; Tag 03CY for the associated module
sheaf.
(blueprint: new-s3-finite-perfect-adic-ordinary-scalar-components)

Proof: identify the constant sections after the etale and pro-etale inverse-image
maps, then use the completed finite-reduction comparison on the free rank-one
quotient.  Restriction along the next quotient is compatible with the two
projection maps, so the resulting family of component isomorphisms commutes on
the rank-one quotient object.  The construction is natural in the chart and
covers zero rings and empty charts.
-/
theorem finitePerfectAdicOrdinaryScalar_components
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (V : X.Etale) (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U) :
    ∃ e : ∀ n : ℕ, finitePerfectAdicOrdinaryScalarSource X d V U W f n ≅
        finitePerfectAdicOrdinaryScalarTarget X d W n,
      ∀ (n : ℕ),
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
              (A ⧸ d.ideal ^ (n + 1))) := by
  sorry

end AlgebraicGeometry.Scheme
