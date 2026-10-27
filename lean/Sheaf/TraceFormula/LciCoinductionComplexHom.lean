/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q29
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Sheaf.TraceFormula.LciCoinductionOrdinaryHom
public import Sheaf.AlgebraicGeometry.SheafExt
public import WeilConjectures.Algebra.Homology.HomComplexComponents

/-! # The canonical underlying Hom comparison for a Koszul chart

Source: Stacks Project, Tags 0BUZ, 0BV1 and 0A95
(blueprint: def-trf-lci-coinduction-complex-hom).
The comparison is fixed on K-injective representatives by the ordinary evaluation-normalized
coinduction comparison and projection onto source degree zero in the Hom complex.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option Elab.async false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

variable [∀ Z : RingedSpace.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z))]

attribute [local instance] LciKoszulDuality.schemeDerived LciKoszulDuality.imageRingDerived
  LciKoszulDuality.imageRingInjectives

/-- Termwise coinduction followed by scalar restriction.
Source: Stacks 0BUZ (blueprint: def-trf-lci-coinduction-complex-hom). -/
def coinductionComplexFunctor {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ}
    (T : LciKoszulDuality.Chart f d) (h : PolynomialChartExactData T.chart.i) :
    CochainComplex T.chart.P.Modules ℤ ⥤ CochainComplex T.chart.P.Modules ℤ :=
  letI : (polynomialChartCoinduction T.chart.i).Additive := h.additive
  letI : T.scalars.Additive :=
    SheafOfModules.instAdditiveRestrictScalars T.chart.i.toRingCatSheafHom
  (polynomialChartCoinduction T.chart.i).mapHomologicalComplex (.up ℤ) ⋙
    T.scalars.mapHomologicalComplex (.up ℤ)

/-- The complex comparison with the formula fixing every component of its inverse.
Source: Stacks 0BUZ, 0A8X (blueprint: def-trf-lci-coinduction-complex-hom). -/
structure CoinductionComplexComparison {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ}
    (T : LciKoszulDuality.Chart f d) (h : PolynomialChartExactData T.chart.i) where
  iso : coinductionComplexFunctor T h ≅
    (homComplexFunctor (R := T.chart.P.sheaf)).obj
      (op ((CochainComplex.singleFunctor _ 0).obj T.quotientModule))
  projection : ∀ (I : CochainComplex T.chart.P.Modules ℤ) (n : ℤ),
    (iso.inv.app I).f n =
      homComplexπ (R := T.chart.P.sheaf)
        ((CochainComplex.singleFunctor _ 0).obj T.quotientModule) I n 0 n (zero_add n) ≫
          T.ordinaryHomComparison.inv.app (I.X n)

/-- The evaluation-normalized ordinary comparison gives the canonical complex comparison.
Source: Stacks 0BUZ, 0A8X (blueprint: def-trf-lci-coinduction-complex-hom).
Proof: compose the inverse degree-zero Hom-complex projection with the termwise
ordinary evaluation comparison. The projection is a natural chain isomorphism because
all other factors vanish. The ordinary comparison is natural in the coefficient module,
so its termwise maps commute with differentials and are inverse degreewise. The displayed
formula specifies every component of the inverse, and hence determines the isomorphism. -/
theorem exists_coinductionComplexComparison {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ}
    (T : LciKoszulDuality.Chart f d) (h : PolynomialChartExactData T.chart.i) :
    Nonempty (CoinductionComplexComparison T h) := by
  sorry

/-- The canonical complex comparison selected with its determining formula.
Source: Stacks 0BUZ, 0A8X (blueprint: def-trf-lci-coinduction-complex-hom). -/
@[no_expose] def coinductionComplexIso {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ}
    (T : LciKoszulDuality.Chart f d) (h : PolynomialChartExactData T.chart.i) :=
  (Classical.choice (exists_coinductionComplexComparison T h)).iso


end AlgebraicGeometry
