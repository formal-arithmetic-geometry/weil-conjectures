/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import Sheaf.Paper.GeneralChartComparisons

/-! # The standing counit comparison for charts -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting.ChartComparisons

/-- The published exceptional composition and normalized etale comparison compose
to the source-etale comparison, without an orientation choice.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-orientation/sk-prop-sp-orientation-charts.proof.md, Step 3, and
sk-prop-sp-composition/thm-pur-composition-coherence.proof.md, Step 1
(blueprint: lem-pur-chart-exceptional-counit-equation).

Proof: the constant coefficient complex and its smooth exceptional image are bounded
constructible. Thus they have bounded-below etale antecedents, and the support images
in the two standing Hom bijections also have etale origin. Expand the definition of
standingExceptionalComposition: it is the successive transpose of compact-support
composition followed by the composite-map counit. Comparison of the two Hom chains
identifies this transpose with the conjugate of the normalized ordinary etale
compact-support compositor. Substitute the etale sum/evaluation adjunction in the
outer factor. Uniqueness of its counit-normalized right adjoint identifies that
factor with chartEtaleIdentification. Naturality of the comparison unit cancels
its inserted unit isomorphisms, leaving exactly diagonalEtaleLocality and the two
diagonalDualizingComparison factors, which define epsilon. -/
theorem chart_exceptional_counit_equation (P : PurityFiniteSetting.{u})
    {V : Scheme.{u}} [IsAffine V] {d : ℕ}
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    {C B : Chart V d} (e : Map C B)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :
    composition P B.proj aV e.hom ≫ (rho P B.proj aV e.hom N).hom =
      (epsilon P B.proj aV e.hom N).hom := by
  sorry

end WeilConjectures.PurityFiniteSetting.ChartComparisons
