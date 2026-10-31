/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SixFunctorDatum
public import WeilConjectures.AlgebraicGeometry.SitePerfectComplex
public import WeilConjectures.AlgebraicGeometry.LegacySitePerfectComplex
public import WeilConjectures.AlgebraicGeometry.CoefficientDualModelTransport

/-! # Local invertibility of rational perfect evaluation -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

/-- Perfect local models make the actual rational evaluation locally invertible.
Source: blueprint prop-sf-dualizable-hom, steps 8--10; Stacks Tag 08JJ
(blueprint: lem-sf-rational-evaluation-cover).

Proof: choose the covering and bounded local complex in the site-perfect
predicate. Apply rationalSliceCompletedEvaluation to compare restriction of
the specified evaluation with completed evaluation on each actual slice.
Normalize the global comparison through the integral ambient realization and
rationalization; the tensor-Hom evaluation and symmetry equations identify its
adjunct. For the fixed restricted target, rationalThickEvaluation gives the
thick evaluation locus in the ambient raw scalar localization. It contains the
unit, hence finite sums and the termwise rational retracts in the local model.
Induct on its finite support using brutal-tail distinguished triangles and
shifts of its terms. The localized complex belongs to the locus; transport
along the local model isomorphism proves the stated component invertible.
No constructibility of local terms, or integral lifting of rational retractions,
is used. Empty support is the zero case, and zero-rank retracts cause no exception. -/
theorem rationalEvaluation_cover
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (X : SixFunctorSpace D)
    (A : SixFunctorCoefficientClosedModels C.l E X.obj.left)
    (K M : (⊤ : ObjectProperty
      (sfRationalConstructibleCategory C.l E X.obj.left)).FullSubcategory)
    (hK : IsSfRationalCoefficientSitePerfect C.l E X.obj.left K.obj) :
    ∀ V : X.obj.left.ProEt, ∃ R : Sieve V,
      R ∈ Scheme.ProEt.topology X.obj.left V ∧
      ∀ (U : X.obj.left.ProEt) (f : U ⟶ V), R f →
        IsIso ((IntegralOnSlice.restrictionRational C.l E X.obj.left
          (U := none) (V := some U) PUnit.unit).map
          ((CoefficientDualModels.stageInclusion C.l E X.obj.left).map
            ((⊤ : ObjectProperty
              (sfRationalConstructibleCategory C.l E X.obj.left)).ι.map
              (ringedSiteDualEvaluationLeft A.rational.closed A.rational.symmetric
                A.rational.closed.monoidal.tensorUnit (Iso.refl _) K M)))) := by sorry

end WeilConjectures
