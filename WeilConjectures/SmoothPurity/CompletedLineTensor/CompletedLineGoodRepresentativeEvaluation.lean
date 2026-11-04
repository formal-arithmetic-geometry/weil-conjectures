/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedLineTensor.CompletedLineTensorOrdinaryData
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import WeilConjectures.SmoothPurity.CompletedLineTensor.CompletedLineScalarBaseSmul
import WeilConjectures.SmoothPurity.CompletedLineTensor.CompletedLineSheafEvaluationSquare
import WeilConjectures.SmoothPurity.CompletedLineTensor.CompletedLineOrdinaryEvaluation

/-! # Evaluation compatibility on a good representative

Source: blueprint sk-def-sp-tate-twist-locally-free, Proof (3).
(blueprint: lem-pur-completed-line-good-representative-evaluation)
-/

@[expose] public noncomputable section
set_option Elab.async false
attribute [local instance 5000] CategoryTheory.HasSheafify.isRightAdjoint
attribute [local instance 5000] Algebra.toModule
attribute [local irreducible] Padic
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.abSheafify
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.abLocallyBijective
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.siteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [local irreducible] HasDerivedCategory.standard
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
universe t u
open CategoryTheory CategoryTheory.Limits Opposite TensorProduct MonoidalCategory
namespace WeilConjectures
namespace CompletedLineTensor

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : AlgebraicGeometry.Scheme.{t})
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (ι : E →ₐ[ℚ_[l]] F)

/--
The representative-level evaluation square for a good K-flat complex `P`, i.e. the
derived evaluation square at `K = Q(P)`. It is the input of the localization argument of
`ordinary_evaluation_compatibility`.
Source: Stacks 06YY; blueprint
literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-the-trace-map-of-affine-space/sk-prop-an/sk-def-sp-tate-twist-locally-free.md,
Proof (3): an invertible module is
flat, so the line tensor is computed termwise
(blueprint: lem-pur-completed-line-good-representative-evaluation).
Proof: the derived tensors and `epsilon` are `mapDerivedCategory` of the exact sheaf
functors and of `evaluation`, so on `Q(P)` they are `Q` applied termwise
(`factors`, `complex`). The fourth clause of `IsPairNormalized` expresses
`(d.ordinary m).app (Q P)` through the invertible universal counit
`completedScalarCounit` on the K-flat complexes `P` and `T_{L,m} P` and the termwise
complex comparison built from `d.ordinarySheaf m`. Substitute this at `m` and at `-m`
(the complex `T_{L,m} P` is again good, line tensor preserving flat terms). By
naturality of the counit for the termwise map `evaluation_L`, both sides of the
equation become `Q` of termwise maps followed by the same invertible counit. After
cancelling it, the equation is `Q` applied termwise to `completed_sheaf_evaluation_square`.
This argument is carried out for every complex in `ordinary_evaluation_compatibility`,
which we specialize to `K = Q(P)`.
-/
theorem completed_good_representative_evaluation (L : integralTowerModules l E X)
    [L.IsFiniteLocallyFreeOfRank 1] (N : integralTowerModules l F X)
    [N.IsFiniteLocallyFreeOfRank 1]
    (b : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E F ι X) L ≅ N)
    (d : PairData l E X F ι L N) (hd : IsPairNormalized l E X F ι L N b d)
    (m : ℤ) (P : (integralOperationsGoodComplex l E X).FullSubcategory) :
    (d.ordinary (-m)).hom.app ((tensor l E X L m).obj (DerivedCategory.Q.obj P.obj)) ≫
      (tensor l F X N (-m)).map
        ((d.ordinary m).hom.app (DerivedCategory.Q.obj P.obj)) ≫
      (epsilon l F X N m).hom.app
        ((completedDerivedScalarExtension l E F ι X).obj (DerivedCategory.Q.obj P.obj)) =
    (completedDerivedScalarExtension l E F ι X).map
      ((epsilon l E X L m).hom.app (DerivedCategory.Q.obj P.obj)) :=
  ordinary_evaluation_compatibility l E X F ι L N b d hd m (DerivedCategory.Q.obj P.obj)

end CompletedLineTensor
end WeilConjectures
