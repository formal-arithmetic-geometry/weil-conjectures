/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedLineTensor.CompletedLineTensorOrdinaryData
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison

/-! # Ordinary signed-line scalar evaluation

Source: blueprint sk-def-sp-tate-twist-locally-free, Proof (3), evaluation compatibility.
(blueprint: lem-pur-completed-line-ordinary-evaluation)

The normalized ordinary comparisons preserve evaluation before completion. This is
the ordinary square used to prove the completed evaluation square by conjugation.
-/

@[expose] public noncomputable section
set_option Elab.async false
attribute [local instance 5000] CategoryTheory.HasSheafify.isRightAdjoint
attribute [local instance 5000] Algebra.toModule
attribute [local irreducible] Padic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
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
open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
namespace WeilConjectures
namespace CompletedLineTensor

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  completedIntegralCommRingSheafUnrestricted completedCoefficientMap
  completedOrdinaryScalarExtension completedDerivedScalarExtension
  completedScalarCounit completedScalarTensorSection integralScalarExtensionOfUniverses
  completedScalarChangeData completedOrdinaryScalarComplex

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : AlgebraicGeometry.Scheme.{t})
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (ι : E →ₐ[ℚ_[l]] F)

/-- The ordinary scalar comparison respects the specified signed-line evaluation.
Source: Stacks 03EL, 03EO, 06YY; blueprint Proof (3), inverse-pair compatibility
(blueprint: lem-pur-completed-line-ordinary-evaluation).
Proof: first check the ordinary sheaf square on sections. The two scalar-line
comparisons move the two line factors past the scalar factor. Evaluation then
multiplies by the image of their pairing. For positive exponents this is precisely
IsPairNormalized's negative pairing clause; for negative exponents interchange the
paired factors, and for zero use multiplication. The defining evaluation formula
identifies the other path with scalar extension of evaluation. Sheafified tensor
generators determine these maps. Apply the square termwise to a flat-term K-flat
representative. Exact line tensor preserves these representatives. Substitute the
universal-counit normalizations of the two ordinary comparisons and the exact
localization comparisons of evaluation. Naturality and cancellation of the invertible
K-flat counits give the derived square. Every derived object has such a resolution,
so naturality transports the equality to every unbounded object. This argument uses
ordinary derived extension only, with no completeness assumption. -/
theorem ordinary_evaluation_compatibility (L : integralTowerModules l E X)
    [L.IsFiniteLocallyFreeOfRank 1] (N : integralTowerModules l F X)
    [N.IsFiniteLocallyFreeOfRank 1]
    (b : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E F ι X) L ≅ N)
    (d : PairData l E X F ι L N) (hd : IsPairNormalized l E X F ι L N b d)
    (m : ℤ) (K : DerivedCategory (integralTowerModules l E X)) :
    (d.ordinary (-m)).hom.app ((tensor l E X L m).obj K) ≫
      (tensor l F X N (-m)).map
        ((d.ordinary m).hom.app K) ≫
      (epsilon l F X N m).hom.app ((completedDerivedScalarExtension l E F ι X).obj K) =
    (completedDerivedScalarExtension l E F ι X).map
      ((epsilon l E X L m).hom.app K) := by sorry

end CompletedLineTensor
end WeilConjectures
