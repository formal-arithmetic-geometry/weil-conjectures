/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedLineTensor.CompletedLineTensorOrdinaryData
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
public import WeilConjectures.SmoothPurity.CompletedLineTensor.CompletedLineGoodRepresentativeEvaluation

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

/-- The normalized ordinary scalar comparison respects signed-line evaluation.
Source: Stacks 03EL, 03EO, 06YY; blueprint Proof (3), inverse-pair compatibility
(blueprint: lem-pur-completed-line-ordinary-evaluation).
The representative square is supplied on the good K-flat localization, and full
faithfulness of its localization transports it to every derived object. -/
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
      (epsilon l F X N m).hom.app
        ((completedDerivedScalarExtension l E F ι X).obj K) =
    (completedDerivedScalarExtension l E F ι X).map
      ((epsilon l E X L m).hom.app K) := by
  classical
  let lhs : (tensor l E X L m ⋙ tensor l E X L (-m)) ⋙
      completedDerivedScalarExtension l E F ι X ⟶
      completedDerivedScalarExtension l E F ι X :=
    Functor.whiskerLeft (tensor l E X L m) (d.ordinary (-m)).hom ≫
      Functor.whiskerRight (d.ordinary m).hom (tensor l F X N (-m)) ≫
      Functor.whiskerLeft (completedDerivedScalarExtension l E F ι X)
        (epsilon l F X N m).hom
  let rhs : (tensor l E X L m ⋙ tensor l E X L (-m)) ⋙
      completedDerivedScalarExtension l E F ι X ⟶
      completedDerivedScalarExtension l E F ι X :=
    Functor.whiskerRight (epsilon l E X L m).hom
      (completedDerivedScalarExtension l E F ι X)
  let Λ := integralOperationsGoodLocalization l E X
  let QI := (HomologicalComplex.quasiIso (integralTowerModules l E X) (.up ℤ)).inverseImage
    (integralOperationsGoodComplex l E X).ι
  let : Λ.IsLocalization QI := integralOperationsGoodLocalization_isLocalization l E X
  let ff := Localization.fullyFaithfulWhiskeringLeft Λ QI
    (DerivedCategory (integralTowerModules l F X))
  have hh : lhs = rhs := ff.map_injective (by
    apply NatTrans.ext
    funext P
    exact completed_good_representative_evaluation l E X F ι L N b d hd m P)
  exact congrArg (fun n ↦ n.app K) hh

end CompletedLineTensor
end WeilConjectures
