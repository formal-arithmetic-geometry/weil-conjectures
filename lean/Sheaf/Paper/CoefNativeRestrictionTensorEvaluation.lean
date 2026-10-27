/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CoefOpenTensorEvaluationData

/-! # Evaluation of the normalized restriction tensor comparison

Source: Stacks 07A4 and 0941; support-open-tensor steps 5--6.
(blueprint: lem-coef-native-restriction-tensor-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
  HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CoefSupportOpenTensor

attribute [-instance] SemilinearSections.hasDerived SemilinearSections.moduleAbelian
  SemilinearSections.abelianSheafify SemilinearSections.locallyBijective
  SemilinearSections.sequenceSmall SemilinearSections.sliceSmall

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Evaluation commutes with the tensor comparison for open inverse image.
This concerns only restriction and tensor, before taking an open-extension mate.
Source: Stacks 07A4, sites-cohomology-lemma-pullback-tensor-product;
Stacks 03EK, sites-modules-section-tensor-product;
support-open-tensor steps 5--6 and the recorded evaluation tensor normalization.
(blueprint: lem-coef-native-restriction-tensor-evaluation).

Proof: choose flat-term K-flat representatives of M and N. On ordinary module
sheaves, precompose the two maps with inverse image of the pure-tensor section
and the inverse-image adjunction unit. The restrictionPure equations for O and
On, the unit normalization of moduleEvalG, and the pure-tensor normalization of
coefficientEvaluationTensorIso identify both outputs with the tensor of the two
pulled, evaluated sections. The inverse-image adjunction and tensor
sheafification show equality of these ordinary maps. On each total summand of
bidegree (a,b), use the same ordinary equality; evaluation preserves direct sums
and the signed differential, so the cochain maps agree. The restrictionModel
fields and evaluationTensor_normalization identify their localizations with the
two displayed composites. Cancel the tensor-model and exact-functor
factorization isomorphisms. Finally naturality along the resolving
quasi-isomorphisms gives the square for M and N. This uses neither an open
tensor projection nor its evaluation equation. Identity and empty opens, zero
objects, and degree n = 0 obey the same unit and generator equations. -/
theorem nativeRestrictionTensorEvaluation {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j]
    (SX : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (SZ : CoefficientDerivedSystemCalculus.{u, u} l E Z)
    (O : SystemOpenModel l E j SX.toCoefficientDerivedSystemTensors
      SZ.toCoefficientDerivedSystemTensors)
    (n : ℕ)
    (On : FiniteOpenModel l E j SX.toCoefficientDerivedSystemTensors
      SZ.toCoefficientDerivedSystemTensors n)
    (M N : coefficientSequenceDerived.{u, u} l E Z) :
    let θ := @OpenTensorModel.restriction.{u+1, u, u} (ℕ × Z.ProEt) _
      (ProEtale.VaryingRing.sequenceSiteSmall Z)
      (coefficientSequenceTopology (ProEt.topology Z))
      (coefficientSequenceCommRingSheaf.{u, u} l E Z)
      SZ.systemClosed SZ.systemTensorModel
      (ℕ × X.ProEt) _ (ProEtale.VaryingRing.sequenceSiteSmall X)
      (coefficientSequenceTopology (ProEt.topology X))
      (coefficientSequenceCommRingSheaf.{u, u} l E X)
      SX.systemClosed SX.systemTensorModel
      (ProEtale.VaryingRing.extension (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) j)
      (ProEtale.VaryingRing.pull (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) j)
      (ProEtale.VaryingRing.extensionAdditive
        (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) j)
      (ProEtale.VaryingRing.extensionLimits
        (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) j)
      (ProEtale.VaryingRing.extensionColimits
        (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) j)
      (ProEtale.VaryingRing.pullAdditive
        (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) j)
      (ProEtale.VaryingRing.pullLimits
        (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) j)
      (ProEtale.VaryingRing.pullColimits
        (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) j)
      (ProEtale.VaryingRing.moduleJAdj (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) j)
      (ProEtale.VaryingRing.baseChange j) (pullSection l E j) O
    let ψ := @OpenTensorModel.restriction.{u+1, u, u} Z.ProEt _
      (ProEtale.VaryingRing.siteSmall Z) (ProEt.topology Z)
      (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) Z)
      (SZ.finiteClosed n) (SZ.finiteTensorModel n)
      X.ProEt _ (ProEtale.VaryingRing.siteSmall X) (ProEt.topology X)
      (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) X)
      (SX.finiteClosed n) (SX.finiteTensorModel n)
      (ProEtale.StrictTower.moduleJ (compactSupportSystemLevel l E n) j)
      (ProEtale.StrictTower.modulePullback (compactSupportSystemLevel l E n) j)
      (ProEtale.StrictTower.moduleJ_additive (compactSupportSystemLevel l E n) j)
      (ProEtale.StrictTower.moduleJ_finiteLimits (compactSupportSystemLevel l E n) j)
      (ProEtale.StrictTower.moduleJ_finiteColimits (compactSupportSystemLevel l E n) j)
      (proEtaleRingModulePullback_additive j
        (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) Z)
        (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) X)
        (ProEtale.StrictTower.constantRingIso (compactSupportSystemLevel l E n) j))
      (proEtaleRingModulePullback_preservesFiniteLimits j
        (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) Z)
        (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) X)
        (ProEtale.StrictTower.constantRingIso (compactSupportSystemLevel l E n) j))
      (proEtaleRingModulePullback_preservesFiniteColimits j
        (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) Z)
        (ProEtale.StrictTower.coefficients (compactSupportSystemLevel l E n) X)
        (ProEtale.StrictTower.constantRingIso (compactSupportSystemLevel l E n) j))
      (ProEtale.StrictTower.moduleJAdj (compactSupportSystemLevel l E n) j)
      (proEtaleBaseChange j) (finitePullSection l E j n) On
    (coefficientSequenceDerivedEvaluation.{u, u} l E X n).map
        (θ.hom.app (M, N)) ≫
      (SX.evaluationTensor n).hom.app
        ((ProEtale.VaryingRing.G (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) j).obj M,
         (ProEtale.VaryingRing.G (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) j).obj N) ≫
      (SX.finiteClosed n).tensor.map (Prod.mkHom
        ((ProEtale.VaryingRing.evalG (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) j n).hom.app M)
        ((ProEtale.VaryingRing.evalG (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) j n).hom.app N)) =
    (ProEtale.VaryingRing.evalG (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) j n).hom.app
          (SZ.systemClosed.tensor.obj (M, N)) ≫
      (ProEtale.StrictTower.modulePullback (compactSupportSystemLevel l E n)
        j).mapDerivedCategory.map ((SZ.evaluationTensor n).hom.app (M, N)) ≫
      ψ.hom.app
        ((coefficientSequenceDerivedEvaluation.{u, u} l E Z n).obj M,
         (coefficientSequenceDerivedEvaluation.{u, u} l E Z n).obj N) := by
  sorry

end WeilConjectures.CoefSupportOpenTensor
