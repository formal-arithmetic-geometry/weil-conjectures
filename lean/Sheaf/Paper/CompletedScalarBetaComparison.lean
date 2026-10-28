/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H9
-/
module

public import Sheaf.Paper.CompletedComparisonQuotientRealizationDefs

/-! # Quotient realization steps

Source: integral comparison proof, quotient normalization and coherent substitution.
-/


@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.SemilinearSections.abelianSheafify
attribute [-instance] WeilConjectures.SemilinearSections.locallyBijective
attribute [-instance] WeilConjectures.finiteSystemSequenceSmall
attribute [-instance] AlgebraicGeometry.ProEtale.VaryingRing.sequenceSiteSmall
attribute [instance 4000] SheafOfModules.monoidalCategory
attribute [instance 4000] HomologicalComplex.monoidalCategory

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open MonoidalCategory
namespace WeilConjectures.CompletedQuotient
universe u

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible] tensorSubstitution comparison pullBridge pullSubstitution
  substitution transport strictMap scalarSubstitution scalarBeta scalarTransport
  scalarLeft scalarRight ScalarIdentity ScalarComposition ScalarAssociation NaturalSubstitution
  ScalarGood StrictCoherence ScalarLimitImage reduction
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local implicit_reducible] value expression IntegralCoherence.value scalarQuotients

/-- The recursive L substitution intertwines the strict comparison with the canonical one.
Source: Stacks 07A4 and 0941; quotient-realization proof steps 2, 3 and 6
(blueprint: lem-pur-completed-scalar-beta-comparison).

Proof: use the coherent scalar quotients of the prescribed representatives as the
three leaves. Their scalar substitution is the scalar realization followed by
scalar change of the E coherent reduction and the fixed K-flat scalar counit.
Expand the recursion at pullF(tensor(input 0,input 1)) and at the tensor of the
two pullF inputs. The defining normalization square of the descended system
pullback/tensor comparison identifies its cochain model with comparison at L.
Naturality moves the two leaf reduction maps through that square. Insert the
primitive tensor and pullback realizations in canonicalIntegralPullbackTensor.
Counit naturality and the adjunction triangle identities cancel their intermediate
reconstruction factors. The remaining factors are exactly the two displayed
recursive substitutions. Work in whole coefficient systems before total limit,
so every horizontal transition and arbitrary choice of representative is retained.
No invertibility of these recursive substitutions is used in this equation;
zero inputs, identity coefficients and ramified extensions obey the same formulas. -/
theorem completedScalarBetaComparison
    {Z X Y : Scheme.{u}} (h : Z ⟶ X) (f : X ⟶ Y)
    [∀ z : Z, Invertible (l : Z.residueField z)]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (M : Fin 3 → sfIntegralConstructibleCategory l E Y)
    (P : Fin 3 → (integralOperationsGoodComplex l E Y).FullSubcategory)
    (φ : ∀ i : Fin 3, DerivedCategory.Q.obj (P i).obj ≅ (M i).obj)
    (good : GoodExpressions l E h f P)
    {ρY : IntegralComparisonRoosModel l L Y}
    (SY : IntegralComparisonScalarModel l E L ι Y (pullbackTensorCalculus l E Y) ρY)
    (goodL : ∀ {W : Scheme.{u}} (A : StrictQuotient.Expression h f 3 W),
      StrictQuotient.SystemGood l L (strictValue l L (scalarQuotients l E L ι P) A)) :
    scalarBeta l E L ι M P φ good SY goodL (sourceExpression h f) ≫
      (coefficientSequenceLimit l L X).map (DerivedCategory.Q.map
        (comparison l L f ((scalarQuotients l E L ι P) 0)
          ((scalarQuotients l E L ι P) 1)).hom) =
    (canonicalIntegralPullbackTensor l L f
      ((sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι Y).obj (M 0))
      ((sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι Y).obj (M 1))).hom.hom ≫
      scalarBeta l E L ι M P φ good SY goodL (targetExpression h f) := by sorry

end WeilConjectures.CompletedQuotient
