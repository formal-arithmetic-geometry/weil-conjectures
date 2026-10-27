/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y3
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
  substituteInputs substitution transport strictMap scalarSubstitution scalarBeta scalarTransport
  scalarLeft scalarRight ScalarIdentity ScalarComposition ScalarAssociation NaturalSubstitution
  ScalarGood StrictCoherence ScalarLimitImage reduction scalarQuotients
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- Identification of the strict comparison and its coherent completed image.
Source: realization proof steps 2, 3 and 5; Stacks 07A4 and 0D6D
(blueprint: lem-pur-completed-comparison-canonical-identification).

Proof: the equality of the two sequence inverse-image interfaces transports the
generator-normalized cochain pullback tensor comparison. Its tensor generators
uniquely fix it, so it agrees with the recorded sequence cochain comparison.
The descended system comparison satisfies its K-flat normalization equation.
Insert the tensor and pullback primitive realization formulas into the recursive
substitutions at the source and target. Naturality moves each reduction-model
map through the tensor and inverse-image functors. Effective counits cancel
against their inverses; the remaining composite is precisely the defining
canonicalIntegralPullbackTensor composite. Generator normalization also supplies
the strong monoidal, signed symmetry and composition equations for the three
pullbacks. Transport along the same interface equality gives StrictCoherence.
Apply this at both coefficients. Naturality of the descended system comparison,
primitive natural isomorphisms and counits gives NaturalComparison for arbitrary
derived input maps, without choosing representatives for those maps. -/
theorem completedComparisonCanonicalIdentification
    {Z X Y : Scheme.{u}} (h : Z ⟶ X) (f : X ⟶ Y)
    [∀ z : Z, Invertible (l : Z.residueField z)]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (M : Fin 3 → sfIntegralConstructibleCategory l E Y)
    (P : Fin 3 → (integralOperationsGoodComplex l E Y).FullSubcategory)
    (φ : ∀ i : Fin 3, DerivedCategory.Q.obj (P i).obj ≅ (M i).obj)
    (good : GoodExpressions l E h f P)
    (invertible : ∀ {W : Scheme.{u}} (A : StrictQuotient.Expression h f 3 W),
      IsIso (substitution l E P (fun i ↦ (M i).obj) φ good A)) :
    (transport l E P (fun i ↦ (M i).obj) φ good invertible
      (sourceExpression h f) (targetExpression h f)
      (comparison l E f (quotient l E (P 0).obj) (quotient l E (P 1).obj)).hom =
        (canonicalIntegralPullbackTensor l E f (M 0) (M 1)).hom.hom) ∧
    StrictCoherence l E h f ∧ StrictCoherence l L h f ∧
    NaturalComparison l E f ∧ NaturalComparison l L f := by sorry

end WeilConjectures.CompletedQuotient
