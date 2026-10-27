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

/-- Scalar quotient closure and the limit image of the two strict scalar routes.
Source: realization proof steps 6 and 7; Stacks 03EL, 07A4 and 0941
(blueprint: lem-pur-completed-comparison-scalar-limit-image).

Proof: coefficient-extension reduction gives the actual scalar quotient systems.
On flat-term K-flat representatives, balanced association sends (x tensor a) tensor b
to x tensor iota(a)*b, with insertion-of-one inverse. This commutes with quotient
transitions and restrictions. Induct over ScalarGenerated, using tensor and
constant-coefficient inverse-image preservation to obtain flat K-flat normalized
expressions. The normalized scalar model realizes the canonical completed scalar
functor; its counit formula is exactly scalarSubstitution. Induction on the same
expression syntax identifies the L realization with scalarBeta and proves its
invertibility. The strict coefficient square sends b tensor (x tensor y) by both
routes to (b tensor x) tensor (1 tensor y); balancing and local generation prove
equality. Apply the total-limit functor. Expand the normalized scalar, tensor and
pullback realization equations and cancel successive inverse substitutions. The
L comparison becomes the canonical completed comparison by its representative
normalization. The two resulting equations are exactly the two composites in
ScalarLimitImage for each of the equal strict routes. No finite coefficient-map
flatness is used, so ramified extensions are included. -/
theorem completedComparisonScalarLimitImage
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
    (∀ (d : Bool) (W : Scheme.{u}) (A : ScalarComplex l E L d W),
      ScalarGenerated l E L ι h f (fun i ↦ quotient l E (P i).obj) d W A →
        ScalarGood l E L d W A) ∧
    ScalarLimitImage l E L ι h f M P φ good invertible := by sorry

end WeilConjectures.CompletedQuotient
