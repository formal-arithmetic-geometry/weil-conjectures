/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
-/
module

public import Sheaf.Paper.CompletedAdicCoefficientDatum
public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Sheaf.CategoryTheory.Triangulated.DerivedLimitProducts
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact

/-!
# Products of evaluated strict towers

Source: blueprint, `prop-weil-pbc-derived-product-representation`; Stacks 07KC
(blueprint: prop-weil-pbc-derived-product-representation).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

variable (T : Scheme.{u}) {A : Type u} [CommRing A]

/-- Evaluation of a tower complex as a tower of complexes, then localization at each level.
Source: blueprint order 1244 (blueprint: prop-weil-pbc-derived-product-representation). -/
def pbcComplexEvaluation (d : Scheme.AdicCoefficientDatum A) :
    CochainComplex (Scheme.CompletedAdicTowers T d) ℤ ⥤ (ℕᵒᵖ ⥤
    DerivedCategory (Scheme.CompletedAdicModules T d)) :=
  HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
    (Functor.whiskeringRight ℕᵒᵖ (CochainComplex (Scheme.CompletedAdicModules T d) ℤ)
      (DerivedCategory (Scheme.CompletedAdicModules T d))).obj DerivedCategory.Q

/-- Evaluation is exact levelwise, so this functor inverts tower quasi-isomorphisms.
Source: blueprint order 1244; Stacks 015F
(blueprint: prop-weil-pbc-derived-product-representation).
Proof: cohomology of a functor-category complex is computed at each object. Thus a
quasi-isomorphism evaluates to a quasi-isomorphism at each n. Localization sends it to
an isomorphism, and a natural transformation with invertible components is invertible. -/
theorem pbcComplexEvaluation_inverts (d : Scheme.AdicCoefficientDatum A) :
    (HomologicalComplex.quasiIso (Scheme.CompletedAdicTowers T d) (ComplexShape.up ℤ)).IsInvertedBy
      (pbcComplexEvaluation T d) := by
  sorry

/-- The canonical evaluated derived tower, obtained by the localization universal property.
Source: blueprint order 1244 (blueprint: prop-weil-pbc-derived-product-representation). -/
def pbcDerivedEvaluation (d : Scheme.AdicCoefficientDatum A) :
    DerivedCategory (Scheme.CompletedAdicTowers T d) ⥤ (ℕᵒᵖ ⥤
    DerivedCategory (Scheme.CompletedAdicModules T d)) :=
  Localization.lift (pbcComplexEvaluation T d) (pbcComplexEvaluation_inverts T d)
    DerivedCategory.Q


/-- The localization comparison, so evaluation retains the representative's transition maps.
Source: Stacks 05RU; blueprint product statement
(blueprint: prop-weil-pbc-derived-product-representation). -/
def pbcEvaluationFactors (d : Scheme.AdicCoefficientDatum A) :
    DerivedCategory.Q ⋙ pbcDerivedEvaluation T d ≅ pbcComplexEvaluation T d :=
  Localization.fac _ (pbcComplexEvaluation_inverts T d) DerivedCategory.Q

/-- The product fan supplied by a representative tower complex. Its projections are
localized complex projections followed by the specified representative isomorphism.
Source: Stacks 07KC (blueprint: prop-weil-pbc-derived-product-representation). -/
def pbcRepresentativeProductFan (d : Scheme.AdicCoefficientDatum A)
    (M : DerivedCategory (Scheme.CompletedAdicTowers T d))
    (I : CochainComplex (Scheme.CompletedAdicTowers T d) ℤ)
    (e : DerivedCategory.Q.obj I ≅ M) :
    Fan (fun n : ℕ ↦ ((pbcDerivedEvaluation T d).obj M).obj (op n)) :=
  Fan.mk (DerivedCategory.Q.obj (∏ᶜ fun n : ℕ ↦ I.asFunctor.obj (op n))) (fun n ↦
    DerivedCategory.Q.map (Pi.π (fun n : ℕ ↦ I.asFunctor.obj (op n)) n) ≫
      ((pbcEvaluationFactors T d).inv.app I).app (op n) ≫
      ((pbcDerivedEvaluation T d).map e.hom).app (op n))

/-- Countable products in the completed-coefficient derived category exist, and every
K-injective tower resolution represents their product by its termwise product.
A resolution C → I and a representative Q(C) ≅ M supply e by inverting Q(C → I).
Source: Stacks 07KC (blueprint: prop-weil-pbc-derived-product-representation).
Proof: countable module-sheaf products are exact and sectionwise by
lem-weil-proetale-countable-products-exact. Apply lem-weil-derived-limit-products-core
with these exact products. It identifies localization of the product complex with the
product of the localizations of its levels, with the displayed projections. Transport
this limiting fan through pbcEvaluationFactors and the representative isomorphism e.
K-injectivity is allowed but not needed by 07KC, which works for any representatives. -/
theorem pbcDerivedProductRepresentation (d : Scheme.AdicCoefficientDatum A) :
    HasCountableProducts (DerivedCategory (Scheme.CompletedAdicModules T d)) ∧
    ∀ (M : DerivedCategory (Scheme.CompletedAdicTowers T d))
      (I : CochainComplex (Scheme.CompletedAdicTowers T d) ℤ)
      (_hI : I.IsKInjective) (e : DerivedCategory.Q.obj I ≅ M),
      Nonempty (IsLimit (pbcRepresentativeProductFan T d M I e)) := by
  sorry

/-- The countable-product existence part of the representation statement.
Source: Stacks 07KC (blueprint: prop-weil-pbc-derived-product-representation). -/
instance pbcDerived_hasCountableProducts (d : Scheme.AdicCoefficientDatum A) :
    HasCountableProducts (DerivedCategory (Scheme.CompletedAdicModules T d)) :=
  (pbcDerivedProductRepresentation T d).1

end AlgebraicGeometry.ProEtale
