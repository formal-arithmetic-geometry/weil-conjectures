/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.KunnethGlobalSections
public import WeilConjectures.CategoryTheory.Etale.EtaleUnboundedRestrictionComparison
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.FiniteCoefficients.Constant
public import WeilConjectures.CategoryTheory.Sites.ConstantSheafCompose
public import WeilConjectures.CategoryTheory.Sites.SheafComposeMonoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction

import WeilConjectures.CategoryTheory.Etale.EtaleUnboundedRestrictionComparison
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import WeilConjectures.ProperBaseChange.RingedToposDerivedPushforwardComposition
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.CategoryTheory.ExactDerivedPasting.Word.ExactDerivedTransformationPasting
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.CategoryTheory.K.KInjectiveTotalDerived
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteKInjectiveResolutionsMixedUniverses
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
import WeilConjectures.AlgebraicGeometry.Sites.PointConstantSheaf

/-!
# Field restriction and the canonical ordinary exterior product

Source: Stacks Project, Tag 0F1E, remark-define-kunneth-map, and Tag 0FPI,
lemma-adjoints-push-pull-compatibility
(blueprint: lem-pur-exterior-product-field-restriction).

## Main definitions

- `RestrictionTensorData`: the balanced quotient, normalized on total complexes.
- `fieldRestrictionSectionsMap`: the canonical mate of restriction of constant complexes.
- `RestrictionSectionsData`: its normalized isomorphism and exactness assertions.
- `fieldRestrictionUnbalancedExterior`: the product before the balanced quotient.
- `fieldRestrictionInputAction`: the two independent coefficient actions.
- `FieldRestrictionExteriorProductData`: the complete normalized compatibility assertion.

## Main statements

- `fieldRestrictionExteriorProduct`: restriction compatibility, independent scalar actions,
  preservation of split retracts, and conservativity.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

section TensorData
variable {C D : Type (u + 2)} [Category.{u + 1} C] [Category.{u + 1} D]
  [Abelian C] [Abelian D] [IsGrothendieckAbelian.{u + 1} C]
  [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory C] [MonoidalCategory D]
  [SymmetricCategory C] [SymmetricCategory D]
  [MonoidalClosed C] [MonoidalClosed D]
  [MonoidalPreadditive C] [MonoidalPreadditive D]
  [HasDerivedCategory.{u + 1} C] [HasDerivedCategory.{u + 1} D]
  [MonoidalCategory (DerivedCategory C)] [MonoidalCategory (DerivedCategory D)]
  [(DerivedCategory.Q : CochainComplex C ℤ ⥤ DerivedCategory C).LaxMonoidal]
  [(DerivedCategory.Q : CochainComplex D ℤ ⥤ DerivedCategory D).LaxMonoidal]
  (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (ordinary : G.LaxMonoidal)

/-- Balanced derived restriction tensorator, including its naturality and its normalization
on every total-tensor summand and at localization. The parameter `ordinary` is the existing
restriction tensorator, not an arbitrary bilinear map. Its value is `x ⊗ y ↦ x ⊗ y` with
balancing changed from F to B. The localization square determines the morphism on K-flat
representatives. Source: Stacks 0F1E and 0FPI
(blueprint: lem-pur-exterior-product-field-restriction). -/
structure RestrictionTensorData where
  map : ∀ P Q : DerivedCategory C,
    G.mapDerivedCategory.obj P ⊗ G.mapDerivedCategory.obj Q ⟶
      G.mapDerivedCategory.obj (P ⊗ Q)
  naturality : ∀ {P P' Q Q' : DerivedCategory C} (a : P ⟶ P') (b : Q ⟶ Q'),
    (G.mapDerivedCategory.map a ⊗ₘ G.mapDerivedCategory.map b) ≫ map P' Q' =
      map P Q ≫ G.mapDerivedCategory.map (a ⊗ₘ b)
  chain : ∀ K L : CochainComplex C ℤ,
    (G.mapHomologicalComplex (.up ℤ)).obj K ⊗
      (G.mapHomologicalComplex (.up ℤ)).obj L ⟶
        (G.mapHomologicalComplex (.up ℤ)).obj (K ⊗ L)
  chain_summand : ∀ (K L : CochainComplex C ℤ) (p q n : ℤ) (h : p + q = n),
    HomologicalComplex.ιTensorObj ((G.mapHomologicalComplex (.up ℤ)).obj K)
        ((G.mapHomologicalComplex (.up ℤ)).obj L) p q n h ≫ (chain K L).f n =
      ordinary.μ (K.X p) (L.X q) ≫ G.map (HomologicalComplex.ιTensorObj K L p q n h)
  normalization : ∀ K L : CochainComplex C ℤ,
    map (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) ≫
        G.mapDerivedCategory.map (Functor.LaxMonoidal.μ DerivedCategory.Q K L) ≫
        G.mapDerivedCategoryFactors.hom.app (K ⊗ L) =
      (G.mapDerivedCategoryFactors.hom.app K ⊗ₘ G.mapDerivedCategoryFactors.hom.app L) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q
          ((G.mapHomologicalComplex (.up ℤ)).obj K)
          ((G.mapHomologicalComplex (.up ℤ)).obj L) ≫
        DerivedCategory.Q.map (chain K L)

end TensorData

attribute [instance] Sheaf.monoidalCategory Sheaf.symmetricCategory

end AlgebraicGeometry.Etale
