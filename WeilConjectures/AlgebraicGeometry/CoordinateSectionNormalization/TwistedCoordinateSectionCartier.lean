/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoordinateSectionNormalization.TwistedCoordinateSectionMaps
public import WeilConjectures.AlgebraicGeometry.CoordinateSectionNormalization.TwistedCoordinateSectionCoprojection
public import WeilConjectures.AlgebraicGeometry.CoordinateSectionNormalization.TwistedCoordinateSectionProjective
public import WeilConjectures.AlgebraicGeometry.Cartier.CartierKummerMap

/-!
# Coordinate-section Cartier realization at every root exponent

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
cor-pur-affine-space-zero-section-purity.proof.md, rank-one supported Cartier normalization
(blueprint: def-pur-coordinate-section-cartier-realization).

The source comparison uses exact closed direct image and the exact site comparison.
One supported-unit-normalized source isomorphism works for every annihilating root exponent.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CoordinateSectionNormalization

open AffineLinePurity

variable (T : Scheme.{u}) (P : WeilConjectures.PurityFiniteSetting.{u})

/-- The canonical derived source comparison attached to the specified underived `α`.
It first uses exact closed direct image, then the exact site/single comparison, then `α`.
Source: blueprint cor-pur-affine-space-zero-section-purity.proof.md, Cartier comparison
(blueprint: def-pur-coordinate-section-cartier-realization). -/
def cartierSource
    (α : (comparisonUpperStar (ModuleCat.{u + 1} (Ring P))
        (AffineSpace PUnit.{u + 1} T)).obj
          ((Etale.lowerStar (ModuleCat.{u + 1} (Ring P)) (sectionMap T)).obj
            (Etale.ordinaryFiniteConstant (Ring P) T)) ≅
      Etale.cartierSupported P.coefficients.l P.extension (P.level - 1) (sectionMap T)) :
    (VectorIntegrationSite.comparison (Ring P) (AffineSpace PUnit.{u + 1} T)).obj
        ((closedImage (Ring P) T).obj (Etale.ordinaryFiniteUnit (Ring P) T)) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        (Etale.cartierSupported P.coefficients.l P.extension (P.level - 1) (sectionMap T)) :=
  (VectorIntegrationSite.comparison (Ring P) (AffineSpace PUnit.{u + 1} T)).mapIso
      ((Etale.lowerStar (ModuleCat.{u + 1} (Ring P))
        (sectionMap T)).singleFunctorCompRightDerivedFunctorIso.app
          (Etale.ordinaryFiniteConstant (Ring P) T)) ≪≫
    ((comparisonUpperStar (ModuleCat.{u + 1} (Ring P))
      (AffineSpace PUnit.{u + 1} T)).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso α

/-- The supported Cartier arrow at every allowed root exponent realizes the one published
pro-etale Cartier arrow. The same `α` is fixed by the actual supported constant unit.
Source: blueprint cor-pur-affine-space-zero-section-purity.proof.md, rank-one normalization
and finite etale-origin transport (blueprint: def-pur-coordinate-section-cartier-realization).
-/
def CartierRealization (aT : T ⟶ Spec (.of P.field.k))
    (hI : (sectionMap T).ker.IsInvertible) : Prop :=
  ∃ α : (comparisonUpperStar (ModuleCat.{u + 1} (Ring P))
      (AffineSpace PUnit.{u + 1} T)).obj
        ((Etale.lowerStar (ModuleCat.{u + 1} (Ring P)) (sectionMap T)).obj
          (Etale.ordinaryFiniteConstant (Ring P) T)) ≅
        Etale.cartierSupported P.coefficients.l P.extension (P.level - 1) (sectionMap T),
    (comparisonUpperStar (ModuleCat.{u + 1} (Ring P))
        (AffineSpace PUnit.{u + 1} T)).map
          (Etale.supportedConstantUnit (Ring P) (sectionMap T)) ≫ α.hom =
      Etale.cartierConstantComparison (Ring P) (AffineSpace PUnit.{u + 1} T) ≫
        Etale.cartierSupportedUnit P.coefficients.l P.extension (P.level - 1)
          (sectionMap T) ∧
    ∀ (b : ℕ) (hA : ((P.coefficients.l ^ (b + 1) : ℕ) : Ring P) = 0),
      (VectorIntegrationSite.comparison (Ring P) (AffineSpace PUnit.{u + 1} T)).map
          (ordinarySupported (Ring P) T (P.coefficients.l ^ (b + 1))
            (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) hA
            (by simpa only [Nat.cast_pow] using
              (primeUnit P (AffineSpace PUnit.{u + 1} T)
                ((AffineSpace PUnit.{u + 1} T ↘ T) ≫ aT)).pow (b + 1)) hI) ≫
        (VectorIntegrationSite.twistDerived P.coefficients.l P.extension (P.level - 1)
          (AffineSpace PUnit.{u + 1} T)
          (primeUnit P (AffineSpace PUnit.{u + 1} T)
            ((AffineSpace PUnit.{u + 1} T ↘ T) ≫ aT)) b hA 1 2).hom =
      (cartierSource T P α).hom ≫
        Etale.cartierKummerMap P.coefficients.l P.extension (P.level - 1)
          (sectionMap T) hI (primeUnit P (AffineSpace PUnit.{u + 1} T)
            ((AffineSpace PUnit.{u + 1} T ↘ T) ≫ aT))

end AlgebraicGeometry.ProEtale.CoordinateSectionNormalization
