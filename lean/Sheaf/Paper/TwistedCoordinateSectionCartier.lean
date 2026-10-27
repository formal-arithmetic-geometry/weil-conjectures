/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Sheaf.Paper.TwistedCoordinateSectionCoprojection
public import Sheaf.Paper.TwistedCoordinateSectionProjective

/-! # Twisted coordinate-section normalization
Source: current blueprint, sec-smooth-purity/sk-prop-an,
cor-pur-affine-space-zero-section-purity.proof.md, rank-one and even-shift paragraphs
(blueprint: def-pur-coordinate-section-cartier-realization).

The supporting module spells out every arrow; this module records the normalization,
its canonical closed coprojection, its Cartier realization and its signed orientation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CoordinateSectionNormalization
open AffineLinePurity VectorIntegrationSite
variable (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})

variable (P : WeilConjectures.PurityFiniteSetting.{u})

/-- The compared supported source, using the exact closed-image/single comparison
and the specified underived support comparison alpha.
Source: blueprint actual Cartier realization
(blueprint: def-pur-coordinate-section-cartier-realization). -/
def cartierSource (α :
    (comparisonUpperStar (ModuleCat.{u + 1} (Ring P)) (AffineSpace PUnit.{u + 1} T)).obj
      ((Etale.lowerStar (ModuleCat.{u + 1} (Ring P)) (sectionMap T)).obj
        (Etale.ordinaryFiniteConstant (Ring P) T)) ≅
      Etale.cartierSupported P.coefficients.l P.extension (P.level - 1) (sectionMap T)) :=
  (VectorIntegrationSite.comparison (Ring P) (AffineSpace PUnit.{u + 1} T)).mapIso
      (((Etale.lowerStar (ModuleCat.{u + 1} (Ring P))
        (sectionMap T)).singleFunctorCompRightDerivedFunctorIso).app
          (Etale.ordinaryFiniteConstant (Ring P) T)) ≪≫
    ((comparisonUpperStar (ModuleCat.{u + 1} (Ring P))
      (AffineSpace PUnit.{u + 1} T)).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso α

/-- Equality with the published Cartier arrow for every annihilating exponent.
Alpha is fixed by the supported-constant unit, and the target is fixed by root projection.
This gives independence of a as equality of derived morphisms, not only of cohomology.
Source: blueprint Steps 5 and 10
(blueprint: def-pur-coordinate-section-cartier-realization). -/
def CartierRealization (aT : T ⟶ Spec (.of P.field.k))
    (hI : (sectionMap T).ker.IsInvertible) : Prop :=
  ∃ α : (comparisonUpperStar (ModuleCat.{u + 1} (Ring P))
      (AffineSpace PUnit.{u + 1} T)).obj
        ((Etale.lowerStar (ModuleCat.{u + 1} (Ring P)) (sectionMap T)).obj
          (Etale.ordinaryFiniteConstant (Ring P) T)) ≅
        Etale.cartierSupported P.coefficients.l P.extension (P.level - 1) (sectionMap T),
    (comparisonUpperStar (ModuleCat.{u + 1} (Ring P)) (AffineSpace PUnit.{u + 1} T)).map
      (Etale.supportedConstantUnit (Ring P) (sectionMap T)) ≫ α.hom =
        Etale.cartierConstantComparison (Ring P) (AffineSpace PUnit.{u + 1} T) ≫
          Etale.cartierSupportedUnit P.coefficients.l P.extension (P.level - 1)
            (sectionMap T) ∧
    ∀ (b : ℕ) (hA : ((P.coefficients.l ^ (b + 1) : ℕ) : Ring P) = 0),
      (VectorIntegrationSite.comparison (Ring P) (AffineSpace PUnit.{u + 1} T)).map
        (ordinarySupported (Ring P) T (P.coefficients.l ^ (b + 1))
          (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) hA
          (affineTraceInvertible (P.coefficients.l ^ (b + 1)) T
            (by simpa only [Nat.cast_pow] using (primeUnit P T aT).pow (b + 1)) 1) hI) ≫
        (twistDerived P.coefficients.l P.extension (P.level - 1)
          (AffineSpace PUnit.{u + 1} T)
          (primeUnit P _ ((AffineSpace PUnit.{u + 1} T ↘ T) ≫ aT)) b hA 1 2).hom =
      (cartierSource T P α).hom ≫
        Etale.cartierKummerMap P.coefficients.l P.extension (P.level - 1) (sectionMap T)
          hI (primeUnit P _ ((AffineSpace PUnit.{u + 1} T ↘ T) ≫ aT))


end AlgebraicGeometry.ProEtale.CoordinateSectionNormalization
