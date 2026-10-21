/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q23
-/
module

public import Sheaf.Paper.OrientationFiniteReductionTwists
public import Sheaf.Paper.FiniteTateSiteDescent

/-! Canonical finite quotient and realization of the completed root lines.
Source: def-coefficient-twists-detailed (blueprint: def-sf-orientation-finite-line-comparisons). -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOfSpec false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct ChangeOfRings
namespace WeilConjectures

/-- The fixed-scalar inverse realization of a finite root power is its explicit
constant-scalar restriction. The equation fixes it on every local section through
the published scalar-unit section and equivalence counit.
Source: finite coefficient conventions (blueprint: def-sf-orientation-finite-line-comparisons).
Proof: restrict the intrinsic module action along constant scalars. The scalar-unit
map into the canonical intrinsic realization gives a morphism from its realization
to the original intrinsic line. Constant sections locally generate the constant
ring sheaf, so this map is an isomorphism and satisfies the displayed equation.
Transport through the fully faithful equivalence. The equation on all sections,
local generation by scalar-unit sections, and sheaf separatedness prove uniqueness. -/
theorem sfOrientationFixedRootSheaf_existsUnique
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u}) (m d : ℕ) :
    ∃! c : (sfIntrinsicModuleEquivalence X
      (Padic.coefficientExtensionRing l E (m + 1))).inverse.obj
        (finiteCoefficientTwist l E X m (d : ℤ)) ≅ finiteTateProSheaf l E m X d,
      ∀ (W : X.ProEtᵒᵖ) (x : (finiteTateProSheaf l E m X d).obj.obj W),
        ((sfIntrinsicModuleEquivalence X
          (Padic.coefficientExtensionRing l E (m + 1))).counitIso.hom.app
            (finiteCoefficientTwist l E X m (d : ℤ))).val.app W
          (sfIntrinsicRealizationUnit X (Padic.coefficientExtensionRing l E (m + 1))
            ((sfIntrinsicModuleEquivalence X
              (Padic.coefficientExtensionRing l E (m + 1))).inverse.obj
                (finiteCoefficientTwist l E X m (d : ℤ))) W (c.inv.hom.app W x)) = x := by
  sorry

/-- The specified finite ordinary-etale shifted line. This notation only packages
already defined coefficients and ordinary Tate powers.
Source: coefficient conventions (blueprint: def-sf-orientation-finite-line-comparisons). -/
def sfOrientationFiniteEtaleLine
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u}) (m r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E m) = 0) (d : ℕ) :=
  ((DerivedCategory.singleFunctor _ 0).obj
    (finiteEtaleTateTwist X (l ^ (r + 1)) (finiteTateCoefficient l E m) hA d))⟦2 * (d : ℤ)⟧

/-- Realization of the actual finite reduction line. The root comparison is
selected by IsFiniteTateSiteComparison, the quotient comparison by the actual
scalar adjunction, and the intrinsic realization by its scalar-unit counit.
Source: realization and finite reduction conventions
(blueprint: def-sf-orientation-finite-line-comparisons). -/
def sfOrientationFiniteSiteLine
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)] (hX : IsUnit (l : Γ(X, ⊤)))
    (m r : ℕ) (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E m) = 0) (d : ℕ) :
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (finiteTateCoefficient l E m)) X).mapDerivedCategory.obj
      (sfOrientationFiniteEtaleLine l E X m r hA d) ≅
    (sfIntrinsicDerivedEquivalence X
      (Padic.coefficientExtensionRing l E (m + 1))).inverse.obj
        ((scalarReductionDerivedExtension l E X m).obj
        (DerivedCategory.Q.obj (sfOrientationIntegralComplex l E X d))) :=
  let A := finiteTateCoefficient l E m
  let F := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X
  let R := (sfIntrinsicModuleEquivalence X
    (Padic.coefficientExtensionRing l E (m + 1))).inverse
  (F.mapDerivedCategory.commShiftIso (2 * (d : ℤ))).app _ ≪≫
    (shiftFunctor _ (2 * (d : ℤ))).mapIso
      ((F.mapDerivedCategorySingleFunctor 0).app _ ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso
          ((finite_tate_site_descent l E m).choose X hX r hA d)) ≪≫
    ((DerivedCategory.singleFunctors _).shiftIso (2 * (d : ℤ)) (-2 * (d : ℤ)) 0
      (by omega)).app _ ≪≫
    (DerivedCategory.singleFunctor _ (-2 * (d : ℤ))).mapIso
      (sfOrientationFixedRootSheaf_existsUnique l E X m d).exists.choose.symm ≪≫
    ((R.mapDerivedCategorySingleFunctor (-2 * (d : ℤ))).app _).symm ≪≫
    R.mapDerivedCategory.mapIso (sfOrientationFiniteReduction l E X m d).symm

end WeilConjectures
