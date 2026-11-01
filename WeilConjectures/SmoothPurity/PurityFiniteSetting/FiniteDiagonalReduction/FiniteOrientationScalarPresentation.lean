/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionComparisons
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCoefficientArrows
public import WeilConjectures.AlgebraicGeometry.Cartier.CartierKummerMap

/-! # Canonical scalar presentations of finite orientation arrows

Source: blueprint/latest, sec-smooth-purity/sk-lem-sp-reduction,
thm-pur-finite-reduction-of-purity.proof.md, Steps 3--4
(blueprint: def-pur-finite-orientation-scalar-presentation).

The fixed-scalar pro-etale presentation is canonically equivalent to the intrinsic
one. All maps below are the published root-generator, scalar-unit and counit mates.
Positive affine coefficient levels are indexed by their predecessors, as in the
published supported-product API; no divisibility by a ramification index is imposed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor

attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  ProEtale.pbcFixedScalarExtension Etale.derivedTensor Etale.upperStar Etale.lowerStar

namespace WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction
open Etale.FiniteSmoothPurity

/-- Coefficient reduction in the fixed-scalar presentation, with the canonical size lift.
Source: Steps 3--4 (blueprint: def-pur-finite-orientation-scalar-presentation). -/
abbrev quotient (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m)
    (hmn : m ≤ P.level) : P.Coefficient →+* (P.finiteReductionSetting m hm).Coefficient :=
  RingHom.ulift.{u + 1, u + 1, u, u} (P.finiteReductionRingHom m hm hmn)

/-- Realize an ordinary coefficient arrow, using the specified site/scalar comparison.
Source: Step 3 (blueprint: def-pur-finite-orientation-scalar-presentation). -/
@[irreducible]
def realize {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) {K : Etale.DerivedCategoryModule A T}
    {L : Etale.DerivedCategoryModule B T}
    (q : (ordinaryScalar φ T).obj K ⟶ L) :
    (proScalar φ T).obj ((comparison A T).obj K) ⟶ (comparison B T).obj L :=
  (ProEtale.pbcComparisonReduction T φ).hom.app K ≫ (comparison B T).map q

/-- Transport a specified coefficient arrow through canonical object presentations.
Source: Step 3 (blueprint: def-pur-finite-orientation-scalar-presentation). -/
@[irreducible]
def presented {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    {K : proCategory A T} {L : proCategory B T}
    {K₀ : Etale.DerivedCategoryModule A T} {L₀ : Etale.DerivedCategoryModule B T}
    (a : K ≅ (comparison A T).obj K₀) (b : L ≅ (comparison B T).obj L₀)
    (q : (ordinaryScalar φ T).obj K₀ ⟶ L₀) : (proScalar φ T).obj K ⟶ L :=
  (proScalar φ T).map a.hom ≫ realize φ T q ≫ b.inv

end WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction
