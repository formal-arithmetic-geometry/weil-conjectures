/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteProductScalarPresentation
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothCoefficientArrows
public import WeilConjectures.AlgebraicGeometry.AffineSpaceZeroSectionPurity

/-! # Canonical coefficient comparisons for supported products and Thom maps

Source: blueprint/latest, sec-smooth-purity/sk-lem-sp-reduction,
thm-pur-finite-reduction-of-purity.proof.md, Steps 3--4
(blueprint: def-pur-finite-product-reduction-comparisons).

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

attribute [local instance 2000] CategoryTheory.sheafIsAbelian

namespace WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction
open Etale.FiniteSmoothPurity

/-- The canonical closed-source comparison, before coefficient specialization.
Source: supported products, Step 3
(blueprint: def-pur-finite-product-reduction-comparisons). -/
@[irreducible]
def closedSourceMap {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) {Z T : Scheme.{u}} (i : Z ⟶ T)
    [IsClosedImmersion i] [HasCompactification i]
    [PreservesFiniteColimits (ProEtale.lowerStar (ModuleCat.{u + 1} A) i)]
    [PreservesFiniteColimits (ProEtale.lowerStar (ModuleCat.{u + 1} B) i)]
    (M : Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A))
    (N : Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} B))
    (q : (proScalar φ Z).obj ((DerivedCategory.singleFunctor _ 0).obj M) ⟶
      (DerivedCategory.singleFunctor _ 0).obj N) :
    (proScalar φ T).obj ((DerivedCategory.singleFunctor _ 0).obj
      ((ProEtale.lowerStar (ModuleCat.{u + 1} A) i).obj M)) ⟶
    (DerivedCategory.singleFunctor _ 0).obj
      ((ProEtale.lowerStar (ModuleCat.{u + 1} B) i).obj N) :=
  (proScalar φ T).map
      ((ProEtale.rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar
        (ModuleCat.{u + 1} A) i).app ((DerivedCategory.singleFunctor _ 0).obj M) ≪≫
      (ProEtale.lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctorIsoMapDerivedCategory.app
        ((DerivedCategory.singleFunctor _ 0).obj M) ≪≫
      ((ProEtale.lowerStar (ModuleCat.{u + 1} A) i).mapDerivedCategorySingleFunctor 0).app M).inv ≫
    proCompactCoefficientMap φ i ((DerivedCategory.singleFunctor _ 0).obj M) ≫
    (ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} B) i).map q ≫
    ((ProEtale.rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar
        (ModuleCat.{u + 1} B) i).app ((DerivedCategory.singleFunctor _ 0).obj N) ≪≫
      (ProEtale.lowerStar (ModuleCat.{u + 1} B) i).rightDerivedFunctorIsoMapDerivedCategory.app
        ((DerivedCategory.singleFunctor _ 0).obj N) ≪≫
      ((ProEtale.lowerStar (ModuleCat.{u + 1} B) i).mapDerivedCategorySingleFunctor 0).app N).hom

/-- The actual zero-support comparison, with exactness derived from finite type.
Source: supported products, Step 3
(blueprint: def-pur-finite-product-reduction-comparisons). -/
@[irreducible]
def productSourceMap (P : PurityFiniteSetting.{u}) (a b : ℕ) (hab : a ≤ b)
    (S : Scheme.{u}) (aS : S ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aS] [QuasiCompact aS] [IsSeparated aS] (r : ℕ) :=
  letI : PreservesFiniteColimits (ProEtale.lowerStar
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient P.coefficients.l P.extension a))
      (ProEtale.AffineZeroPurity.zero S r)) :=
    ProEtale.AffineZeroPurity.zero_exact P a S aS r
  letI : PreservesFiniteColimits (ProEtale.lowerStar
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient P.coefficients.l P.extension b))
      (ProEtale.AffineZeroPurity.zero S r)) :=
    ProEtale.AffineZeroPurity.zero_exact P b S aS r
  @closedSourceMap _ _ inferInstance inferInstance inferInstance inferInstance
    (Etale.cartierCoefficientReduction P.coefficients.l P.extension a b hab)
    S (iteratedAffineLine S r) (ProEtale.AffineZeroPurity.zero S r)
    (ProEtale.AffineZeroPurity.zero_closed S r) inferInstance
    (ProEtale.AffineZeroPurity.zero_exact P b S aS r)
    (ProEtale.AffineZeroPurity.zero_exact P a S aS r)
    ((ProEtale.AffineZeroPurity.setting P b).constant S)
    ((ProEtale.AffineZeroPurity.setting P a).constant S) (productUnitMap P a b hab S)

/-- The product target comparison uses the ordered tensor powers of the normalized
root comparison and the canonical ordinary/pro-etale scalar mate.
Source: node proof Steps 3--4
(blueprint: def-pur-finite-product-reduction-comparisons). -/
@[irreducible]
def productTargetMap (P : PurityFiniteSetting.{u}) (a b : ℕ) (hab : a ≤ b)
    (T : Scheme.{u})
    (e : CoefficientLineComparison
      (Etale.cartierCoefficientReduction P.coefficients.l P.extension a b hab)
      (P.coefficients.l ^ (b + 1 + 1)) (P.coefficients.l ^ (a + 1 + 1))
      (ProEtale.AffineSpacePurity.annihilates (ProEtale.AffineZeroPurity.setting P b))
      (ProEtale.AffineSpacePurity.annihilates (ProEtale.AffineZeroPurity.setting P a)) T)
    (r : ℕ) :=
  presented (Etale.cartierCoefficientReduction P.coefficients.l P.extension a b hab) T
    (productTargetPresentation P b T r) (productTargetPresentation P a T r)
    (e.tensorPower r).hom


end WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction
