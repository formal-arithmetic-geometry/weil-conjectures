/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

import all Mathlib.Logic.Small.Defs

import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteDiagonalReduction.FiniteDiagonalOrientationAssembly
import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteDiagonalReduction.FiniteDiagonalBaseChangeReduction
import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteDiagonalReduction.FiniteDiagonalDncReduction
import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteDiagonalReduction.FiniteDiagonalVectorReduction
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionAffineOrientation
public import WeilConjectures.AlgebraicGeometry.Cartier.CartierKummerMap
public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.AffineSpaceZeroSectionPurity
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.DiagonalDncChartNormalization
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCoefficientArrows
public import WeilConjectures.SmoothPurity.DncCoefficientTransport.PurityDncCoefficientTransport
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteDiagonalReduction.FiniteOrientationScalarPresentation
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteDiagonalReduction.FiniteSupportedReductionEquation
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteDiagonalReduction.FiniteProductScalarPresentation
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteDiagonalReduction.FiniteProductReductionComparisons
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteDiagonalReduction.FiniteDiagonalReductionComparisons

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionComparisons
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.PurityAffineLineOrientation
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalRegularPureCodimension
public import WeilConjectures.AlgebraicGeometry.Purity.PurityNormalProjection
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Section.PuritySectionInvariantIntrinsic
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.PurityDiagonalBaseChangeCompared
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Dnc.PurityDncInvariance
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Vector.VectorBundlePurity
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.PurityDiagonalDualizingObject

/-! # Reduction of the supported and diagonal orientation maps

Source: blueprint/latest, sec-smooth-purity/sk-lem-sp-reduction,
thm-pur-finite-reduction-of-purity.proof.md, Steps 3--4
(blueprint: lem-pur-finite-diagonal-orientation-reduction).

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

attribute [local irreducible]
  WeilConjectures.PurityFiniteSetting.finiteReductionOrientation
  WeilConjectures.PurityFiniteSetting.finiteReductionOrientationExceptionalComparison
  WeilConjectures.PurityFiniteSetting.finiteReductionOrientationInputComparison
  WeilConjectures.PurityFiniteSetting.finiteReductionUnitComparison

namespace WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction
open Etale.FiniteSmoothPurity

section EmptyProduct

set_option allowUnsafeReducibility true in
attribute [local reducible] iteratedAffineLine
  ProEtale.AffineZeroPurity.supportData ProEtale.AffineZeroPurity.zero
  ProEtale.AffineZeroPurity.classSource PurityFiniteSetting.functorialCupSource
  ProEtale.AffineSpacePurity.action Scheme.Hom.toIteratedAffineLine

end EmptyProduct

private theorem chainSquare {C : Type*} {D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A B E T : C} {A' B' E' T' : D}
    (a : A ⟶ B) (b : B ⟶ E) (c : E ⟶ T)
    (a' : A' ⟶ B') (b' : B' ⟶ E') (c' : E' ⟶ T')
    (qA : F.obj A ⟶ A') (qB : F.obj B ⟶ B')
    (qE : F.obj E ⟶ E') (qT : F.obj T ⟶ T')
    (ha : F.map a ≫ qB = qA ≫ a')
    (hb : F.map b ≫ qE = qB ≫ b')
    (hc : F.map c ≫ qT = qE ≫ c')
    (o : A ⟶ T) (o' : A' ⟶ T')
    (ho : o = a ≫ b ≫ c) (ho' : o' = a' ≫ b' ≫ c') :
    F.map o ≫ qT = qA ≫ o' := by
  subst o
  subst o'
  simp only [Functor.map_comp, Category.assoc]
  rw [hc, ← Category.assoc (F.map b), hb]
  simp only [Category.assoc]
  rw [← Category.assoc (F.map a), ha]
  simp only [Category.assoc]

section Diagonal
variable (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
variable {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
variable [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
variable [SmoothOfRelativeDimension d f]
variable (aY : Y ⟶ Spec (.of P.field.k))
variable [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]

/-- Reduction commutes with each of the three normalized diagonal factors, hence
with the specified diagonal orientation itself. No orientation is used to select
any coefficient comparison.
Source: node proof Steps 5--9; blueprint reduction proof Steps 3--4
(blueprint: lem-pur-finite-diagonal-orientation-reduction).
Proof: the actual diagonal base-change comparison is an adjunction mate, so the
scalar adjunction-unit and reduced-counit equations give the first square.
For DNC, use centred etale coordinates near the diagonal. Both coordinate maps
commute with reduction by pullback balancing and exceptional mate compatibility;
the normal framing [y(a)-x(a)] maps to da independently of coefficients. Conjugate
the reduced delta by q_N and q_C. In every coordinate chart its normalized reading
is the identity, since delta_A has that reading and the coordinate squares commute.
Uniqueness of the normalized DNC comparison identifies it with delta_B. For the
last square invert the coefficient-compatible integration adjunct gamma and pull
it to the normal zero section. The site comparison theorem identifies that mate
with the displayed ordinary-etale counit mate. Compose the three squares and use
the actual diagonal assembly to get the last equality. The unit normalizations
cover m=n and d=0; all tensors are derived, so no quotient flatness is required. -/
theorem diagonalOrientationReduction :
    ∃ e : CoefficientLineComparison (quotient P m hm hmn)
        P.diagonalExponent (P.finiteReductionSetting m hm).diagonalExponent
        P.diagonalExponent_annihilates
        (P.finiteReductionSetting m hm).diagonalExponent_annihilates X,
      (proScalar (quotient P m hm hmn) X).map (P.chartDiagonalAlpha d f aY).inv ≫
        diagonalSectionMap P m hm hmn d f aY =
      omegaMap P m hm hmn f aY ≫
        ((P.finiteReductionSetting m hm).chartDiagonalAlpha d f aY).inv ∧
      (proScalar (quotient P m hm hmn) X).map (P.chartDiagonalDelta d f aY).hom ≫
        normalSectionMap P m hm hmn d f aY =
      diagonalSectionMap P m hm hmn d f aY ≫
        ((P.finiteReductionSetting m hm).chartDiagonalDelta d f aY).hom ∧
      (proScalar (quotient P m hm hmn) X).map (vectorFactor P d f aY).hom ≫
        proTwistMap d e =
      normalSectionMap P m hm hmn d f aY ≫
        (vectorFactor (P.finiteReductionSetting m hm) d f aY).hom ∧
      (proScalar (quotient P m hm hmn) X).map
          (P.diagonalDualizingObject d f aY).hom ≫ proTwistMap d e =
      omegaMap P m hm hmn f aY ≫
        ((P.finiteReductionSetting m hm).diagonalDualizingObject d f aY).hom := by
  obtain ⟨e, hv⟩ := diagonalVectorReduction P m hm hmn d f aY
  have ha := diagonalBaseChangeReduction P m hm hmn d f aY
  have hd := diagonalDncReduction P m hm hmn d f aY
  refine ⟨e, ha, hd, hv, ?_⟩
  exact chainSquare (proScalar (quotient P m hm hmn) X)
    (P.chartDiagonalAlpha d f aY).inv (P.chartDiagonalDelta d f aY).hom
    (vectorFactor P d f aY).hom
    ((P.finiteReductionSetting m hm).chartDiagonalAlpha d f aY).inv
    ((P.finiteReductionSetting m hm).chartDiagonalDelta d f aY).hom
    (vectorFactor (P.finiteReductionSetting m hm) d f aY).hom
    (omegaMap P m hm hmn f aY) (diagonalSectionMap P m hm hmn d f aY)
    (normalSectionMap P m hm hmn d f aY) (proTwistMap d e) ha hd hv
    (P.diagonalDualizingObject d f aY).hom
    ((P.finiteReductionSetting m hm).diagonalDualizingObject d f aY).hom
    (diagonalOrientationAssembly P d f aY)
    (diagonalOrientationAssembly (P.finiteReductionSetting m hm) d f aY)

end Diagonal
end WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction
