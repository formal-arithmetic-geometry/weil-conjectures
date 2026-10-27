module

import Sheaf.Paper.FiniteDiagonalOrientationAssembly
import Sheaf.Paper.FiniteDiagonalBaseChangeReduction
import Sheaf.Paper.FiniteDiagonalDncReduction
import Sheaf.Paper.FiniteDiagonalVectorReduction
public import Sheaf.Paper.FiniteReductionAffineOrientation
public import Sheaf.AlgebraicGeometry.CartierKummerMap
public import Sheaf.Paper.AffineSpaceZeroSectionPurity
public import Sheaf.Paper.DiagonalDncChartNormalization
public import Sheaf.Paper.FiniteSmoothCoefficientArrows
public import Sheaf.SecSmoothPurity.PurityDncCoefficientTransport
public import Sheaf.Paper.FiniteOrientationScalarPresentation
public import Sheaf.Paper.FiniteSupportedReductionEquation
public import Sheaf.Paper.FiniteProductScalarPresentation
public import Sheaf.Paper.FiniteProductReductionComparisons
public import Sheaf.Paper.FiniteDiagonalReductionComparisons

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.Paper.FiniteReductionComparisons
public import Sheaf.Paper.PurityAffineLineOrientation
public import Sheaf.AlgebraicGeometry.DiagonalRegularPureCodimension
public import Sheaf.Paper.PurityNormalProjection
public import Sheaf.Paper.PuritySectionInvariantIntrinsic
public import Sheaf.Paper.PurityDiagonalBaseChangeCompared
public import Sheaf.Paper.PurityDncInvariance
public import Sheaf.Paper.VectorBundlePurity
public import Sheaf.Paper.PurityDiagonalDualizingObject

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

/-- Specialize the existing family reduction before inserting the large coefficient datum.
Source: CartierKummerReduction; node proof Step 1
(blueprint: lem-pur-finite-diagonal-orientation-reduction). -/
private theorem supportedKummerReductionAt_of_family (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (c : Etale.CartierKummerFamily l E) (a b : ℕ) (hab : a ≤ b)
    (S : Scheme.{u})
    (hT : IsUnit (l : Γ(AffineSpace (ULift.{u} (Fin 1)) S, ⊤)))
    (h : Etale.CartierKummerReduction l E c) :
    supportedKummerReductionAt l E c a b hab S hT := by
  unfold Etale.CartierKummerReduction at h
  unfold supportedKummerReductionAt
  exact h a b hab (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)
    (finiteReductionZeroCartier S) hT

/-- The actual supported Cartier boundary reduces on the affine zero divisor.
Source: node proof Step 1; Stacks 0A45, 07A6
(blueprint: lem-pur-finite-diagonal-orientation-reduction).
Proof: apply Cartier-Kummer coefficient compatibility to the effective Cartier
zero divisor: its coordinate is a nonzerodivisor over every base. The two scalar
units are fixed on supported constants and root-limit tensors by their section
formulas. Their universal properties transpose the supported Ext equation to the
asserted B-linear derived reduction equation, without quotient flatness. -/
theorem supportedKummerReduction (P : PurityFiniteSetting.{u})
    (a b : ℕ) (hab : a ≤ b) (S : Scheme.{u})
    [S.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (S ↘ Spec (.of P.field.k))]
    [QuasiCompact (S ↘ Spec (.of P.field.k))]
    [IsSeparated (S ↘ Spec (.of P.field.k))] :
    supportedKummerReductionAt P.coefficients.l P.extension (cartierFamily P) a b hab S
      (ProEtale.AffineLinePurity.primeUnit P _
        (AffineSpace (ULift.{u} (Fin 1)) S ↘ Spec (.of P.field.k))) := by
  apply supportedKummerReductionAt_of_family
  unfold cartierFamily
  exact (Etale.cartier_kummer_map P.coefficients.l P.extension).2.exists.choose_spec.2.2.2.2.2

/-- Reduction of the actual Kummer exceptional adjunct at every positive level.
Source: node proof Step 2 (blueprint: lem-pur-finite-diagonal-orientation-reduction).
Proof: transpose the preceding supported equation through the two exceptional
adjunctions. The reduced counit normalization identifies the intervening mate
with finiteReductionOrientationExceptionalComparison. The input and unit maps
are precisely their independent root and scalar-unit normalizations. -/
theorem affineOrientationReduction (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
    (S : Scheme.{u}) [S.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (S ↘ Spec (.of P.field.k))]
    [QuasiCompact (S ↘ Spec (.of P.field.k))]
    [IsSeparated (S ↘ Spec (.of P.field.k))] :
    (P.finiteReduction m hm hmn S).map (P.finiteReductionOrientation S) ≫
      P.finiteReductionOrientationExceptionalComparison m hm hmn S ≫
      ((P.finiteReductionSetting m hm).compositionExceptional
        (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)).map
          (P.finiteReductionOrientationInputComparison m hm hmn S).hom =
    P.finiteReductionUnitComparison m hm hmn S ≫
      (P.finiteReductionSetting m hm).finiteReductionOrientation S := by
  sorry

/-- All ordered supported products and their actual exceptional adjuncts reduce.
The coefficient-line record fixes the root power, every scalar/root generator, and
its derived scalar counit; it is not an arbitrary endpoint isomorphism.
Source: node proof Steps 3--4
(blueprint: lem-pur-finite-diagonal-orientation-reduction).
Proof: ordinary balancing sends (x tensor y) tensor b to bar(x)bar(y)b and
commutes with the supported multiplication. On flat-term K-flat representatives
this is the derived tensor square; its even shifts preserve every cup sign.
Induct through List.finRange in the definition of supportedClass, starting with
the scalar unit at r=0. The canonical support identification is coefficient-free.
Finally transpose the supported square under the closed exceptional Hom bijection.
Its reduced counit is proCoefficientMap, giving the displayed Thom square.
The root-power map and balancing construct the indicated coefficient-line record
at all positive levels, including equal levels and arbitrary ramification. -/
theorem supportedProductsReduction (P : PurityFiniteSetting.{u})
    (a b : ℕ) (hab : a ≤ b) (S : Scheme.{u}) (aS : S ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aS] [QuasiCompact aS] [IsSeparated aS] (r : ℕ) :
    ∃ e : CoefficientLineComparison
        (Etale.cartierCoefficientReduction P.coefficients.l P.extension a b hab)
        (P.coefficients.l ^ (b + 1 + 1)) (P.coefficients.l ^ (a + 1 + 1))
        (ProEtale.AffineSpacePurity.annihilates (ProEtale.AffineZeroPurity.setting P b))
        (ProEtale.AffineSpacePurity.annihilates (ProEtale.AffineZeroPurity.setting P a))
        (iteratedAffineLine S r),
      (proScalar _ (iteratedAffineLine S r)).map
          (ProEtale.AffineZeroPurity.supportedClass P b S aS r) ≫
        productTargetMap P a b hab _ e r =
      productSourceMap P a b hab S aS r ≫
        ProEtale.AffineZeroPurity.supportedClass P a S aS r ∧
      (proScalar _ S).map (ProEtale.AffineZeroPurity.thom P b S aS r) ≫
        proCoefficientMap _ (ProEtale.AffineZeroPurity.zero S r)
          (ProEtale.AffineZeroPurity.target P b (iteratedAffineLine S r) r) ≫
        (ProEtale.rightDerivedUpperShriek
          (ModuleCat.{u + 1} (ProEtale.AffineZeroPurity.setting P a).Coefficient)
          (ProEtale.AffineZeroPurity.zero S r)).map
            (productTargetMap P a b hab _ e r) =
      productUnitMap P a b hab S ≫ ProEtale.AffineZeroPurity.thom P a S aS r := by
  sorry

/-- The empty supported product is the coefficient unit and its Thom adjunct is
its normalized identity-adjunction unit.
Source: node proof Steps 3--4, empty-product case
(blueprint: lem-pur-finite-diagonal-orientation-reduction).
Proof: the empty list in product is its unit clause. The support identification
is the identity by the empty-coordinate universal property. The exact pushforward
identity comparison gives the first equation. Transposing through the identity
exceptional adjunction gives the second, whose normalization is the specified
identity-adjunction comparison in normalizationRaw at zero. -/
theorem supportedProductsUnit (P : PurityFiniteSetting.{u}) (n : ℕ)
    (S : Scheme.{u}) (aS : S ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aS] [QuasiCompact aS] [IsSeparated aS] :
    ProEtale.AffineZeroPurity.supportedClass P n S aS 0 =
      (ProEtale.cupSingle (ProEtale.AffineZeroPurity.setting P n) S).map
        (((ProEtale.lowerStarCongr
          (ModuleCat.{u + 1} (ProEtale.AffineZeroPurity.setting P n).Coefficient)
          (ProEtale.AffineZeroPurity.zero_zero S)) ≪≫
          ProEtale.lowerStarId
            (ModuleCat.{u + 1} (ProEtale.AffineZeroPurity.setting P n).Coefficient) S).hom.app
              ((ProEtale.AffineZeroPurity.setting P n).constant S)) ∧
    ProEtale.AffineZeroPurity.thom P n S aS 0 ≫
      ProEtale.AffineZeroPurity.normalization P n S aS 0 = 𝟙 _ := by
  sorry

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
