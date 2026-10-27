module

public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import Sheaf.Paper.PurityFiniteSetting
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Sheaf.Paper.PurityAffineLineDatum
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.Paper.SfDerivedDirectImage
public import Sheaf.AlgebraicGeometry.ProEtalePairFlasque
public import Sheaf.AlgebraicGeometry.SupportLocalizationTriangle
public import Sheaf.Paper.FiniteDirectImageComposition
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
import Sheaf.Paper.PurityFiniteKummerLevel
import Sheaf.Paper.AffineLineSupportGeometry
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
public import Sheaf.AlgebraicGeometry.SupportTriangleConstruction
import Sheaf.AlgebraicGeometry.ProEtaleRingedClosedKernelAdjoint
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.AlgebraicGeometry.ProEtaleModuleDirectImageLeftExact
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

/-! # The affine-line support triangle after its retraction

Source: blueprint main-20261015, sk-prop-a1-kummer/lem-pur-gysin-structure.proof.md,
first paragraph (blueprint: lem-pur-zero-support-retraction-triangle).

All support functors below are the ordinary supported-kernel functors on module sheaves.
The comparison maps are the fixed right-derived compositors and identity comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open AlgebraicGeometry.ProEtale

attribute [local irreducible] Functor.rightDerivedFunctor
  Functor.mapDerivedCategory Functor.rightDerivedFunctorPlus
  DerivedCategory.Q DerivedCategory.Qh

namespace WeilConjectures.PurityFiniteSetting

/-- Ordinary constant-coefficient sheaves on the stipulated small site.
Source: affine-line datum (blueprint: lem-pur-zero-support-retraction-triangle). -/
abbrev ZeroSupportSheaves (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :=
  Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)

/-- The actual finite quotient supplies finiteness without an extra hypothesis.
Source: finite coefficient conventions (blueprint: lem-pur-zero-support-retraction-triangle).
-/
instance zeroSupportFinite (P : PurityFiniteSetting.{u}) : Finite P.Coefficient :=
  letI : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  inferInstanceAs (Finite (ULift.{u + 1} P.Ring))

/-- The zero section is the existing affine-space closed immersion.
Source: affine-line datum (blueprint: lem-pur-zero-support-retraction-triangle). -/
instance zeroSupportClosed (Y : Scheme.{u}) : IsClosedImmersion (zeroSection Y) :=
  inferInstanceAs (IsClosedImmersion (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y))

/-- The punctured line is the existing coordinate basic open.
Source: affine-line datum (blueprint: lem-pur-zero-support-retraction-triangle). -/
instance zeroSupportOpen (Y : Scheme.{u}) : IsOpenImmersion (openImmersion Y) :=
  inferInstanceAs (IsOpenImmersion ((Line Y).basicOpen (coordinate Y)).ι)

variable (P : PurityFiniteSetting.{u}) (Y : Scheme.{u})

/-- Bounded-below input in degree zero, with the specified finite twist.
Source: first paragraph of the Gysin proof
(blueprint: lem-pur-zero-support-retraction-triangle). -/
abbrev zeroSupportInput (h : P.ramificationIndex ∣ P.level) :=
  (DerivedCategory.Plus.singleFunctor (P.ZeroSupportSheaves (Line Y)) 0).obj
    (P.twist h (Line Y))

/-- The ordinary right derived supported-kernel functor, followed by inclusion in D.
Source: def-pur-flasque-support (blueprint: lem-pur-zero-support-retraction-triangle). -/
abbrev zeroSupportValueFunctor :=
  (finiteClosedUpperShriek P.Coefficient (zeroSection Y)
    (openImmersion Y)).rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι

/-- The affine-line direct image of bounded-below inputs.
Source: Gysin proof, first paragraph (blueprint: lem-pur-zero-support-retraction-triangle). -/
abbrev zeroSupportMiddleFunctor :=
  DerivedCategory.Plus.ι ⋙
    (lowerStar (ModuleCat.{u + 1} P.Coefficient) (lineProjection Y)).rightDerivedFunctor

/-- The punctured-line direct image, with actual open restriction of the input.
Source: Gysin proof, first paragraph (blueprint: lem-pur-zero-support-retraction-triangle). -/
abbrev zeroSupportOpenFunctor :=
  DerivedCategory.Plus.ι ⋙
    (upperStar (ModuleCat.{u + 1} P.Coefficient) (openImmersion Y)).mapDerivedCategory ⋙
    (lowerStar (ModuleCat.{u + 1} P.Coefficient) (puncturedProjection Y)).rightDerivedFunctor

/-- The fixed open-unit arrow followed by the inverse of the recorded compositor.
Source: Gysin proof, first paragraph (blueprint: lem-pur-zero-support-retraction-triangle). -/
def zeroSupportRestriction : P.zeroSupportMiddleFunctor Y ⟶ P.zeroSupportOpenFunctor Y :=
  Functor.whiskerLeft DerivedCategory.Plus.ι
    (Functor.whiskerRight
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient)
        (openImmersion Y)).mapDerivedCategoryRightDerivedAdjunction.unit
      (lowerStar (ModuleCat.{u + 1} P.Coefficient) (lineProjection Y)).rightDerivedFunctor ≫
    Functor.whiskerLeft
      (upperStar (ModuleCat.{u + 1} P.Coefficient) (openImmersion Y)).mapDerivedCategory
      (finiteDirectImageComposition P.Coefficient
        (openImmersion Y) (lineProjection Y)).inv)

section Pair
variable [QuasiCompact (openImmersion Y)]
  (hPair : IsCompl (Set.range (zeroSection Y)) (Set.range (openImmersion Y)))

/-- Use the localization theorem's adjunction with its injective-model counit normalization.
The theorem determines it through that normalization, rather than merely asserting an adjoint.
Source: lem-pur-support-localization-triangle
(blueprint: lem-pur-zero-support-retraction-triangle). -/
def zeroSupportAdjunction :=
  (supportLocalizationTriangle P.Coefficient (zeroSection Y) (openImmersion Y) hPair).choose

/-- The exact closed image; the sole auxiliary instance is the theorem for this closed/open pair.
Source: Stacks Tag 09BM (blueprint: lem-pur-zero-support-retraction-triangle). -/
abbrev zeroSupportClosedExact :
    PreservesFiniteColimits (lowerStar (ModuleCat.{u + 1} P.Coefficient) (zeroSection Y)) :=
  preservesFiniteColimits_lowerStar_of_isCompl
    (R := P.Coefficient) (zeroSection Y) (openImmersion Y) hPair

/-- The retraction comparison Rp_* s_* = R(ps)_* = id, with the fixed exact comparison.
Source: Gysin proof, ps=id (blueprint: lem-pur-zero-support-retraction-triangle). -/
def zeroSupportCollapse :
    (supportClosedDerivedPlus P.Coefficient (zeroSection Y) (openImmersion Y) hPair ⋙
      DerivedCategory.Plus.ι ⋙
      (lowerStar (ModuleCat.{u + 1} P.Coefficient) (lineProjection Y)).rightDerivedFunctor) ≅
      DerivedCategory.Plus.ι :=
  letI := P.zeroSupportClosedExact Y hPair
  Functor.isoWhiskerLeft DerivedCategory.Plus.ι
    (Functor.isoWhiskerRight
      (lowerStar (ModuleCat.{u + 1} P.Coefficient)
        (zeroSection Y)).rightDerivedFunctorIsoMapDerivedCategory.symm
      (lowerStar (ModuleCat.{u + 1} P.Coefficient) (lineProjection Y)).rightDerivedFunctor ≪≫
    (finiteDirectImageComposition P.Coefficient (zeroSection Y) (lineProjection Y)).symm ≪≫
    Functor.rightDerivedFunctorNatIso
      (lowerStarCongr (ModuleCat.{u + 1} P.Coefficient)
        (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin 1)) Y)) ≪≫
    Functor.rightDerivedFunctorNatIso (lowerStarId (ModuleCat.{u + 1} P.Coefficient) Y) ≪≫
    (𝟭 (P.ZeroSupportSheaves Y)).rightDerivedFunctorIsoMapDerivedCategory ≪≫
    Functor.mapDerivedCategoryIdIso (P.ZeroSupportSheaves Y))

/-- Image of the actual support-adjunction counit, with the retraction comparison inverted.
Source: Gysin proof, first arrow (blueprint: lem-pur-zero-support-retraction-triangle). -/
def zeroSupportFirst : P.zeroSupportValueFunctor Y ⟶ P.zeroSupportMiddleFunctor Y :=
  Functor.whiskerLeft
    (finiteClosedUpperShriek P.Coefficient (zeroSection Y)
      (openImmersion Y)).rightDerivedFunctorPlus (P.zeroSupportCollapse Y hPair).inv ≫
    Functor.whiskerRight (P.zeroSupportAdjunction Y hPair).counit
      (DerivedCategory.Plus.ι ⋙
        (lowerStar (ModuleCat.{u + 1} P.Coefficient) (lineProjection Y)).rightDerivedFunctor)

/-- The first term before applying Rp_*, using exact closed image and the bounded inclusion.
Source: support localization (blueprint: lem-pur-zero-support-retraction-triangle). -/
abbrev zeroSupportLocalFirstFunctor :=
  (finiteClosedUpperShriek P.Coefficient (zeroSection Y)
    (openImmersion Y)).rightDerivedFunctorPlus ⋙
      supportClosedDerivedPlus P.Coefficient (zeroSection Y) (openImmersion Y) hPair ⋙
      DerivedCategory.Plus.ι

/-- The open term before applying Rp_*, using the bounded-below direct image.
Source: support localization (blueprint: lem-pur-zero-support-retraction-triangle). -/
abbrev zeroSupportLocalThirdFunctor :=
  (upperStar (ModuleCat.{u + 1} P.Coefficient) (openImmersion Y)).mapDerivedCategoryPlus ⋙
    (lowerStar (ModuleCat.{u + 1} P.Coefficient)
      (openImmersion Y)).rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι

/-- The unrotated localization triangle with its actual counit and unit, for a natural boundary.
Source: support localization (blueprint: lem-pur-zero-support-retraction-triangle). -/
def zeroSupportLocalTriangle
    (d : P.zeroSupportLocalThirdFunctor Y ⟶ P.zeroSupportLocalFirstFunctor Y hPair ⋙
      shiftFunctor (DerivedCategory (P.ZeroSupportSheaves (Line Y))) (1 : ℤ))
    (K : DerivedCategory.Plus (P.ZeroSupportSheaves (Line Y))) :=
  Triangle.mk
    (DerivedCategory.Plus.ι.map ((P.zeroSupportAdjunction Y hPair).counit.app K))
    (DerivedCategory.Plus.ι.map
      ((derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} P.Coefficient)
        (openImmersion Y)).unit.app K)) (d.app K)

/-- The first-term identification is the retraction compositor at the actual support value.
Source: Gysin proof, ps=id (blueprint: lem-pur-zero-support-retraction-triangle). -/
def zeroSupportAlpha (K : DerivedCategory.Plus (P.ZeroSupportSheaves (Line Y))) :=
  (P.zeroSupportCollapse Y hPair).app
    ((finiteClosedUpperShriek P.Coefficient (zeroSection Y)
      (openImmersion Y)).rightDerivedFunctorPlus.obj K)

end Pair

/-- The canonical coefficient map for open restriction, fixed on actual root tensors.
Source: affine-line datum, twist restriction
(blueprint: lem-pur-zero-support-retraction-triangle). -/
def zeroSupportOpenCoefficient (h : P.ramificationIndex ∣ P.level) :
    (upperStar (ModuleCat.{u + 1} P.Coefficient)
      (openImmersion Y)).mapDerivedCategory.obj (P.zeroSupportInput Y h).obj ⟶
        P.derivedSheaf h (Punctured Y) true :=
  ((upperStar (ModuleCat.{u + 1} P.Coefficient)
    (openImmersion Y)).mapDerivedCategorySingleFunctor 0).hom.app (P.twist h (Line Y)) ≫
    (DerivedCategory.singleFunctor (P.ZeroSupportSheaves (Punctured Y)) 0).map
      ((comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} P.Coefficient)
        (openImmersion Y)).hom.app (P.twistEtale h (Line Y)) ≫
        (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) (Punctured Y)).map
          (P.twistEtalePullback h (openImmersion Y)))

/-- The actual Q=R pi_* A_U(1)[0], without a constructibility restriction.
Source: Gysin proof (blueprint: lem-pur-zero-support-retraction-triangle). -/
abbrev zeroSupportQ (h : P.ramificationIndex ∣ P.level) :=
  (lowerStar (ModuleCat.{u + 1} P.Coefficient)
    (puncturedProjection Y)).rightDerivedFunctor.obj (P.derivedSheaf h (Punctured Y) true)

/-- The third-term comparison uses bounded/unbounded compatibility, then the inverse
compositor for pj=pi, and finally the specified coefficient restriction identification.
Source: Gysin proof (blueprint: lem-pur-zero-support-retraction-triangle). -/
def zeroSupportBeta (h : P.ramificationIndex ∣ P.level)
    (c : (upperStar (ModuleCat.{u + 1} P.Coefficient)
        (openImmersion Y)).mapDerivedCategory.obj (P.zeroSupportInput Y h).obj ≅
      P.derivedSheaf h (Punctured Y) true) :=
  (lowerStar (ModuleCat.{u + 1} P.Coefficient) (lineProjection Y)).rightDerivedFunctor.mapIso
    ((lowerStar (ModuleCat.{u + 1} P.Coefficient)
      (openImmersion Y)).rightDerivedFunctorPlusCompatibility.app
        ((upperStar (ModuleCat.{u + 1} P.Coefficient)
          (openImmersion Y)).mapDerivedCategoryPlus.obj (P.zeroSupportInput Y h))) ≪≫
    (finiteDirectImageComposition P.Coefficient (openImmersion Y)
      (lineProjection Y)).symm.app _ ≪≫
    (lowerStar (ModuleCat.{u + 1} P.Coefficient)
      (puncturedProjection Y)).rightDerivedFunctor.mapIso c

section Conclusions
variable [QuasiCompact (openImmersion Y)]
  (hPair : IsCompl (Set.range (zeroSection Y)) (Set.range (openImmersion Y)))

/-- Transport of the image triangle by (alpha,id,beta), including the shifted first term.
The connecting map uses the same local boundary and the shift comparison of Rp_*.
Source: Gysin proof, first paragraph (blueprint: lem-pur-zero-support-retraction-triangle). -/
def zeroSupportTriangle (h : P.ramificationIndex ∣ P.level)
    (c : (upperStar (ModuleCat.{u + 1} P.Coefficient)
        (openImmersion Y)).mapDerivedCategory.obj (P.zeroSupportInput Y h).obj ≅
      P.derivedSheaf h (Punctured Y) true)
    (d : P.zeroSupportLocalThirdFunctor Y ⟶ P.zeroSupportLocalFirstFunctor Y hPair ⋙
      shiftFunctor (DerivedCategory (P.ZeroSupportSheaves (Line Y))) (1 : ℤ)) :=
  Triangle.mk ((P.zeroSupportFirst Y hPair).app (P.zeroSupportInput Y h))
    ((P.zeroSupportRestriction Y).app (P.zeroSupportInput Y h) ≫
      (lowerStar (ModuleCat.{u + 1} P.Coefficient)
        (puncturedProjection Y)).rightDerivedFunctor.map c.hom)
    ((P.zeroSupportBeta Y h c).inv ≫
      (lowerStar (ModuleCat.{u + 1} P.Coefficient)
        (lineProjection Y)).rightDerivedFunctor.map (d.app (P.zeroSupportInput Y h)) ≫
      ((lowerStar (ModuleCat.{u + 1} P.Coefficient)
        (lineProjection Y)).rightDerivedFunctor.commShiftIso (1 : ℤ)).hom.app _ ≫
      (P.zeroSupportAlpha Y hPair (P.zeroSupportInput Y h)).hom⟦(1 : ℤ)⟧')

/-- The support triangle assertion, including exactness, all shifts and all cohomology sheaves,
and the natural local boundary. The comparison of triangles fixes all three components.
Source: Gysin proof, first paragraph (blueprint: lem-pur-zero-support-retraction-triangle). -/
def ZeroSupportRetractionTriangle (h : P.ramificationIndex ∣ P.level) : Prop :=
  letI := P.zeroSupportClosedExact Y hPair
  Nonempty ((lowerStar (ModuleCat.{u + 1} P.Coefficient)
      (zeroSection Y)).rightDerivedFunctor ≅
    (lowerStar (ModuleCat.{u + 1} P.Coefficient) (zeroSection Y)).mapDerivedCategory) ∧
  (∀ q : ℤ, Nonempty
    (shiftFunctor (DerivedCategory (P.ZeroSupportSheaves Y)) q ⋙
        (lowerStar (ModuleCat.{u + 1} P.Coefficient) (zeroSection Y)).mapDerivedCategory ≅
      (lowerStar (ModuleCat.{u + 1} P.Coefficient) (zeroSection Y)).mapDerivedCategory ⋙
        shiftFunctor (DerivedCategory (P.ZeroSupportSheaves (Line Y))) q)) ∧
  (∀ q : ℤ, Nonempty
    (DerivedCategory.homologyFunctor (P.ZeroSupportSheaves Y) q ⋙
        lowerStar (ModuleCat.{u + 1} P.Coefficient) (zeroSection Y) ≅
      (lowerStar (ModuleCat.{u + 1} P.Coefficient) (zeroSection Y)).mapDerivedCategory ⋙
        DerivedCategory.homologyFunctor (P.ZeroSupportSheaves (Line Y)) q)) ∧
  ∃ (c : (upperStar (ModuleCat.{u + 1} P.Coefficient)
          (openImmersion Y)).mapDerivedCategory.obj (P.zeroSupportInput Y h).obj ≅
        P.derivedSheaf h (Punctured Y) true)
    (d : P.zeroSupportLocalThirdFunctor Y ⟶ P.zeroSupportLocalFirstFunctor Y hPair ⋙
      shiftFunctor (DerivedCategory (P.ZeroSupportSheaves (Line Y))) (1 : ℤ)),
    c.hom = P.zeroSupportOpenCoefficient Y h ∧
    (∃ (I : SupportComplex P.Coefficient (Line Y))
      (hI : IsSupportInjectiveModel P.Coefficient I)
      (hq : IsIso (DerivedCategory.Q.map
        (supportConeQuotient P.Coefficient (zeroSection Y) (openImmersion Y) hPair I)))
      (eB : DerivedCategory.Q.obj I ≅ (P.zeroSupportInput Y h).obj)
      (eL : supportModelTriangle P.Coefficient (zeroSection Y) (openImmersion Y) hPair I hq ≅
        P.zeroSupportLocalTriangle Y hPair d (P.zeroSupportInput Y h)),
      eL.hom.hom₁ = (supportFirstModelComparison P.Coefficient (zeroSection Y)
        (openImmersion Y) hPair I hI (P.zeroSupportInput Y h) eB).hom ∧
      eL.hom.hom₂ = eB.hom ∧
      eL.hom.hom₃ = (supportThirdModelComparison P.Coefficient (openImmersion Y)
        I hI (P.zeroSupportInput Y h) eB).hom) ∧
    P.zeroSupportLocalTriangle Y hPair d (P.zeroSupportInput Y h) ∈
      distTriang (DerivedCategory (P.ZeroSupportSheaves (Line Y))) ∧
    P.zeroSupportTriangle Y hPair h c d ∈
      distTriang (DerivedCategory (P.ZeroSupportSheaves Y)) ∧
    ∃ e : (lowerStar (ModuleCat.{u + 1} P.Coefficient)
          (lineProjection Y)).rightDerivedFunctor.mapTriangle.obj
        (P.zeroSupportLocalTriangle Y hPair d (P.zeroSupportInput Y h)) ≅
      P.zeroSupportTriangle Y hPair h c d,
      e.hom.hom₁ = (P.zeroSupportAlpha Y hPair (P.zeroSupportInput Y h)).hom ∧
      e.hom.hom₂ = 𝟙 _ ∧ e.hom.hom₃ = (P.zeroSupportBeta Y h c).hom

end Conclusions

/-- Affine-line support localization after the retraction, on ordinary small pro-etale
module sheaves, with no identification with a transported exceptional functor.

Source: blueprint main-20261015, sk-prop-a1-kummer/lem-pur-gysin-structure.proof.md,
first paragraph (blueprint: lem-pur-zero-support-retraction-triangle).

Proof:
1. FiniteKummerLevel identifies the coefficient quotient with a finite power of Z/ell^N;
   hence A is finite. AffineLineSupportGeometry gives the stated finite-type and
   Noetherian properties and quasi-compactness of the complementary open.
2. Closed pushforward is exact by the quasi-compact-complement theorem (Stacks 09BM).
   ExactFunctorDerivedFunctor identifies its termwise functor with Rs_*. Exact functors
   preserve kernels, images and quotients, giving the natural cohomology comparison in
   every integer degree, and termwise shifts give the shift comparison.
3. F is in degree zero. SupportLocalizationTriangle gives its injective-model triangle
   with the support-adjunction counit and the open unit. Its construction by supported
   kernels gives the natural boundary and resolution-independent maps of triangles.
4. The module categories have K-injective resolutions and p_* is additive, so its right
   derived functor is triangulated with its specified shift comparison.
5. Apply the inverse finite direct-image compositors for ps=id and pj=pi. Exactness
   identifies Rs_* with s_*; the identity comparison gives alpha. Restriction of the
   finite root tensor twist gives c and then beta, with c fixed by its root-tensor map.
6. Transport the image triangle by (alpha,id,beta). The displayed formulas for the three
   arrows give its three commuting squares and identify it with a distinguished triangle.
   All comparisons, the counit, the unit, and d are natural, proving the asserted
   naturality. No transported exceptional-adjoint comparison is used. -/
theorem zero_support_retraction_triangle (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a] :
    Finite P.Ring ∧ IsNoetherian Y ∧ IsNoetherian (Line Y) ∧ IsNoetherian (Punctured Y) ∧
    (LocallyOfFiniteType (lineProjection Y ≫ a) ∧ QuasiCompact (lineProjection Y ≫ a)) ∧
    (LocallyOfFiniteType (puncturedProjection Y ≫ a) ∧
      QuasiCompact (puncturedProjection Y ≫ a)) ∧
    ∃ (hq : QuasiCompact (openImmersion Y))
      (hPair : IsCompl (Set.range (zeroSection Y)) (Set.range (openImmersion Y))),
      @ZeroSupportRetractionTriangle P Y hq hPair h := by
  sorry

end WeilConjectures.PurityFiniteSetting
