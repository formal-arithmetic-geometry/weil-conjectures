/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q76
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleRingedClosedKernelAdjoint
public import Sheaf.Paper.ClosedFiniteAdjointCounitTransport
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.IntegralExceptionalInverseImage
public import Sheaf.Paper.SfExceptionalReductionTransitions
public import Sheaf.Paper.EtaleSystemQuotientNormalization
public import Sheaf.Paper.EtaleCompactScalarCoherence
public import Sheaf.Paper.FiniteCoefficientDirectImage
public import Sheaf.Paper.WitnessCompatibility
public import Sheaf.Paper.ExceptionalDerivedSiteRealization
public import Sheaf.Paper.ExceptionalFiniteSupportRealization
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Shift.Adjunction
import Sheaf.AlgebraicGeometry.EtaleClosedSupportAmplitude
import Sheaf.AlgebraicGeometry.EtaleClosedSupportTriangle
import Sheaf.AlgebraicGeometry.OpenComplementKnown
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.ClassicalSupportCounitIdentification
import Sheaf.AlgebraicGeometry.ClosedUnboundedCompactSupportNormalization
import Sheaf.Paper.CoefficientSystemDerivedComparison
import Sheaf.Paper.EtaleCoefficientSystemAdjoint
import Sheaf.CategoryTheory.ExactDerivedAdjunctionBounds
import Sheaf.Paper.RoosIntrinsicCompletenessEquivalence
import Sheaf.AlgebraicGeometry.SupportLocalizationTriangle
import Sheaf.AlgebraicGeometry.ClosedDirectImageStrictReduction
import Sheaf.Paper.ComparisonPullbackExact
import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
import Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.CategoryTheory.Triangulated.TriangleMorphismExtension
import Sheaf.SixFunctors.ProEtaleClosedTensorProjection
import Sheaf.AlgebraicGeometry.ComparisonDirectImage
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit

/-! # Counit normalization of the closed exceptional functor

Source: current blueprint, sec-smooth-purity/sk-prop-sf-localization,
prop-sf-localization-all-stages.proof.md, exceptional identification in (2)--(3).
(blueprint: lem-sf-finite-exceptional-site-normalization).

Finite sheaves are written in the existing fixed-module coordinates. The predicate
below uses the canonical intrinsic realization, so its domain is precisely D^b_c,
without a finite-Tor condition. Adjunctions are quantified as presentations of the
kernel adjoint: their normalized comparison is determined by their counit.
Natural-number levels denote positive exponents n+1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genInjectivity false
set_option genSizeOfSpec false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FiniteExceptionalNormalization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The recorded positive quotient, lifted to the small site's value universe.
Source: blueprint localization, finite stage
(blueprint: lem-sf-finite-exceptional-site-normalization). -/
abbrev A (n : ℕ) := ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))

/-- The fixed-module presentation of the original small pro-etale derived category.
Source: blueprint localization, finite stage
(blueprint: lem-sf-finite-exceptional-site-normalization). -/
abbrev C (T : Scheme.{u}) (n : ℕ) :=
  DerivedCategory (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (A l E n)))

/-- Bounded constructibility, tested through the canonical intrinsic realization.
Source: blueprint localization, K in D^b_c(X,A_n)
(blueprint: lem-sf-finite-exceptional-site-normalization). -/
def bc (T : Scheme.{u}) (n : ℕ) : ObjectProperty (C l E T n) :=
  fun K ↦ intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) T
    ((ProEtale.finiteCoefficientIntrinsicRealization T
      (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.obj K)

/-- The actual etale compact-support functor at (id_Z,i).
Source: blueprint localization, finite exceptional adjoint
(blueprint: lem-sf-finite-exceptional-site-normalization). -/
abbrev etaleSupport {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (n : ℕ) :=
  Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (A l E n))
    (Compactification.ofIsProper i)

/-- The same ordinary etale right adjoint as in the specified exceptional definition.
Source: blueprint localization, finite exceptional adjoint
(blueprint: lem-sf-finite-exceptional-site-normalization). -/
abbrev etaleExceptional {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (n : ℕ) :=
  (etaleSupport l E i n).rightAdjoint

/-- The literal comparison-site formula at the specified compactification.
Source: blueprint localization, displayed finite identification
(blueprint: lem-sf-finite-exceptional-site-normalization). -/
abbrev exceptional {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (n : ℕ) :=
  ProEtale.sfFiniteExceptionalAt (A l E n) (Compactification.ofIsProper i)

/-- The ordinary unbounded closed direct image in the same coordinates.
Source: blueprint localization, ambient kernel adjunction
(blueprint: lem-sf-finite-exceptional-site-normalization). -/
abbrev image {X Z : Scheme.{u}} (i : Z ⟶ X) (n : ℕ) :=
  (ProEtale.lowerStar (ModuleCat.{u + 1} (A l E n)) i).rightDerivedFunctor

/-- The open-unit target in the supported triangle.
Source: blueprint localization, finite supported triangle
(blueprint: lem-sf-finite-exceptional-site-normalization). -/
abbrev openImage {X U : Scheme.{u}} (j : U ⟶ X) (n : ℕ) :=
  (ProEtale.upperStar (ModuleCat.{u + 1} (A l E n)) j).leftDerivedFunctor ⋙
    (ProEtale.lowerStar (ModuleCat.{u + 1} (A l E n)) j).rightDerivedFunctor

/-- The actual open adjunction unit, with no chosen completion of a triangle.
Source: blueprint localization, open unit
(blueprint: lem-sf-finite-exceptional-site-normalization). -/
def openUnit {X U : Scheme.{u}} (j : U ⟶ X) (n : ℕ) :
    𝟭 (C l E X n) ⟶ openImage l E j n :=
  (ProEtale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} (A l E n)) j).unit

/-- The specified transported exceptional counit, with closed direct image expressed
as its right-derived functor. The exact termwise comparison is canonical.
Source: blueprint localization, finite counit normalization
(blueprint: lem-sf-finite-exceptional-site-normalization). -/
def counit {X Z U : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (h : IsCompl (Set.range i) (Set.range j)) (n : ℕ) (K : C l E X n) :
    (image l E i n).obj ((exceptional l E i n).obj K) ⟶ K :=
  haveI := ProEtale.preservesFiniteColimits_lowerStar_of_isCompl
    (R := A l E n) i j h
  (Functor.rightDerivedFunctorIsoMapDerivedCategory
    (ProEtale.lowerStar (ModuleCat.{u + 1} (A l E n)) i)).hom.app _ ≫
    ProEtale.ClosedFiniteTransport.transportedCounit (A l E n) i j h K

/-- Canonical shift of the etale right adjoint and of the site formula.
Source: blueprint localization, shift normalization
(blueprint: lem-sf-finite-exceptional-site-normalization). -/
def specifiedShift {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (n : ℕ) (d : ℤ) :
    shiftFunctor (C l E X n) d ⋙ exceptional l E i n ≅
      exceptional l E i n ⋙ shiftFunctor (C l E Z n) d :=
  haveI := (Adjunction.ofIsLeftAdjoint (etaleSupport l E i n)).rightAdjointCommShift ℤ
  haveI : (exceptional l E i n).CommShift ℤ :=
    inferInstanceAs (((ProEtale.comparisonLowerStar
      (ModuleCat.{u + 1} (A l E n)) X).rightDerivedFunctor ⋙
      etaleExceptional l E i n ⋙
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (A l E n)) Z).mapDerivedCategory).CommShift ℤ)
  Functor.commShiftIso (exceptional l E i n) d

/-- One finite normalization, including the boundary and its uniqueness. The comparison
is a natural isomorphism on the full bounded constructible domain, independent of origins.
The last clause identifies every distinguished supported triangle with canonical middle
and open components; in particular it applies to every transported etale origin.
Source: blueprint localization, finite identification and uniqueness
(blueprint: lem-sf-finite-exceptional-site-normalization). -/
structure FiniteNormalization {X Z U : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (h : IsCompl (Set.range i) (Set.range j)) (n : ℕ)
    (J : C l E X n ⥤ C l E Z n) (a : image l E i n ⊣ J) where
  etale_preserves : ∀ K : Etale.DerivedCategoryModule (A l E n) X,
    Etale.DerivedCategory.isBoundedConstructible (A l E n) X K →
    Etale.DerivedCategory.isBoundedConstructible (A l E n) Z
      ((etaleExceptional l E i n).obj K)
  etale_triangle : ∃ δ :
      (Etale.upperStar (ModuleCat.{u + 1} (A l E n)) j).leftDerivedFunctor ⋙
        (Etale.lowerStar (ModuleCat.{u + 1} (A l E n)) j).rightDerivedFunctor ⟶
      (etaleExceptional l E i n ⋙ etaleSupport l E i n) ⋙
        shiftFunctor (Etale.DerivedCategoryModule (A l E n) X) (1 : ℤ),
    ∀ K : Etale.DerivedCategoryModule (A l E n) X,
      Etale.DerivedCategory.isBoundedConstructible (A l E n) X K →
      Triangle.mk ((Adjunction.ofIsLeftAdjoint (etaleSupport l E i n)).counit.app K)
        ((Etale.derivedUpperStarLowerStarAdjunction
          (ModuleCat.{u + 1} (A l E n)) j).unit.app K) (δ.app K) ∈ distTriang _
  comparison : (bc l E X n).ι ⋙ J ≅ (bc l E X n).ι ⋙ exceptional l E i n
  kernel_preserves : ∀ K : (bc l E X n).FullSubcategory, bc l E Z n (J.obj K.obj)
  counit_eq (K : (bc l E X n).FullSubcategory) :
    (image l E i n).map (comparison.hom.app K) ≫ counit l E i j h n K.obj =
      a.counit.app K.obj
  unit_unique (P : C l E Z n) (hP : bc l E Z n P)
      (hI : bc l E X n ((image l E i n).obj P))
      (v : P ⟶ (exceptional l E i n).obj ((image l E i n).obj P)) :
    ((image l E i n).map v ≫ counit l E i j h n ((image l E i n).obj P) = 𝟙 _) ↔
      v = a.unit.app P ≫ comparison.hom.app ⟨(image l E i n).obj P, hI⟩
  shifts (K : (bc l E X n).FullSubcategory) (d : ℤ)
      (hK : bc l E X n (K.obj⟦d⟧)) :
    comparison.hom.app ⟨K.obj⟦d⟧, hK⟩ ≫ (specifiedShift l E i n d).hom.app K.obj =
      (Adjunction.RightAdjointCommShift.iso a d).hom.app K.obj ≫
        (shiftFunctor (C l E Z n) d).map (comparison.hom.app K)
  boundary : (bc l E X n).ι ⋙ openImage l E j n ⟶
    ((bc l E X n).ι ⋙ J ⋙ image l E i n) ⋙ shiftFunctor (C l E X n) (1 : ℤ)
  distinguished (K : (bc l E X n).FullSubcategory) :
    Triangle.mk (a.counit.app K.obj) ((openUnit l E j n).app K.obj)
      (boundary.app K) ∈ distTriang (C l E X n)
  triangle_unique (K : (bc l E X n).FullSubcategory)
      (δ : (openImage l E j n).obj K.obj ⟶
        ((image l E i n).obj ((exceptional l E i n).obj K.obj))⟦(1 : ℤ)⟧)
      (hδ : Triangle.mk (counit l E i j h n K.obj) ((openUnit l E j n).app K.obj) δ ∈
        distTriang (C l E X n)) :
    ∃ e : Triangle.mk (a.counit.app K.obj) ((openUnit l E j n).app K.obj)
        (boundary.app K) ≅
      Triangle.mk (counit l E i j h n K.obj) ((openUnit l E j n).app K.obj) δ,
      e.hom.hom₁ = (image l E i n).map (comparison.hom.app K) ∧
      e.hom.hom₂ = 𝟙 K.obj ∧ e.hom.hom₃ = 𝟙 _ ∧
      ∀ e' : Triangle.mk (a.counit.app K.obj) ((openUnit l E j n).app K.obj)
          (boundary.app K) ≅
        Triangle.mk (counit l E i j h n K.obj) ((openUnit l E j n).app K.obj) δ,
        e'.hom.hom₂ = 𝟙 K.obj → e'.hom.hom₃ = 𝟙 _ → e' = e

/-- Actual positive quotient, induced by the identity on the valuation ring.
Source: blueprint localization, coefficient quotients
(blueprint: lem-sf-finite-exceptional-site-normalization). -/
def quotient {m n : ℕ} (h : n ≤ m) : A l E m →+* A l E n :=
  (Ideal.Quotient.factor
    (S := Padic.coefficientExtensionIdeal l E (m + 1))
    (T := Padic.coefficientExtensionIdeal l E (n + 1))
    (Ideal.pow_le_pow_right (Nat.succ_le_succ h))).ulift

/-- The actual finite scalar extension, without a flatness hypothesis.
Source: blueprint localization, derived reduction
(blueprint: lem-sf-finite-exceptional-site-normalization). -/
abbrev scalar (T : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :=
  ProEtale.pbcFixedScalarExtension (ProEt.topology T) (quotient l E h)

/-- Exact comparison inverse image in the recorded fixed-module coordinates.
Source: blueprint localization, etale origins
(blueprint: lem-sf-finite-exceptional-site-normalization). -/
abbrev site (T : Scheme.{u}) (n : ℕ) :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (A l E n)) T).mapDerivedCategory

/-- The origin map is the image of the actual comparison-adjunction unit.
Source: blueprint localization, origin independence
(blueprint: lem-sf-finite-exceptional-site-normalization). -/
def origin {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (n : ℕ)
    (P : Etale.DerivedCategoryModule (A l E n) X) :
    (site l E Z n).obj ((etaleExceptional l E i n).obj P) ⟶
      (exceptional l E i n).obj ((site l E X n).obj P) :=
  (site l E Z n).map ((etaleExceptional l E i n).map
    ((ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} (A l E n)) X).unit.app P))

/-- The kernel quotient map is literally the mate of inverse closed projection.
Source: blueprint localization, coefficient-extended exceptional counit
(blueprint: lem-sf-finite-exceptional-site-normalization). -/
def quotientMate {X Z : Scheme.{u}} (i : Z ⟶ X)
    (J : ∀ n : ℕ, C l E X n ⥤ C l E Z n)
    (a : ∀ n : ℕ, image l E i n ⊣ J n) {m n : ℕ} (h : n ≤ m)
    (q : image l E i m ⋙ scalar l E X h ≅ scalar l E Z h ⋙ image l E i n) :
    J m ⋙ scalar l E Z h ⟶ scalar l E X h ⋙ J n :=
  (mateEquiv (a m) (a n) (TwoSquare.mk _ _ _ _ q.inv)).natTrans

/-- Quotient compatibility with the ordinary etale counit transpose. The equation is
in the smaller coefficient category and therefore retains its complete scalar action.
Its source ranges over all constructible origins, and naturality gives the same equation
for every isomorphic pro-etale input. Only the stated boundedness of its reduction is used.
Source: blueprint localization, finite quotient normalization
(blueprint: lem-sf-finite-exceptional-site-normalization). -/
structure Quotients {X Z U : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (hij : IsCompl (Set.range i) (Set.range j))
    (J : ∀ n : ℕ, C l E X n ⥤ C l E Z n)
    (a : ∀ n : ℕ, image l E i n ⊣ J n)
    (N : ∀ n : ℕ, FiniteNormalization l E i j hij n (J n) (a n)) where
  projection {m n : ℕ} (h : n ≤ m) :
    image l E i m ⋙ scalar l E X h ≅ scalar l E Z h ⋙ image l E i n
  projection_eq {m n : ℕ} (h : n ≤ m) (P : C l E Z m) :
    (projection h).hom.app P =
      ProEtale.finiteCoefficientChangeDirectImageMap (quotient l E h) i P
  etaleProjection {m n : ℕ} (h : n ≤ m) :
    etaleSupport l E i m ⋙ Etale.scalarExtension (quotient l E h) X ≅
      Etale.scalarExtension (quotient l E h) Z ⋙ etaleSupport l E i n
  etaleProjection_eq {m n : ℕ} (h : n ≤ m) :
    (etaleProjection h).hom =
      Etale.compactScalarMap (quotient l E h) (Compactification.ofIsProper i)
  origins (n : ℕ) (P : Etale.DerivedCategoryModule (A l E n) X)
      (hP : Etale.DerivedCategory.isBoundedConstructible (A l E n) X P) :
    IsIso (origin l E i n P)
  compatible {m n : ℕ} (h : n ≤ m)
      (P : Etale.DerivedCategoryModule (A l E m) X)
      (hP : Etale.DerivedCategory.isBoundedConstructible (A l E m) X P)
      (hC : bc l E X m ((site l E X m).obj P))
      (hD : bc l E X n ((site l E X n).obj
        ((Etale.scalarExtension (quotient l E h) X).obj P))) :
    (scalar l E Z h).map (origin l E i m P) ≫
        (scalar l E Z h).map ((N m).comparison.inv.app ⟨_, hC⟩) ≫
        (quotientMate l E i J a h (projection h)).app ((site l E X m).obj P) ≫
        (J n).map ((ProEtale.pbcComparisonReduction X (quotient l E h)).hom.app P) =
      (ProEtale.pbcComparisonReduction Z (quotient l E h)).hom.app
          ((etaleExceptional l E i m).obj P) ≫
        (site l E Z n).map
          ((Etale.etaleCoefficientQuotientMate (quotient l E h)
            (Compactification.ofIsProper i)
            (Adjunction.ofIsLeftAdjoint (etaleSupport l E i m))
            (Adjunction.ofIsLeftAdjoint (etaleSupport l E i n))
            (etaleProjection h)).app P) ≫
        origin l E i n ((Etale.scalarExtension (quotient l E h) X).obj P) ≫
        (N n).comparison.inv.app ⟨_, hD⟩

/-- Finite counit normalization for the kernel adjoint. Quantifying over an adjunction
presentation includes the one constructed from ringedClosedKernelShriek; it does not
postulate an ambient exceptional adjoint for general morphisms.

Source: current blueprint, localization proof (2)--(3), finite identification
(blueprint: lem-sf-finite-exceptional-site-normalization).

Proof:
1. lem-pur-closed-unbounded-compact-support-normalization identifies etale compact
support at (id,i) with exact i_*. Uniqueness of right adjoints transports the counit.
The etale support triangle, open finiteness and lem-exc-closed-amplitude give bounded
constructible preservation; a finite dimension bound exists, including d=0 for empty X.
2. Every finite constructible input has an etale origin. Exact comparison pulls its
support triangle back. The canonical direct-image mate identifies the open arrow with
the actual open unit, and lem-pur-closed-finite-adjoint-counit-transport fixes its first
arrow. The classical support-counit identification and exact derived adjunction bounds
identify the ambient kernel adjoint with this supported first term on D+.
3. Hom(i_*P[a],Rj_*N)=0 by the open adjunction and j*i_*=0. Triangle-morphism extension
therefore gives the unique comparison with canonical middle and open components.
Its closed component is the counit transpose. This proves naturality and independence
of the origin. Transposing identities also identifies the adjunction units.
4. The closed projection formula makes the canonical scalar direct-image map invertible.
Its inverse mate is precisely quotientMate. On etale origins, scalar/site compatibility
and the counit normalizations give the same transpose on both sides of compatible.
Adjunction injectivity proves equality, with no flatness or finite-Tor assumption. -/
theorem finiteExceptionalSiteNormalization
    (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    {X Z U : Scheme.{u}} [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (h : IsCompl (Set.range i) (Set.range j))
    (J : ∀ n : ℕ, C l E X n ⥤ C l E Z n)
    (a : ∀ n : ℕ, image l E i n ⊣ J n) :
    ∃ N : ∀ n : ℕ, FiniteNormalization l E i j h n (J n) (a n),
      Nonempty (Quotients l E i j h J a N) := by
  sorry

/-- Closed compact support for any compactification is ordinary closed direct image.
This is the forget-supports map followed by the canonical derived compositor.
Source: blueprint localization, independence of compactifications
(blueprint: lem-sf-finite-exceptional-site-normalization). -/
def closedCompactIso {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (c : Compactification i) (n : ℕ) :
    Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (A l E n)) c ≅
      (Etale.lowerStar (ModuleCat.{u + 1} (A l E n)) i).rightDerivedFunctor :=
  haveI := c.isClosedImmersion_openImmersion (inferInstance : IsProper i)
  Functor.isoWhiskerRight
    (asIso (Etale.derivedOpenImmersionLowerShriekToLowerStar
      (ModuleCat.{u + 1} (A l E n)) c.i)) _ ≪≫
    Etale.rightDerivedLowerStarComp (ModuleCat.{u + 1} (A l E n)) c.i c.g ≪≫
    Etale.rightDerivedLowerStarCongr (ModuleCat.{u + 1} (A l E n)) c.comm.symm

/-- Fixed coordinates for integral reduction; this is an equivalence, not a change
in constructibility or a finite-Tor restriction.
Source: blueprint localization, integral finite reductions
(blueprint: lem-sf-finite-exceptional-site-normalization). -/
abbrev red (W : Scheme.{u}) (n : ℕ) :=
  scalarReductionDerivedExtension l E W n ⋙
    (sfIntrinsicDerivedEquivalence W (Padic.coefficientExtensionRing l E (n + 1))).inverse

/-- Closed direct-image reduction in fixed module coordinates, obtained from the
recorded scalar-unit mate and the canonical realization equivalences.
Source: blueprint localization, reduced integral counit
(blueprint: lem-sf-finite-exceptional-site-normalization). -/
def closedReduction {X Z : Scheme.{u}} (i : Z ⟶ X) (n : ℕ)
    (P : DerivedCategory (scalarReductionSource l E Z)) :
    (red l E X n).obj ((sfCompletedDerivedDirectImage l E i).obj P) ⟶
      (image l E i n).obj ((red l E Z n).obj P) :=
  let EX := sfIntrinsicDerivedEquivalence X (Padic.coefficientExtensionRing l E (n + 1))
  let EZ := sfIntrinsicDerivedEquivalence Z (Padic.coefficientExtensionRing l E (n + 1))
  let V := (scalarReductionDerivedExtension l E Z n).obj P
  EX.inverse.map ((SfExceptionalReduction.directReduction l E i n).app P) ≫
    EX.inverse.map ((proEtaleConstantDerivedDirectImage i
      (Padic.coefficientExtensionRing l E (n + 1))).map (EZ.counitIso.inv.app V)) ≫
    EX.inverse.map ((sfIntrinsicDerivedDirectImageComparison i
      (Padic.coefficientExtensionRing l E (n + 1))).hom.app (EZ.inverse.obj V)) ≫
    EX.unitIso.inv.app _

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Z U : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of D.k))] [QuasiCompact (Z ↘ Spec (.of D.k))]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (.of D.k))]

/-- Evaluation of the specified actual exceptional system. Every factor is a coordinate
counit, a site comparison, or the counit mate of closed compact support. In particular,
this map does not come from choosing a lift of finite derived arrows.
Source: blueprint localization, specified exceptional coefficient tower
(blueprint: lem-sf-finite-exceptional-site-normalization). -/
def integralEvaluation
    (K : DerivedCategory (scalarReductionSource l E X)) (n : ℕ) :
    (sfIntrinsicDerivedEquivalence Z (Padic.coefficientExtensionRing l E (n + 1))).inverse.obj
      ((coefficientSequenceDerivedEvaluation l E Z n).obj
        ((integralExceptionalSystem l E D hl i).obj K)) ≅
      (exceptional l E i n).obj ((red l E X n).obj K) :=
  let S := integralExceptionalSupport l E D hl i
  let G := integralExceptionalAdjoint l E D hl i
  let BX := integralExceptionalComparison l E X S.PY
  let BZ := integralExceptionalComparison l E Z S.PX
  let RX := (integralExceptionalEtaleRealization l E X n).mapDerivedCategory
  let RZ := (integralExceptionalEtaleRealization l E Z n).mapDerivedCategory
  let NZ := site l E Z n
  let DX := (ProEtale.comparisonLowerStar (ModuleCat.{u + 1} (A l E n)) X).rightDerivedFunctor
  let H := etaleExceptional l E i n
  let adj := (Adjunction.ofIsLeftAdjoint (etaleSupport l E i n)).ofNatIsoLeft
    (ProEtale.ClosedFiniteTransport.compactSupportIso (A l E n) i ≪≫
      (closedCompactIso l E i (integralExceptionalCompactification D i) n).symm)
  let input := (integralExceptionalDerivedCoordinates l E X).obj
    ((pullbackTensorCalculus l E X).reduction.obj K)
  let P := BX.derived.system.direct.obj input
  let Q := G.right.obj P
  let N := BZ.derived.system.inverse.obj Q
  let eX := RX.mapIso ((BX.derived.directEvaluation n).app input) ≪≫
    (integralExceptionalSiteDerivedRight l E X S.PY BX n).app _ ≪≫
    DX.mapIso (integralExceptionalCoordinatesFixed l E X BX.evaluation
      ((pullbackTensorCalculus l E X).reduction.obj K) n ≪≫
      (sfIntrinsicDerivedEquivalence X (Padic.coefficientExtensionRing l E (n + 1))).inverse.mapIso
        (((pullbackTensorCalculus l E X).reductionEvaluation n).app K))
  integralExceptionalCoordinatesInvFixed l E Z BZ.evaluation N n ≪≫
    (integralExceptionalProRealization l E Z n).mapDerivedCategory.mapIso
      ((BZ.derived.inverseEvaluation n).app Q) ≪≫
    (integralExceptionalSiteDerivedInverse l E Z S.PX BZ n).app _ ≪≫
    NZ.mapIso (RZ.mapIso ((G.evaluation n).app P) ≪≫
      (integralExceptionalEtaleRightAdjoint l E i (integralExceptionalCompactification D i)
        S n G H adj).app _ ≪≫ H.mapIso eX)

/-- The specified target reduction: reduce the limit and apply the actual
reduction/limit counit, then the fixed finite evaluation comparison.
Source: blueprint localization, normalized reduction of the exceptional limit
(blueprint: lem-sf-finite-exceptional-site-normalization). -/
def targetReduction (K : DerivedCategory (scalarReductionSource l E X)) (n : ℕ) :
    (red l E Z n).obj ((integralExceptionalInverseImage l E D hl i).obj K) ⟶
      (exceptional l E i n).obj ((red l E X n).obj K) :=
  (sfIntrinsicDerivedEquivalence Z (Padic.coefficientExtensionRing l E (n + 1))).inverse.map
    (((pullbackTensorCalculus l E Z).reductionEvaluation n).inv.app _ ≫
      (coefficientSequenceDerivedEvaluation l E Z n).map
        ((pullbackTensorCalculus l E Z).adjunction.counit.app
          ((integralExceptionalSystem l E D hl i).obj K))) ≫
    (integralEvaluation l E D hl i K n).hom

/-- The objectwise normalized level map, before any assembly is asserted.
Source: blueprint localization, counit-normalized finite reductions
(blueprint: lem-sf-finite-exceptional-site-normalization). -/
def integralLevelAt (K : DerivedCategory (scalarReductionSource l E X))
    (L : DerivedCategory (scalarReductionSource l E Z))
    (e : ∀ n : ℕ, (red l E Z n).obj L ≅
      (exceptional l E i n).obj ((red l E X n).obj K)) (n : ℕ) :
    (coefficientSequenceDerivedEvaluation l E Z n).obj
      ((pullbackTensorCalculus l E Z).reduction.obj L) ⟶
    (coefficientSequenceDerivedEvaluation l E Z n).obj
      ((integralExceptionalSystem l E D hl i).obj K) :=
  let EZ := sfIntrinsicDerivedEquivalence Z (Padic.coefficientExtensionRing l E (n + 1))
  EZ.counitIso.inv.app _ ≫
    EZ.functor.map
      (EZ.inverse.map (((pullbackTensorCalculus l E Z).reductionEvaluation n).hom.app L) ≫
        (e n).hom ≫ (integralEvaluation l E D hl i K n).inv) ≫
    EZ.counitIso.hom.app _

/-- The proposed level map, with all quotient actions retained, between evaluations
of the strict reduction and the specified exceptional system. This is only a level map;
its assembly is asserted below in the actual derived system category.
Source: blueprint localization, integral normalized finite comparisons
(blueprint: lem-sf-finite-exceptional-site-normalization). -/
def integralLevel
    (JR : DerivedCategory (scalarReductionSource l E X) ⥤
      DerivedCategory (scalarReductionSource l E Z))
    (e : ∀ n : ℕ, (sfIntegralConstructible l E X).ι ⋙ JR ⋙ red l E Z n ≅
      (sfIntegralConstructible l E X).ι ⋙ red l E X n ⋙ exceptional l E i n)
    (K : sfIntegralConstructibleCategory l E X) (n : ℕ) :
    (coefficientSequenceDerivedEvaluation l E Z n).obj
      ((pullbackTensorCalculus l E Z).reduction.obj (JR.obj K.obj)) ⟶
    (coefficientSequenceDerivedEvaluation l E Z n).obj
      ((integralExceptionalSystem l E D hl i).obj K.obj) :=
  integralLevelAt l E D hl i K.obj (JR.obj K.obj) (fun n ↦ (e n).app K) n

/-- Integral normalization on actual systems, conditional exactly on constructibility
of the kernel right adjoint and its counit-normalized coherent finite reductions.
The finite reductions are written after the finite site isomorphism; equivalently they
are the maps to J_n(K_n) of the statement. The compatibility condition is an equality
in A_m modules, before restriction to completed coefficients.

Source: current blueprint localization proof, Integral stage, final paragraph
(blueprint: lem-sf-finite-exceptional-site-normalization).

Proof:
1. Apply simultaneous strict closed reduction to the reduced integral counit. Its inverse
closed comparison gives one system map i_* R_Z(J_R K) -> R_X K. Apply the actual derived
system comparison direct image. The section-normalized closed support comparison identifies
its source with the ordinary etale system compact-support functor applied to Rnu_Z,* of
R_Z(J_R K). Transpose under the specified etale system adjunction, then apply exact
comparison inverse image and its original unit. The resulting b is already a morphism
in D of strict coefficient systems. This construction is natural in K.
2. Evaluate this constructed b. The direct-image square, universal derived evaluation,
and ordinary etale system adjunction identify its evaluation with the counit transpose
integralLevel. The finite theorem and the assumed coherent reductions show that these
are isomorphisms. Levelwise cone cohomology detects isomorphisms of actual systems;
no fullness or faithfulness of the functor to towers in a derived category is used.
3. The coefficient reduction/limit unit is invertible on integral constructible J_R K:
its intrinsic completeness is equivalent to the Roos completion unit. The valuation
ring is complete, its uniformizer regular, and its quotients finite, so the recorded
adic-datum hypotheses hold. Apply the total derived inverse limit to b and precede it
by this completion unit. This is gamma and is invertible.
4. Simultaneous strict reduction preserved the original counit and augmentation. Closed
direct image preserves limits and its exact K-injective-derived composition identifies
the system counit after the limit with the original completed counit. The inverse
transpose of gamma therefore preserves that counit; transposing identities gives the
unit equation below. All these equalities are system/adjunction equalities, not tests
of equality of derived maps on their level evaluations. -/
theorem integralExceptionalSiteNormalization
    [IsSeparated (X ↘ Spec (.of D.k))]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (hij : IsCompl (Set.range i) (Set.range j))
    (JR : DerivedCategory (scalarReductionSource l E X) ⥤
      DerivedCategory (scalarReductionSource l E Z))
    (aR : sfCompletedDerivedDirectImage l E i ⊣ JR)
    (hJR : ∀ K : sfIntegralConstructibleCategory l E X,
      sfIntegralConstructible l E Z (JR.obj K.obj))
    (e : ∀ n : ℕ, (sfIntegralConstructible l E X).ι ⋙ JR ⋙ red l E Z n ≅
      (sfIntegralConstructible l E X).ι ⋙ red l E X n ⋙ exceptional l E i n)
    (he : ∀ (n : ℕ) (K : sfIntegralConstructibleCategory l E X),
      closedReduction l E i n (JR.obj K.obj) ≫ (image l E i n).map ((e n).hom.app K) ≫
          counit l E i j hij n ((red l E X n).obj K.obj) =
        (red l E X n).map (aR.counit.app K.obj))
    (hc : ∀ (m n : ℕ) (h : n ≤ m) (K : sfIntegralConstructibleCategory l E X),
      integralLevel l E D hl i JR e K m ≫
          (coefficientSequenceDerivedTransition l E Z h).app
            ((integralExceptionalSystem l E D hl i).obj K.obj) =
        (coefficientSequenceDerivedTransition l E Z h).app
            ((pullbackTensorCalculus l E Z).reduction.obj (JR.obj K.obj)) ≫
          (normalizedDVRRes l E Z h).map (integralLevel l E D hl i JR e K n)) :
    ∃ b : (sfIntegralConstructible l E X).ι ⋙ JR ⋙
          (pullbackTensorCalculus l E Z).reduction ≅
        (sfIntegralConstructible l E X).ι ⋙ integralExceptionalSystem l E D hl i,
      (∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ),
        (coefficientSequenceDerivedEvaluation l E Z n).map (b.hom.app K) =
          integralLevel l E D hl i JR e K n) ∧
      ∃ gamma : (sfIntegralConstructible l E X).ι ⋙ JR ≅
          (sfIntegralConstructible l E X).ι ⋙ integralExceptionalInverseImage l E D hl i,
        (∀ K : sfIntegralConstructibleCategory l E X,
          gamma.hom.app K = (pullbackTensorCalculus l E Z).adjunction.unit.app (JR.obj K.obj) ≫
            (coefficientSequenceLimit l E Z).map (b.hom.app K)) ∧
        (∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ),
          (red l E Z n).map (gamma.hom.app K) ≫ targetReduction l E D hl i K.obj n =
            (e n).hom.app K) ∧
        ∃ epsilon : (sfIntegralConstructible l E X).ι ⋙
            integralExceptionalInverseImage l E D hl i ⋙ sfCompletedDerivedDirectImage l E i ⟶
          (sfIntegralConstructible l E X).ι,
          (∀ K : sfIntegralConstructibleCategory l E X,
            (sfCompletedDerivedDirectImage l E i).map (gamma.hom.app K) ≫ epsilon.app K =
              aR.counit.app K.obj) ∧
          (∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ),
            (red l E X n).map (epsilon.app K) =
              closedReduction l E i n
                  ((integralExceptionalInverseImage l E D hl i).obj K.obj) ≫
                (image l E i n).map (targetReduction l E D hl i K.obj n) ≫
                counit l E i j hij n ((red l E X n).obj K.obj)) ∧
          (∀ (P : DerivedCategory (scalarReductionSource l E Z))
            (hP : sfIntegralConstructible l E X ((sfCompletedDerivedDirectImage l E i).obj P)),
            (sfCompletedDerivedDirectImage l E i).map
                (aR.unit.app P ≫ gamma.hom.app ⟨_, hP⟩) ≫ epsilon.app ⟨_, hP⟩ = 𝟙 _) := by
  sorry

/-- Objectwise form of the integral implication, with no global constructibility
hypothesis on J_R. The comparison is a morphism of actual strict systems first;
the limit comparison is its image preceded by the specified completion unit.

Source: current blueprint localization proof, Integral stage, final paragraph
(blueprint: lem-sf-finite-exceptional-site-normalization).

Proof: perform the strict-system adjunction construction in the preceding proof on
this single input. Simultaneous strict reduction applies to its original integral
counit. The finite counit normalizations identify the evaluated transpose with
integralLevelAt; compatibility is the specified quotient-transition square. Each
level is an isomorphism, hence its actual system cone vanishes. Intrinsic completeness
of J_R K in hL identifies it with the limit of its strict reduction, via the recorded
completion unit. Applying the total limit gives gamma. The reduction/limit triangle
identity gives the targetReduction equation. This construction on the full domain of
such inputs is natural, as asserted by integralExceptionalSiteNormalization. -/
theorem integralExceptionalSiteNormalizationAt
    [IsSeparated (X ↘ Spec (.of D.k))]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (hij : IsCompl (Set.range i) (Set.range j))
    (JR : DerivedCategory (scalarReductionSource l E X) ⥤
      DerivedCategory (scalarReductionSource l E Z))
    (aR : sfCompletedDerivedDirectImage l E i ⊣ JR)
    (K : DerivedCategory (scalarReductionSource l E X))
    (hK : sfIntegralConstructible l E X K)
    (hL : sfIntegralConstructible l E Z (JR.obj K))
    (e : ∀ n : ℕ, (red l E Z n).obj (JR.obj K) ≅
      (exceptional l E i n).obj ((red l E X n).obj K))
    (he : ∀ n : ℕ,
      closedReduction l E i n (JR.obj K) ≫ (image l E i n).map (e n).hom ≫
          counit l E i j hij n ((red l E X n).obj K) =
        (red l E X n).map (aR.counit.app K))
    (hc : ∀ (m n : ℕ) (h : n ≤ m),
      integralLevelAt l E D hl i K (JR.obj K) e m ≫
          (coefficientSequenceDerivedTransition l E Z h).app
            ((integralExceptionalSystem l E D hl i).obj K) =
        (coefficientSequenceDerivedTransition l E Z h).app
            ((pullbackTensorCalculus l E Z).reduction.obj (JR.obj K)) ≫
          (normalizedDVRRes l E Z h).map
            (integralLevelAt l E D hl i K (JR.obj K) e n)) :
    ∃ b : (pullbackTensorCalculus l E Z).reduction.obj (JR.obj K) ≅
        (integralExceptionalSystem l E D hl i).obj K,
      (∀ n : ℕ, (coefficientSequenceDerivedEvaluation l E Z n).map b.hom =
        integralLevelAt l E D hl i K (JR.obj K) e n) ∧
      ∃ gamma : JR.obj K ≅ (integralExceptionalInverseImage l E D hl i).obj K,
        gamma.hom = (pullbackTensorCalculus l E Z).adjunction.unit.app (JR.obj K) ≫
          (coefficientSequenceLimit l E Z).map b.hom ∧
        (∀ n : ℕ, (red l E Z n).map gamma.hom ≫ targetReduction l E D hl i K n =
          (e n).hom) ∧
        ∃ epsilon : (sfCompletedDerivedDirectImage l E i).obj
              ((integralExceptionalInverseImage l E D hl i).obj K) ⟶ K,
          (sfCompletedDerivedDirectImage l E i).map gamma.hom ≫ epsilon = aR.counit.app K ∧
          ∀ n : ℕ, (red l E X n).map epsilon =
            closedReduction l E i n ((integralExceptionalInverseImage l E D hl i).obj K) ≫
              (image l E i n).map (targetReduction l E D hl i K n) ≫
              counit l E i j hij n ((red l E X n).obj K) := by
  sorry

end WeilConjectures.FiniteExceptionalNormalization
