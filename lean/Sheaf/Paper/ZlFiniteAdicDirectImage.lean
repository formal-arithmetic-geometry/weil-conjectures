/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Sheaf.Paper.SfConstructibleHeart
public import Sheaf.Paper.SfDerivedDirectImage
public import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
public import Sheaf.Paper.SfIntegralReductionTower
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Sheaf.Paper.LocalFrobeniusTrace
public import Sheaf.Paper.CommonStageCompactWeilCohomology
public import Sheaf.Paper.ConstructiblePullbackTExact
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Algebra.DirectSum.Module
public import Sheaf.AlgebraicGeometry.ProEtaleUnitLerayChainFormula
public import WeilConjectures.CategoryTheory.StageSystem.Functor

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.PbcQbarStandardCohomology
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Sheaf.Paper.IntegralDerivedOperationsOnSlices
import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
import Sheaf.Paper.SfIntegralConstructible
import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
import Sheaf.Paper.SfDerivedComplete
import Sheaf.Paper.FiniteCoefficientPoint
import Sheaf.Paper.IntegralUniformCoefficient
import Sheaf.Paper.PbcRationalCategory
import Sheaf.Paper.SfRationalizationKaroubi
import Sheaf.Paper.ExactProductFunctorStrictLimit
import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.Paper.IntegralPullbackComposition
import Sheaf.CategoryTheory.Triangulated.TExactTruncationComparison
import Sheaf.Paper.IntegralOperationsPreserveConstructible
import Sheaf.Paper.IntegralOperationsScalarComparisons
import Sheaf.Paper.SfIntegralDirectImageConstructible
import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import Sheaf.Paper.ProEtaleConstructibleOrigin
import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import WeilConjectures.AlgebraicGeometry.SpecAlgClosedEtaleSheafConstant
import Sheaf.Paper.PointProEtaleSectionsExact
import Sheaf.Paper.PointSectionsScalarExtension
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import WeilConjectures.SixFunctors.Finite.BaseChange
import WeilConjectures.SixFunctors.Finite.Stalk
import Sheaf.AlgebraicGeometry.FinitePresentationOfFiniteLocallyNoetherian
import Sheaf.Paper.LocalizedTStructure
import Sheaf.Paper.PbcRationalTransport
import Sheaf.Paper.PbcScalarExtension
import WeilConjectures.SixFunctors.Finite.Exact
import Sheaf.AlgebraicGeometry.FiniteFpProEtalePushforwardExact
import Sheaf.Paper.SfCommonStageDirectImage

/-! # Finite direct image at rational adic coefficients

Source: Stacks Project, Tags 03QP and 09A8; Bhatt--Scholze, Proposition 6.8.14
and Remark 6.8.15 (blueprint: lem-zl-finite-adic-direct-image).

## Main definitions and statement

- `ZlFiniteAdicDirectImageData`: the finite-field and common-stage clauses.
- `zlFiniteAdicExchange` and `zlFiniteAdicEvaluation`: canonical counit restrictions.
- `zlFiniteAdicStalkToSum`: the linear map with those geometric germ components.
- `zlFiniteAdicFiniteCounit`: the section-normalized finite derived counit.
- `zlFiniteAdicFibreRestriction`, `zlFiniteAdicFibreToSum`: the actual ordinary H0 arrows.
- `zlFiniteAdicDirectImage`: existence of the complete specified finite-image system.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOf false

universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated AlgebraicGeometry
open DirectSum
namespace WeilConjectures

/-- The geometric objects quantified over in the finite-image theorem, bundled only
for the simultaneous naturality clauses. The structure morphism, finite type and
separatedness are the original hypotheses.
Source: finite-image statement (blueprint: lem-zl-finite-adic-direct-image). -/
structure ZlFiniteAdicSpace (D : FiniteFieldDatum.{u}) where
  space : Over (Spec (.of D.k))
  [finiteType : LocallyOfFiniteType space.hom]
  [quasiCompact : QuasiCompact space.hom]
  [separated : IsSeparated space.hom]

attribute [instance] ZlFiniteAdicSpace.finiteType ZlFiniteAdicSpace.quasiCompact
  ZlFiniteAdicSpace.separated

/-- The bundled structure morphism, as the standard scheme-over-base instance.
Source: geometric hypotheses (blueprint: lem-zl-finite-adic-direct-image). -/
instance zlFiniteAdicSpaceOver {D : FiniteFieldDatum.{u}} (X : ZlFiniteAdicSpace D) :
    X.space.left.Over (Spec (.of D.k)) := ⟨X.space.hom⟩

/-- Finite type from the bundled geometric hypothesis.
Source: geometric hypotheses (blueprint: lem-zl-finite-adic-direct-image). -/
instance zlFiniteAdicSpaceFiniteType {D : FiniteFieldDatum.{u}} (X : ZlFiniteAdicSpace D) :
    LocallyOfFiniteType (X.space.left ↘ Spec (.of D.k)) := X.finiteType

/-- Quasi-compactness from the bundled geometric hypothesis.
Source: geometric hypotheses (blueprint: lem-zl-finite-adic-direct-image). -/
instance zlFiniteAdicSpaceQuasiCompact {D : FiniteFieldDatum.{u}} (X : ZlFiniteAdicSpace D) :
    QuasiCompact (X.space.left ↘ Spec (.of D.k)) := X.quasiCompact

/-- Separatedness from the bundled geometric hypothesis.
Source: geometric hypotheses (blueprint: lem-zl-finite-adic-direct-image). -/
instance zlFiniteAdicSpaceSeparated {D : FiniteFieldDatum.{u}} (X : ZlFiniteAdicSpace D) :
    IsSeparated (X.space.left ↘ Spec (.of D.k)) := X.separated

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)

/-- The point object of the geometric category.
Source: geometric-fibre clause (blueprint: lem-zl-finite-adic-direct-image). -/
def zlFiniteAdicPoint : ZlFiniteAdicSpace D where
  space := Over.mk (𝟙 (Spec (.of D.k)))
  finiteType := inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (.of D.k))))
  quasiCompact := inferInstanceAs (QuasiCompact (𝟙 (Spec (.of D.k))))
  separated := inferInstanceAs (IsSeparated (𝟙 (Spec (.of D.k))))

/-- The geometric finite fibre, with its second projection as structure map.
Source: geometric-fibre clause (blueprint: lem-zl-finite-adic-direct-image). -/
def zlFiniteAdicFibre {X Y : ZlFiniteAdicSpace D}
    (f : X.space.left ⟶ Y.space.left) [IsFinite f]
    (y : Spec (.of D.k) ⟶ Y.space.left) : ZlFiniteAdicSpace D where
  space := Over.mk (pullback.snd f y)
  finiteType := inferInstanceAs (LocallyOfFiniteType (pullback.snd f y))
  quasiCompact := inferInstanceAs (QuasiCompact (pullback.snd f y))
  separated := inferInstanceAs (IsSeparated (pullback.snd f y))

/-- Finiteness of the structure map of the chosen geometric fibre.
Source: finite base change, Stacks 01WG
(blueprint: lem-zl-finite-adic-direct-image). -/
instance zlFiniteAdicFibreFinite {X Y : ZlFiniteAdicSpace D}
    (f : X.space.left ⟶ Y.space.left) [IsFinite f]
    (y : Spec (.of D.k) ⟶ Y.space.left) :
    IsFinite (zlFiniteAdicFibre D f y).space.hom :=
  inferInstanceAs (IsFinite (pullback.snd f y))

/-- The existing rational pullback, using the inherited residue-unit structure.
Source: inverse-image and stalk convention
(blueprint: lem-zl-finite-adic-direct-image). -/
abbrev zlFiniteAdicPull (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] {X Y : ZlFiniteAdicSpace D}
    (f : X.space.left ⟶ Y.space.left) :=
  @rationalDerivedPullback l _ E _ _ _ _ _ f
    (constructiblePullbackResidueUnits D l hl X.space.left)
    (constructiblePullbackResidueUnits D l hl Y.space.left)

/-- The recorded integral pullback, with exactly the same residue-unit instances
as its rationalization. Source: Stacks 099N(5), integral pullback convention
(blueprint: lem-zl-finite-adic-direct-image). -/
abbrev zlFiniteAdicIntegralPull (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] {X Y : ZlFiniteAdicSpace D}
    (f : X.space.left ⟶ Y.space.left) :=
  @constructibleIntegralPullback l _ E _ _ _ _ _ f
    (constructiblePullbackResidueUnits D l hl X.space.left)
    (constructiblePullbackResidueUnits D l hl Y.space.left)

/-- The finite-reduction map of the recorded completed direct image. Its transpose
is direct image of the scalar-extension unit followed by the recorded, resolution-
normalized restriction comparison. In particular no new comparison is chosen.
Source: Stacks 0D6E, 07A6; integral direct-image proof, Step 3
(blueprint: lem-zl-finite-adic-direct-image). -/
def zlFiniteAdicImageReduction (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] {X Y : ZlFiniteAdicSpace D}
    (f : X.space.left ⟶ Y.space.left)
    (I : sfIntegralConstructibleCategory l E X.space.left ⥤
      sfIntegralConstructibleCategory l E Y.space.left)
    (e : I ⋙ (sfIntegralConstructible l E Y.space.left).ι ≅
      (sfIntegralConstructible l E X.space.left).ι ⋙ sfCompletedDerivedDirectImage l E f)
    (K : sfIntegralConstructibleCategory l E X.space.left) (n : ℕ) :
    (scalarReductionDerivedExtension l E Y.space.left n).obj (I.obj K).obj ⟶
      sfFiniteDerivedDirectImage l E f K.obj n :=
  ((derivedScalarExtensionRestrictionAdjunction l E Y.space.left n).choose.homEquiv
    _ _).symm
    (e.hom.app K ≫
      (sfCompletedDerivedDirectImage l E f).map
        ((derivedScalarExtensionRestrictionAdjunction l E X.space.left n).choose.unit.app
          K.obj) ≫
      (sfDerivedRestrictionComparison l E f n).hom.app
        ((scalarReductionDerivedExtension l E X.space.left n).obj K.obj))

/-- The finite-level counit for the actual sectionwise direct image. The comparison
of its two direct-image presentations is the identity on sections; the adjunction
is the recorded tensor-unit-normalized adjunction, then its derived adjunction.
Source: Stacks 03D3, 07A6, 03QP
(blueprint: lem-zl-finite-adic-direct-image). -/
def zlFiniteAdicFiniteCounit (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] {X Y : ZlFiniteAdicSpace D}
    (f : X.space.left ⟶ Y.space.left) (n : ℕ) :
    AlgebraicGeometry.Scheme.proEtaleConstantDerivedDirectImage f
        (Padic.coefficientExtensionRing l E (n + 1)) ⋙
      AlgebraicGeometry.Scheme.proEtaleConstantRingDerivedPullback
        (Padic.coefficientExtensionRing l E (n + 1)) f ⟶ 𝟭 _ :=
  letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  (((AlgebraicGeometry.Scheme.proEtaleConstantRingAdjunction
    (Padic.coefficientExtensionRing l E (n + 1)) f).ofNatIsoRight
      (AlgebraicGeometry.Scheme.proEtaleUnitLerayDirectImageIso
        (Padic.coefficientExtensionRing l E (n + 1)) f)).mapDerivedCategoryRightDerivedAdjunction
          ).counit

/-- A rational finite direct image, identified with the actual completed derived
image before localization. The integral counit has the prescribed finite reductions
through integralComparison, and the rational counit is its localization through
rationalComparison and the recorded pullback comparison. These equations normalize
the adjunction used by every later restriction map against the recorded direct image.
The exact-heart and cohomology data use the existing standard t-structures.
Source: Stacks 03QP, 09A8; Bhatt--Scholze 6.8.14 and 6.8.15
(blueprint: lem-zl-finite-adic-direct-image). -/
structure ZlFiniteAdicRationalImage (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] {X Y : ZlFiniteAdicSpace D}
    (f : X.space.left ⟶ Y.space.left) where
  integral : sfIntegralConstructibleCategory l E X.space.left ⥤
    sfIntegralConstructibleCategory l E Y.space.left
  integral_obj : ∀ K : sfIntegralConstructibleCategory l E X.space.left,
    (integral.obj K).obj = (sfCompletedDerivedDirectImage l E f).obj K.obj
  integralComparison : integral ⋙ (sfIntegralConstructible l E Y.space.left).ι ≅
    (sfIntegralConstructible l E X.space.left).ι ⋙ sfCompletedDerivedDirectImage l E f
  integralComparison_normalized : ∀ K : sfIntegralConstructibleCategory l E X.space.left,
    integralComparison.hom.app K = eqToHom (integral_obj K)
  functor : sfRationalConstructibleCategory l E X.space.left ⥤
    sfRationalConstructibleCategory l E Y.space.left
  rational_obj : ∀ K : sfRationalConstructibleCategory l E X.space.left,
    functor.obj K = (sfRationalConstructibleLocalization l E Y.space.left).obj
      (integral.obj K.obj)
  rationalComparison : sfRationalConstructibleLocalization l E X.space.left ⋙ functor ≅
    integral ⋙ sfRationalConstructibleLocalization l E Y.space.left
  rationalComparison_normalized : ∀ K : sfIntegralConstructibleCategory l E X.space.left,
    rationalComparison.hom.app K =
      eqToHom (rational_obj ((sfRationalConstructibleLocalization l E X.space.left).obj K))
  integralCounit : integral ⋙ zlFiniteAdicIntegralPull D l hl E f ⟶ 𝟭 _
  integralCounit_reduction : ∀ (K : sfIntegralConstructibleCategory l E X.space.left)
    (P : (integralOperationsGoodComplex l E Y.space.left).FullSubcategory)
    (e : DerivedCategory.Q.obj P.obj ≅ (integral.obj K).obj) (n : ℕ),
    (scalarReductionDerivedExtension l E X.space.left n).map
        (integralCounit.app K).hom =
      (@integralPullbackReductionIso l _ E _ _ _ _ _ f
        (constructiblePullbackResidueUnits D l hl X.space.left)
        (constructiblePullbackResidueUnits D l hl Y.space.left)
        (integral.obj K) P e n).hom ≫
      (AlgebraicGeometry.Scheme.proEtaleConstantRingDerivedPullback
        (Padic.coefficientExtensionRing l E (n + 1)) f).map
          (zlFiniteAdicImageReduction D l E f integral integralComparison K n) ≫
      (zlFiniteAdicFiniteCounit D l E f n).app
        ((scalarReductionDerivedExtension l E X.space.left n).obj K.obj)
  adjunction : zlFiniteAdicPull D l hl E f ⊣ functor
  counit_localization : ∀ K : sfIntegralConstructibleCategory l E X.space.left,
    adjunction.counit.app ((sfRationalConstructibleLocalization l E X.space.left).obj K) =
      (zlFiniteAdicPull D l hl E f).map (rationalComparison.hom.app K) ≫
      (@localPullbackObjectIso l _ E _ _ _ _ _ f
        (constructiblePullbackResidueUnits D l hl X.space.left)
        (constructiblePullbackResidueUnits D l hl Y.space.left)
        ((sfRationalConstructibleLocalization l E Y.space.left).obj (integral.obj K))).hom ≫
      (sfRationalConstructibleLocalization l E X.space.left).map (integralCounit.app K)
  exactness : ConstructiblePullbackComparison
    (sfRationalStandardTStructure l E X.space.left D hl)
    (sfRationalStandardTStructure l E Y.space.left D hl)
    (sfRationalHeartProperty l E X.space.left) (sfRationalHeartProperty l E Y.space.left)
    functor

variable (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]

/-- The recorded rational composition comparison, with all geometric hypotheses inherited.
Source: integral pullback composition and local stalk convention
(blueprint: lem-zl-finite-adic-direct-image). -/
abbrev zlFiniteAdicComposition {X Y Z : ZlFiniteAdicSpace D}
    (f : X.space.left ⟶ Y.space.left) (g : Y.space.left ⟶ Z.space.left)
    (K : sfRationalConstructibleCategory l E Z.space.left) :=
  @localPullbackComposition l _ E _ _ _ _ _ _ f g
    (constructiblePullbackResidueUnits D l hl X.space.left)
    (constructiblePullbackResidueUnits D l hl Y.space.left)
    (constructiblePullbackResidueUnits D l hl Z.space.left) K

/-- H⁰ of the recorded coefficient point fibre.
Source: coefficient stalk convention (blueprint: lem-zl-finite-adic-direct-image). -/
def zlFiniteAdicPointH0 :=
  pointRationalFibre D l hl E ⋙ DerivedCategory.coefficientFdCohomology E 0

/-- The actual geometric stalk, expressed through the dependency's derived point fibre.
Source: local Frobenius trace, underlying point complex
(blueprint: lem-zl-finite-adic-direct-image). -/
def zlFiniteAdicStalk (X : ZlFiniteAdicSpace D)
    (x : Spec (.of D.k) ⟶ X.space.left) :
    sfRationalConstructibleCategory l E X.space.left ⥤ ModuleCat.{u} E :=
  zlFiniteAdicPull D l hl E (X := zlFiniteAdicPoint D) x ⋙ zlFiniteAdicPointH0 D l hl E

/-- The finite set indexing the sum: all geometric lifts, with the equation included.
Source: Stacks 03QP(1) (blueprint: lem-zl-finite-adic-direct-image). -/
abbrev ZlFiniteAdicLifts {X Y : ZlFiniteAdicSpace D}
    (f : X.space.left ⟶ Y.space.left) (y : Spec (.of D.k) ⟶ Y.space.left) :=
  {x : Spec (.of D.k) ⟶ X.space.left // x ≫ f = y}

/-- Restriction at one geometric lift, before taking point sections. It is the
pullback of the direct-image counit, preceded by the canonical composition map.
Source: Stacks 03QP(1), restriction/germ map
(blueprint: lem-zl-finite-adic-direct-image). -/
def zlFiniteAdicEvaluation {X Y : ZlFiniteAdicSpace D}
    {f : X.space.left ⟶ Y.space.left}
    (F : ZlFiniteAdicRationalImage D l hl E f)
    (y : Spec (.of D.k) ⟶ Y.space.left) (x : ZlFiniteAdicLifts D f y)
    (K : sfRationalConstructibleCategory l E X.space.left) :
    (zlFiniteAdicPull D l hl E (X := zlFiniteAdicPoint D) y).obj (F.functor.obj K) ⟶
      (zlFiniteAdicPull D l hl E (X := zlFiniteAdicPoint D) x.val).obj K :=
  (eqToIso (congrArg (fun g ↦
    (zlFiniteAdicPull D l hl E (X := zlFiniteAdicPoint D) g).obj (F.functor.obj K))
      x.property.symm)).hom ≫
    (zlFiniteAdicComposition D l hl E (X := zlFiniteAdicPoint D) x.val f
      (F.functor.obj K)).hom ≫
    (zlFiniteAdicPull D l hl E (X := zlFiniteAdicPoint D) x.val).map
      (F.adjunction.counit.app K)

/-- The canonical exchange map of a commuting square. It is the adjoint of
pullback of the counit, using the specified composition comparison on each side.
No cartesianness is needed to construct this arrow.
Source: Stacks 0959, counit construction
(blueprint: lem-zl-finite-adic-direct-image). -/
def zlFiniteAdicExchange {X Y X' Y' : ZlFiniteAdicSpace D}
    {f : X.space.left ⟶ Y.space.left} {f' : X'.space.left ⟶ Y'.space.left}
    (F : ZlFiniteAdicRationalImage D l hl E f)
    (F' : ZlFiniteAdicRationalImage D l hl E f')
    (a : X'.space.left ⟶ X.space.left) (b : Y'.space.left ⟶ Y.space.left)
    (w : a ≫ f = f' ≫ b) (K : sfRationalConstructibleCategory l E X.space.left) :
    (zlFiniteAdicPull D l hl E b).obj (F.functor.obj K) ⟶
      F'.functor.obj ((zlFiniteAdicPull D l hl E a).obj K) :=
  (F'.adjunction.homEquiv _ _)
    ((zlFiniteAdicComposition D l hl E f' b (F.functor.obj K)).inv ≫
      (eqToIso (congrArg (fun g ↦ (zlFiniteAdicPull D l hl E g).obj
        (F.functor.obj K)) w.symm)).hom ≫
      (zlFiniteAdicComposition D l hl E a f (F.functor.obj K)).hom ≫
      (zlFiniteAdicPull D l hl E a).map (F.adjunction.counit.app K))

/-- Transport of a point pullback in a commuting square, with a possibly semilinear
point isomorphism. Both arrows are the recorded composition comparisons.
Source: diagram naturality clause (blueprint: lem-zl-finite-adic-direct-image). -/
def zlFiniteAdicPointTransport {X X' : ZlFiniteAdicSpace D}
    (a : X'.space.left ⟶ X.space.left)
    (σ : (zlFiniteAdicPoint D).space.left ⟶ (zlFiniteAdicPoint D).space.left)
    (x : Spec (.of D.k) ⟶ X.space.left) (x' : Spec (.of D.k) ⟶ X'.space.left)
    (w : x' ≫ a = σ ≫ x) (K : sfRationalConstructibleCategory l E X.space.left) :
    (zlFiniteAdicPull D l hl E (X := zlFiniteAdicPoint D) x').obj
        ((zlFiniteAdicPull D l hl E a).obj K) ≅
      (zlFiniteAdicPull D l hl E (X := zlFiniteAdicPoint D)
        (Y := zlFiniteAdicPoint D) σ).obj
          ((zlFiniteAdicPull D l hl E (X := zlFiniteAdicPoint D) x).obj K) :=
  (zlFiniteAdicComposition D l hl E (X := zlFiniteAdicPoint D) x' a K).symm ≪≫
    eqToIso (congrArg (fun g ↦
      (zlFiniteAdicPull D l hl E (X := zlFiniteAdicPoint D) g).obj K) w) ≪≫
    zlFiniteAdicComposition D l hl E (X := zlFiniteAdicPoint D)
      (Y := zlFiniteAdicPoint D) σ x K

open Classical in
/-- The unique linear map into a finite direct sum with the supplied components.
It is constructed by the finite direct-sum/product equivalence, including an empty set.
Source: Stacks 03QP(1) (blueprint: lem-zl-finite-adic-direct-image). -/
def zlFiniteAdicModuleSumMap {R : Type v} [Ring R] (I : Type u) [Finite I]
    (V : I → ModuleCat.{max u v} R) {M : ModuleCat.{max u v} R}
    (e : ∀ i : I, M ⟶ V i) : M ⟶ ModuleCat.of R (⨁ i : I, V i) := by
  letI := Fintype.ofFinite I
  exact ModuleCat.ofHom
    ((DirectSum.linearEquivFunOnFintype R I (fun i ↦ V i)).symm.toLinearMap.comp
      (LinearMap.pi (fun i ↦ (e i).hom)))

/-- The restriction map from the image stalk to the direct sum of the source stalks.
Every component is the actual counit restriction, so no unspecified map occurs.
Source: Stacks 03QP(1) (blueprint: lem-zl-finite-adic-direct-image). -/
def zlFiniteAdicStalkToSum {X Y : ZlFiniteAdicSpace D}
    (f : X.space.left ⟶ Y.space.left)
    (F : ZlFiniteAdicRationalImage D l hl E f)
    (y : Spec (.of D.k) ⟶ Y.space.left) (h : Finite (ZlFiniteAdicLifts D f y))
    (K : sfRationalConstructibleCategory l E X.space.left) :=
  @zlFiniteAdicModuleSumMap E _ (ZlFiniteAdicLifts D f y) h
    (fun x ↦ (zlFiniteAdicStalk D l hl E X x.val).obj K) _
    (fun x ↦ (zlFiniteAdicPointH0 D l hl E).map
      (zlFiniteAdicEvaluation D l hl E F y x K))

/-- The two canonical restrictions are invertible on sheaves. The map to the middle
term is the exchange/counit map. The map from the middle term to the finite sum is
its inverse followed by the explicitly constructed stalk-to-sum restriction.
The ordinary comparison in the system below identifies that middle term with H⁰(S,F_S).
Source: Stacks 03QP(1), 0959; Bhatt--Scholze 6.8.14
(blueprint: lem-zl-finite-adic-direct-image). -/
structure ZlFiniteAdicFibreComparison {X Y : ZlFiniteAdicSpace D}
    (f : X.space.left ⟶ Y.space.left) [IsFinite f]
    (F : ZlFiniteAdicRationalImage D l hl E f)
    (y : Spec (.of D.k) ⟶ Y.space.left)
    (H : ZlFiniteAdicRationalImage D l hl E
      (X := zlFiniteAdicFibre D f y) (Y := zlFiniteAdicPoint D) (pullback.snd f y)) where
  finite : Finite (ZlFiniteAdicLifts D f y)
  baseChange : ∀ K : sfRationalHeart l E X.space.left,
    IsIso ((zlFiniteAdicPointH0 D l hl E).map
      (zlFiniteAdicExchange D l hl E F H (pullback.fst f y) y
        pullback.condition K.obj))
  stalkToSum : ∀ K : sfRationalHeart l E X.space.left,
    IsIso (zlFiniteAdicStalkToSum D l hl E f F y finite K.obj)

/-- The actual Roos projection in the recorded ordinary-cohomology definition.
This exposes the very same witness selected by integralImage, without choosing a
new direct image or a comparison. Its domain is definitionally that recorded image.
Source: ordinary-cohomology definition, integralImage; Stacks 07A6
(blueprint: lem-zl-finite-adic-direct-image). -/
def zlFiniteAdicOrdinaryProjection (X : ZlFiniteAdicSpace D)
    (K : sfIntegralConstructibleCategory l E X.space.left) (n : ℕ) :
    (integralImage D l hl E X.space.left K).obj ⟶
      sfDirectImageTerm l E X.space.hom K.obj n := by
  letI : (Spec (.of D.k)).Over (Spec (.of D.k)) := ⟨𝟙 _⟩
  letI : (X.space.left ↘ Spec (.of D.k)).IsOver (Spec (.of D.k)) := inferInstance
  let h := sfIntegralDirectImage_constructible D.k l (finiteFieldDatumPrimeUnit D l hl)
    E (X.space.left ↘ Spec (.of D.k)) K.obj K.property
  letI := h.1.choose
  let L : SfIntegralDirectImage l E (X.space.left ↘ Spec (.of D.k)) K.obj :=
    h.1.choose_spec.some
  exact L.projection ≫ Pi.π _ n

/-- Comparison with the recorded ordinary image, including its specified projections.
The subtype retains its actual comparison and the equation on every projection,
without generating new constructor laws for these already existing objects.
Source: ordinary-cohomology definition and direct-image comparison, Stacks 07A6
(blueprint: lem-zl-finite-adic-direct-image). -/
def ZlFiniteAdicOrdinaryData (X : ZlFiniteAdicSpace D)
    (F : ZlFiniteAdicRationalImage D l hl E (X := X) (Y := zlFiniteAdicPoint D) X.space.hom)
    (K : sfIntegralConstructibleCategory l E X.space.left) :=
  { comparison : F.integral.obj K ≅ integralImage D l hl E X.space.left K //
    ∀ n : ℕ,
      comparison.hom.hom ≫ zlFiniteAdicOrdinaryProjection D l hl E X K n =
        ((derivedScalarExtensionRestrictionAdjunction l E (Spec (.of D.k)) n).choose.homEquiv
          _ _) (zlFiniteAdicImageReduction D l E (X := X) (Y := zlFiniteAdicPoint D)
            X.space.hom F.integral F.integralComparison K n) }

/-- One finite-coefficient-field clause, simultaneously for all finite morphisms so
that its canonical restrictions and diagram transports can be compared. The ordinary
comparison identifies the middle term with the dependency's H⁰(S,F_S). Exactness
and all Hʲ comparisons are the fields of image.exactness. Naturality of both displayed
isomorphisms follows from exchangeNatural, evaluationNatural and the finite-sum
universal property.
Source: Stacks 03QP, 0959; Bhatt--Scholze 6.8.14, 6.8.15
(blueprint: lem-zl-finite-adic-direct-image). -/
structure ZlFiniteAdicRationalSystem where
  image : ∀ {X Y : ZlFiniteAdicSpace D} (f : X.space.left ⟶ Y.space.left) [IsFinite f],
    ZlFiniteAdicRationalImage D l hl E f
  ordinary : ∀ (X : ZlFiniteAdicSpace D) [IsFinite X.space.hom]
    (K : sfIntegralConstructibleCategory l E X.space.left),
    ZlFiniteAdicOrdinaryData D l hl E X
      (image (X := X) (Y := zlFiniteAdicPoint D) X.space.hom) K
  fibre : ∀ {X Y : ZlFiniteAdicSpace D} (f : X.space.left ⟶ Y.space.left) [IsFinite f]
    (y : Spec (.of D.k) ⟶ Y.space.left),
    ZlFiniteAdicFibreComparison D l hl E f (image f) y
      (image (X := zlFiniteAdicFibre D f y) (Y := zlFiniteAdicPoint D) (pullback.snd f y))
  exchangeNatural : ∀ {X Y X' Y' : ZlFiniteAdicSpace D}
    (f : X.space.left ⟶ Y.space.left) [IsFinite f]
    (f' : X'.space.left ⟶ Y'.space.left) [IsFinite f']
    (a : X'.space.left ⟶ X.space.left) (b : Y'.space.left ⟶ Y.space.left)
    (w : a ≫ f = f' ≫ b)
    (K L : sfRationalConstructibleCategory l E X.space.left) (t : K ⟶ L),
    (zlFiniteAdicPull D l hl E b).map ((image f).functor.map t) ≫
        zlFiniteAdicExchange D l hl E (image f) (image f') a b w L =
      zlFiniteAdicExchange D l hl E (image f) (image f') a b w K ≫
        (image f').functor.map ((zlFiniteAdicPull D l hl E a).map t)
  evaluationNatural : ∀ {X Y : ZlFiniteAdicSpace D}
    (f : X.space.left ⟶ Y.space.left) [IsFinite f]
    (y : Spec (.of D.k) ⟶ Y.space.left) (x : ZlFiniteAdicLifts D f y)
    (K L : sfRationalConstructibleCategory l E X.space.left) (t : K ⟶ L),
    zlFiniteAdicEvaluation D l hl E (image f) y x K ≫
        (zlFiniteAdicPull D l hl E (X := zlFiniteAdicPoint D) x.val).map t =
      (zlFiniteAdicPull D l hl E (X := zlFiniteAdicPoint D) y).map
          ((image f).functor.map t) ≫
        zlFiniteAdicEvaluation D l hl E (image f) y x L
  diagramNatural : ∀ {X Y X' Y' : ZlFiniteAdicSpace D}
    (f : X.space.left ⟶ Y.space.left) [IsFinite f]
    (f' : X'.space.left ⟶ Y'.space.left) [IsFinite f']
    (a : X'.space.left ≅ X.space.left) (b : Y'.space.left ≅ Y.space.left)
    (σ : (zlFiniteAdicPoint D).space.left ≅ (zlFiniteAdicPoint D).space.left)
    (w : a.hom ≫ f = f' ≫ b.hom)
    (y : Spec (.of D.k) ⟶ Y.space.left) (y' : Spec (.of D.k) ⟶ Y'.space.left)
    (wy : y' ≫ b.hom = σ.hom ≫ y)
    (x : ZlFiniteAdicLifts D f y) (x' : ZlFiniteAdicLifts D f' y')
    (wx : x'.val ≫ a.hom = σ.hom ≫ x.val)
    (K : sfRationalConstructibleCategory l E X.space.left),
    (zlFiniteAdicPull D l hl E (X := zlFiniteAdicPoint D) y').map
        (zlFiniteAdicExchange D l hl E (image f) (image f') a.hom b.hom w K) ≫
      zlFiniteAdicEvaluation D l hl E (image f') y' x'
        ((zlFiniteAdicPull D l hl E a.hom).obj K) =
      (zlFiniteAdicPointTransport D l hl E b.hom σ.hom y y' wy
          ((image f).functor.obj K)).hom ≫
        (zlFiniteAdicPull D l hl E (X := zlFiniteAdicPoint D)
          (Y := zlFiniteAdicPoint D) σ.hom).map
            (zlFiniteAdicEvaluation D l hl E (image f) y x K) ≫
        (zlFiniteAdicPointTransport D l hl E a.hom σ.hom x.val x'.val wx K).inv

/-- The normalized comparison with the actual ordinary-cohomology object. Its
integral map preserves the recorded Roos projections; its rational map is literally
that map tensored with one, after the prescribed object identification.
Source: ordinary-cohomology and restriction clauses; Stacks 07A6
(blueprint: lem-zl-finite-adic-direct-image). -/
def zlFiniteAdicOrdinaryComparison (R : ZlFiniteAdicRationalSystem D l hl E)
    (X : ZlFiniteAdicSpace D) [IsFinite X.space.hom]
    (K : sfRationalConstructibleCategory l E X.space.left) :
    (R.image (X := X) (Y := zlFiniteAdicPoint D) X.space.hom).functor.obj K ≅
      rationalImage D l hl E X.space.left K :=
  eqToIso ((R.image (X := X) (Y := zlFiniteAdicPoint D) X.space.hom).rational_obj K) ≪≫
    (sfRationalConstructibleLocalization l E (Spec (.of D.k))).mapIso
      (R.ordinary X K.obj).val

/-- The first displayed restriction, with actual ordinary H0 as its target.
The exchange is followed by the Roos-projection-normalized ordinary comparison.
Source: Stacks 03QP(1), 0959; ordinary-cohomology clause
(blueprint: lem-zl-finite-adic-direct-image). -/
def zlFiniteAdicFibreRestriction (R : ZlFiniteAdicRationalSystem D l hl E)
    {X Y : ZlFiniteAdicSpace D} (f : X.space.left ⟶ Y.space.left) [IsFinite f]
    (y : Spec (.of D.k) ⟶ Y.space.left)
    (K : sfRationalConstructibleCategory l E X.space.left) :
    (zlFiniteAdicStalk D l hl E Y y).obj ((R.image f).functor.obj K) ⟶
      (zlFiniteAdicPointH0 D l hl E).obj
        (rationalImage D l hl E (zlFiniteAdicFibre D f y).space.left
          ((zlFiniteAdicPull D l hl E (X := zlFiniteAdicFibre D f y) (Y := X)
            (pullback.fst f y)).obj K)) :=
  (zlFiniteAdicPointH0 D l hl E).map
      (zlFiniteAdicExchange D l hl E (R.image f)
        (R.image (X := zlFiniteAdicFibre D f y) (Y := zlFiniteAdicPoint D) (pullback.snd f y))
        (pullback.fst f y) y pullback.condition K) ≫
    (zlFiniteAdicPointH0 D l hl E).map
      (zlFiniteAdicOrdinaryComparison D l hl E R (zlFiniteAdicFibre D f y)
        ((zlFiniteAdicPull D l hl E (X := zlFiniteAdicFibre D f y) (Y := X)
          (pullback.fst f y)).obj K)).hom

/-- The second displayed restriction, from actual ordinary H0 to the finite sum.
Undo only the normalized ordinary comparison and invertible exchange, then apply
the explicitly counit-normalized germ map to the finite sum.
Source: Stacks 03QP(1), 0959; finite-fibre restriction clause
(blueprint: lem-zl-finite-adic-direct-image). -/
def zlFiniteAdicFibreToSum (R : ZlFiniteAdicRationalSystem D l hl E)
    {X Y : ZlFiniteAdicSpace D} (f : X.space.left ⟶ Y.space.left) [IsFinite f]
    (y : Spec (.of D.k) ⟶ Y.space.left) (K : sfRationalHeart l E X.space.left) :=
  letI := (R.fibre f y).baseChange K
  (zlFiniteAdicPointH0 D l hl E).map
      (zlFiniteAdicOrdinaryComparison D l hl E R (zlFiniteAdicFibre D f y)
        ((zlFiniteAdicPull D l hl E (pullback.fst f y)).obj K.obj)).inv ≫
    inv ((zlFiniteAdicPointH0 D l hl E).map
      (zlFiniteAdicExchange D l hl E (R.image f)
        (R.image (X := zlFiniteAdicFibre D f y) (Y := zlFiniteAdicPoint D)
          (pullback.snd f y)) (pullback.fst f y) y pullback.condition K.obj)) ≫
    zlFiniteAdicStalkToSum D l hl E f (R.image f) y (R.fibre f y).finite K.obj

variable (L : Type u) [Field L] [Algebra (Padic l) L]
  [FiniteDimensional (Padic l) L] (ι : E →ₐ[Padic l] L)

/-- The existing scalar extension between rational constructible categories.
Source: coefficient-stage convention (blueprint: lem-zl-finite-adic-direct-image). -/
abbrev zlFiniteAdicScalar (X : ZlFiniteAdicSpace D) :=
  sfRationalScalarExtension l E X.space.left 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι

/-- The scalar comparison is the specified adjunction mate of the recorded
pullback/scalar comparison. This fixes the comparison itself, also at equal stages.
Source: Bhatt--Scholze 6.8.14(2), coefficient extension clause
(blueprint: lem-zl-finite-adic-direct-image). -/
def zlFiniteAdicScalarExchange {X Y : ZlFiniteAdicSpace D}
    {f : X.space.left ⟶ Y.space.left}
    (F : ZlFiniteAdicRationalImage D l hl E f)
    (G : ZlFiniteAdicRationalImage D l hl L f)
    (K : sfRationalConstructibleCategory l E X.space.left) :
    (zlFiniteAdicScalar D l E L ι Y).obj (F.functor.obj K) ⟶
      G.functor.obj ((zlFiniteAdicScalar D l E L ι X).obj K) := by
  letI := constructiblePullbackResidueUnits D l hl X.space.left
  letI := constructiblePullbackResidueUnits D l hl Y.space.left
  exact (G.adjunction.homEquiv _ _)
    ((rationalPullbackScalarComparison l E L ι f).inv.app (F.functor.obj K) ≫
      (zlFiniteAdicScalar D l E L ι X).map (F.adjunction.counit.app K))

variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- Extend a small coefficient module to the specified algebraic closure, in its
independent universe. The map is the actual subfield embedding after Shrink transport.
Source: common-stage convention (blueprint: lem-zl-finite-adic-direct-image). -/
abbrev zlFiniteAdicExtend (A : AlgebraicallyClosedCoefficients.Index l Ω) :=
  ModuleCat.extendScalars (A.val.subtype.comp (Shrink.algEquiv (Padic l) A.val).toRingHom)

/-- The common-stage stalk-to-fibre map is literally scalar extension of the finite-stage
counit/restriction map. This definition works on arbitrary representative complexes;
its invertibility on the common-stage heart is asserted below.
Source: common-stage and restriction clauses
(blueprint: lem-zl-finite-adic-direct-image). -/
def zlFiniteAdicQbarFibreMap {X Y : ZlFiniteAdicSpace D}
    (f : X.space.left ⟶ Y.space.left) [IsFinite f]
    (y : Spec (.of D.k) ⟶ Y.space.left)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω X.space.left)
    (R : ZlFiniteAdicRationalSystem D l hl
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω K.stage)) :=
  (zlFiniteAdicExtend l Ω K.stage).map
    (zlFiniteAdicFibreRestriction D l hl
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω K.stage) R f y K.obj)

/-- The common-stage sum restriction applies the same scalar extension to each
counit evaluation and then the canonical finite-sum map. It reindexes actual geometric
lifts and includes the empty sum.
Source: common-stage and finite-sum clauses
(blueprint: lem-zl-finite-adic-direct-image). -/
def zlFiniteAdicQbarStalkToSum {X Y : ZlFiniteAdicSpace D}
    (f : X.space.left ⟶ Y.space.left) [IsFinite f]
    (y : Spec (.of D.k) ⟶ Y.space.left)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω X.space.left)
    (R : ZlFiniteAdicRationalSystem D l hl
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω K.stage)) :=
  @zlFiniteAdicModuleSumMap Ω _ (ZlFiniteAdicLifts D f y) (R.fibre f y).finite
    (fun x ↦ (zlFiniteAdicExtend l Ω K.stage).obj
      ((zlFiniteAdicStalk D l hl
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω K.stage) X x.val).obj K.obj)) _
    (fun x ↦ (zlFiniteAdicExtend l Ω K.stage).map
      ((zlFiniteAdicPointH0 D l hl
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω K.stage)).map
          (zlFiniteAdicEvaluation D l hl
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω K.stage)
            (R.image f) y x K.obj)))

/-- All clauses of finite adic direct image, with the original coefficient categories.
The scalar-system functor is the common-stage direct image on objects and every Hom
representative. Its beta is the canonical scalar mate, so restrictions, germ maps,
cohomology comparisons and diagram transports descend from a common finite field.
The two explicit Qbar maps below use the scalar-extended coefficient stalks themselves;
no equality of the scheme and algebraic-closure universes is imposed.
Source: Stacks 03QP, 0959, 09A8; Bhatt--Scholze 6.8.14, 6.8.15
(blueprint: lem-zl-finite-adic-direct-image). -/
structure ZlFiniteAdicDirectImageData where
  rational : ∀ (A : Type u) [Field A] [Algebra (Padic l) A] [FiniteDimensional (Padic l) A],
    ZlFiniteAdicRationalSystem D l hl A
  stages : ∀ {X Y : ZlFiniteAdicSpace D} (f : X.space.left ⟶ Y.space.left) [IsFinite f],
    StageSystem.Morphism
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X.space.left)
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y.space.left)
  stageFunctor : ∀ {X Y : ZlFiniteAdicSpace D}
    (f : X.space.left ⟶ Y.space.left) [IsFinite f]
    (A : AlgebraicallyClosedCoefficients.Index l Ω),
    (stages f).Φ A =
      ((rational (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A)).image f).functor
  stageMate : ∀ {X Y : ZlFiniteAdicSpace D}
    (f : X.space.left ⟶ Y.space.left) [IsFinite f]
    (A B : AlgebraicallyClosedCoefficients.Index l Ω) (h : A ≤ B)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω X.space.left A),
    HEq
      ((operationStageTransitionIso l Ω Y.space.left A B h).inv.app
          (((stages f).Φ A).obj K) ≫
        ((stages f).β h).hom.app K ≫
          ((stages f).Φ B).map
            ((operationStageTransitionIso l Ω X.space.left A B h).hom.app K))
      (zlFiniteAdicScalarExchange D l hl
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A)
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω B)
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω A B h)
        ((rational (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A)).image f)
        ((rational (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω B)).image f) K)
  commonExactness : ∀ {X Y : ZlFiniteAdicSpace D}
    (f : X.space.left ⟶ Y.space.left) [IsFinite f],
    ConstructiblePullbackComparison
      (sfCommonStageStandardTStructure l X.space.left Ω D hl)
      (sfCommonStageStandardTStructure l Y.space.left Ω D hl)
      (sfCommonStageHeartProperty l X.space.left Ω)
      (sfCommonStageHeartProperty l Y.space.left Ω) (stages f).functor
  commonBaseChange : ∀ {X Y : ZlFiniteAdicSpace D}
    (f : X.space.left ⟶ Y.space.left) [IsFinite f]
    (y : Spec (.of D.k) ⟶ Y.space.left) (K : sfCommonStageHeart l X.space.left Ω),
    IsIso (zlFiniteAdicQbarFibreMap D l hl Ω f y K.obj
      (rational (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω K.obj.stage)))
  commonStalkToSum : ∀ {X Y : ZlFiniteAdicSpace D}
    (f : X.space.left ⟶ Y.space.left) [IsFinite f]
    (y : Spec (.of D.k) ⟶ Y.space.left) (K : sfCommonStageHeart l X.space.left Ω),
    IsIso (zlFiniteAdicQbarStalkToSum D l hl Ω f y K.obj
      (rational (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω K.obj.stage)))

/-- Finite direct image is t-exact, its heart restriction is exact, and its canonical
stalk restrictions identify the image stalk with finite-fibre H⁰ and the finite direct
sum of source stalks. These identifications are natural in sheaf maps and in diagram
isomorphisms, including every base-field semilinear isomorphism, and extend at a common
finite coefficient stage to the specified algebraic closure.
Source: Stacks 03QP and 0959 (finite-level input), 09A8 (pro-etale exactness);
Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15
(blueprint: lem-zl-finite-adic-direct-image).

Proof, in the order of the DAG:
1. Finite-type geometric schemes are Noetherian and finite-dimensional. Finite maps
are finitely presented. Integral constructibility and canonical finite reductions follow
from lem-sf-integral-direct-image-constructible; the reductions have etale origin by
lem-sf-proetale-constructible-origin.
2. Stacks 09A8, lem-zl-finite-fp-proetale-pushforward-exact, makes module direct image
exact on all completed and finite-coefficient modules. It preserves sectionwise products
and the actual coefficient quotient maps. Apply the projection-normalized comparison of
lem-cbc-exact-product-functor-strict-limit.
3. Use the constant/completed equivalence and completion unit to identify the actual
completed derived direct image with the recorded reduction-tower direct image. This
identification respects the Roos projections. Exactness gives the integral Hʲ formula and
preserves both standard halves; it does not require surjectivity of cohomology towers.
4. Form finite-level exchange from pullback of the counit. Stacks 0959 and the canonical
etale/pro-etale comparison mate make it invertible on etale-origin reductions. Stacks
03QP gives the finite-stalk sum and finite etale exactness, including nonreduced fibres.
5. On flat-term K-flat representatives, counit restriction commutes with every coefficient
quotient. The scalar-extension transpose of direct image of its unit is exactly
zlFiniteAdicImageReduction, by the recorded resolution-normalized restriction square.
The ordinary tensor-unit adjunction then gives integralCounit_reduction, with the actual
finite counit zlFiniteAdicFiniteCounit. This gives strict tower maps, rather than
unrelated levelwise isomorphisms.
6. Reconstruct both sides of exchange by their canonical reductions. The evaluation
calculus lem-coef-derived-system-evaluation-calculus identifies system counits with those
projections. Derived limit therefore gives exactly the displayed exchange map.
7. Pass the second tower map through derived limit. Only a finite sum is interchanged:
in the strict Roos model reindex the two products, preserving 1-shift and its cone. The
empty fibre gives zero. Both comparisons are constructed before point sections.
8. Identify the stratified-perfect integral category with the bounded complete category
and their identical raw rationalizations. Localize the actual linear functor and maps.
The counit is localized through rationalComparison and the prescribed integral-pullback
object comparison; this gives counit_localization, so a separately twisted rational
adjunction cannot be used for the restriction maps. The localized standard t-structure
gives t-exactness and exact hearts. The normalized
truncation comparison gives natural Hʲ isomorphisms, with the stated formula.
9. Apply exact point sections and H⁰. Pullback is t-exact on constructible complexes, so
the resulting objects are exactly the stalks and ordinary finite-fibre cohomology in the
statement. The finite-sum map is uniquely fixed by its counit components.
10. Finite scalar extension commutes with these operations. Its comparison is the mate
of the recorded pullback/scalar comparison; this proves stageMate, including equal
stages. Every restriction component sends a tensor to the tensor of its restriction.
The coherent stage-system functor therefore descends the functors and all maps to the
common-stage category, independently of the representative and every enlargement.
11. Diagram isomorphisms take each restriction to the restriction at the transported
point. The recorded pullback composition comparisons identify the two routes exactly
as diagramNatural. No map is required to be over k, so all semilinear isomorphisms are
included. Applying point sections, localization and scalar extension preserves the
identity. Naturality in sheaf maps is the same counit naturality identity. -/
theorem zlFiniteAdicDirectImage : Nonempty (ZlFiniteAdicDirectImageData D l hl Ω) := by
  sorry

end WeilConjectures
