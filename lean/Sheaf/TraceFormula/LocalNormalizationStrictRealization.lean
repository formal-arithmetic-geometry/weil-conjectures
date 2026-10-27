/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.AlgebraicGeometry.FrobeniusDetailed
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.FiniteCoefficientPoint
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.SixFunctors.SchemeFrobenius
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Sheaf.Paper.IntegralPullbackComparisonRealization
public import Sheaf.Paper.IntegralFinitePullbackComposition
public import Sheaf.SixFunctors.SelectedSchemeGaloisComparison
public import Sheaf.SixFunctors.FrobeniusPointTransport
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.IntegralSectionsPerfectReduction
public import Sheaf.Paper.FrobeniusCoefficientReductionCoherence
public import Sheaf.CategoryTheory.SemilinearScalarLocalization
import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
import Sheaf.Paper.PointSystemInsertionComposition
import Sheaf.AlgebraicGeometry.FrobeniusTrivializationPullback
import Sheaf.SixFunctors.SchemeGaloisCoefficientChange
import Sheaf.Paper.PointSectionsFiniteReduction
public import Sheaf.Paper.PointSectionsFiniteReductionData
import Sheaf.Paper.IntegralOperationsPreserveConstructible
import Sheaf.Paper.EffectiveComparisonRealizationModels
import Sheaf.TraceFormula.CounitRealizationSubstitution
import Sheaf.Paper.IntegralPullbackReductionCounit
import Sheaf.TraceFormula.IntegralComparisonCounitCharacterization
import Sheaf.SixFunctors.FrobeniusPointTransportNatural
public import Sheaf.TraceFormula.PointTransportComposition
public import Sheaf.Paper.PointPullbackRepresentativeDiagram
public import Sheaf.Paper.IntegralPointTransportTowerPowers
public import Sheaf.SixFunctors.SchemeGaloisComparisonNormalForm

/-! # Strict realization of local Frobenius normalization

Source: main-20261015, sec-trace-formula/sk-thm-trace-transport,
prop-trf-karoubi-independence.proof.md, final transport sentence, local normalization
steps 5--7 (blueprint: lem-trf-local-normalization-strict-realization).

Levels n denote the positive exponents n+1. All towers retain their actual quotient
transitions. The two recipes are defined as chain maps before passage to derived categories.
-/

@[expose] public noncomputable section
set_option autoImplicit false


set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.pointReductionModuleDerived
attribute [local irreducible] CategoryTheory.Limits.limit
  WeilConjectures.completedIntegralCoefficientSheafUnrestricted
  HasDerivedCategory.standard WeilConjectures.unrestrictedIntegralReductionExistence
  WeilConjectures.frobeniusPointIso
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures.LocalNormalization

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Finiteness of every positive quotient, reusing the coefficient node's theorem.
Source: local normalization coefficient convention
(blueprint: lem-trf-local-normalization-strict-realization). -/
instance finiteQuotient (n : ℕ) : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
  Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))

/-- Ordinary finite tensor pullback, with the dependency's unit-normalized presentation.
Source: local normalization step 1
(blueprint: lem-trf-local-normalization-strict-realization). -/
def finitePull {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  (proEtaleConstantRingPullback (Padic.coefficientExtensionRing l E (n + 1)) f)
    |>.mapHomologicalComplex (.up ℤ)

/-- Exact finite sections on complexes.
Source: local normalization steps 2--3
(blueprint: lem-trf-local-normalization-strict-realization). -/
def finiteSections (n : ℕ) :=
  (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)))
    |>.mapHomologicalComplex (.up ℤ)

/-- The actual ordinary compositor on complexes, from nested to direct pullback.
Source: local normalization step 1, Stacks 0D6D
(blueprint: lem-trf-local-normalization-strict-realization). -/
def finiteComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    finitePull l E g n ⋙ finitePull l E f n ≅ finitePull l E (f ≫ g) n :=
  (Functor.mapHomologicalComplexCompIso
    (Iso.refl (proEtaleConstantRingPullback (Padic.coefficientExtensionRing l E (n + 1)) g ⋙
      proEtaleConstantRingPullback (Padic.coefficientExtensionRing l E (n + 1)) f))
    (.up ℤ)) ≪≫
  NatIso.mapHomologicalComplex
    (proEtaleConstantRingModulePullbackComposition f g
      (Padic.coefficientExtensionRing l E (n + 1))).choose.symm (.up ℤ)

/-- The finite point insertion is restriction, followed by the actual tensor-unit map.
Source: local normalization step 2
(blueprint: lem-trf-local-normalization-strict-realization). -/
def finiteInsertion (r n : ℕ)
    (N : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ) :
    (finiteSections D l E n).obj N ⟶
      (finiteSections D l E n).obj
        ((finitePull l E ((pointFrobeniusAut D) ^ r).hom n).obj N) :=
  pointPowerFiniteSigma D l E r n N ≫
    (finiteSections D l E n).map
      (inverseImageFiniteComparisonComplex l E ((pointFrobeniusAut D) ^ r).hom n N) ≫
    (finiteSections D l E n).map
      ((NatIso.mapHomologicalComplex
        (integralFinitePullbackModel l E ((pointFrobeniusAut D) ^ r).hom n)
        (.up ℤ)).hom.app N)

attribute [local irreducible] proEtaleModuleInverseImage
  integralFinitePullbackModel
  integralOperationsLevelPullback
  proEtaleConstantRingComparison


attribute [local irreducible] finitePull finiteSections

/-- Successive one-step finite insertions, with the identity and specified compositors.
The zero case is the identity map in the canonical identity-pullback coordinates.
Source: local normalization step 2, the recurrence defining I
(blueprint: lem-trf-local-normalization-strict-realization). -/
def finiteSuccessiveInsertion (n : ℕ)
    (N : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ) :
    (r : ℕ) → (finiteSections D l E n).obj N ⟶
      (finiteSections D l E n).obj
        ((finitePull l E ((pointFrobeniusAut D) ^ r).hom n).obj N)
  := Nat.rec (finiteInsertion D l E 0 n N) (fun r previous ↦
      previous ≫
      finiteInsertion D l E 1 n
        ((finitePull l E ((pointFrobeniusAut D) ^ r).hom n).obj N) ≫
      (finiteSections D l E n).map
        ((finiteComp l E ((pointFrobeniusAut D) ^ 1).hom
          ((pointFrobeniusAut D) ^ r).hom n).hom.app N) ≫
      (finiteSections D l E n).map
        (eqToHom (congrArg (fun f ↦ (finitePull l E f n).obj N)
          (congrArg Iso.hom (pow_succ (pointFrobeniusAut D) r)).symm)))

attribute [local semireducible] finitePull finiteSections

/-- The simultaneous quotient of the single chosen representative.
Source: local normalization step 1
(blueprint: lem-trf-local-normalization-strict-realization). -/
abbrev quotient {X : Scheme.{u}}
    (Q : CochainComplex (integralTowerModules l E X) ℤ) (n : ℕ) :=
  (unrestrictedIntegralFiniteComplex l E X n).obj Q

/-- The actual integral-to-quotient homomorphism, in the point-fibre size convention.
Source: local normalization steps 1--2
(blueprint: lem-trf-local-normalization-strict-realization). -/
abbrev quotientScalars (n : ℕ) := pointReductionQuotient l E n

/-- Coefficient restriction of the finite section complex, with the quotient scalar map.
Source: local normalization step 2
(blueprint: lem-trf-local-normalization-strict-realization). -/
abbrev restrictSections (n : ℕ) :=
  (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (quotientScalars l E n))
    |>.mapHomologicalComplex (.up ℤ)

/-- The entire section tower with the actual transitions from Q, without localization.
Source: local normalization steps 1, 5
(blueprint: lem-trf-local-normalization-strict-realization). -/
abbrev tower {Y : Scheme.{u}} (z : Spec (.of D.k) ⟶ Y)
    (Q : CochainComplex (integralTowerModules l E Y) ℤ) :=
  (PointPullbackRepresentative.sectionTower l E D.k z).obj Q

/-- Restricting coefficients before or after sections gives the identity on every section.
Source: local normalization steps 1--2, constant-to-completion normalization
(blueprint: lem-trf-local-normalization-strict-realization).
Proof: both scalar actions send a constant integral scalar to its actual quotient.
Their additive groups and differentials are the same final-object evaluations.
The identity is therefore a linear chain isomorphism. Equality on every element
of every degree determines it uniquely. -/
theorem levelIdentity_existsUnique {Y : Scheme.{u}} (z : Spec (.of D.k) ⟶ Y)
    (Q : CochainComplex (integralTowerModules l E Y) ℤ) (n : ℕ) :
    ∃! e : (tower D l E z Q).obj (op n) ≅
        (restrictSections l E n).obj ((finiteSections D l E n).obj
          (((integralOperationsLevelPullback l E z n).mapHomologicalComplex (.up ℤ)).obj
            (quotient l E Q n))),
      ∀ (i : ℤ) (x : ((tower D l E z Q).obj (op n)).X i), HEq (e.hom.f i x) x := by
  sorry

/-- The normalized identity followed by the dependency's actual pullback-presentation map.
Source: local normalization steps 1--2
(blueprint: lem-trf-local-normalization-strict-realization). -/
def levelModel {Y : Scheme.{u}} (z : Spec (.of D.k) ⟶ Y)
    (Q : CochainComplex (integralTowerModules l E Y) ℤ) (n : ℕ) :
    (tower D l E z Q).obj (op n) ≅
      (restrictSections l E n).obj
        ((finiteSections D l E n).obj ((finitePull l E z n).obj (quotient l E Q n))) :=
  (levelIdentity_existsUnique D l E z Q n).exists.choose ≪≫
    (restrictSections l E n).mapIso ((finiteSections D l E n).mapIso
      ((NatIso.mapHomologicalComplex (integralFinitePullbackModel l E z n) (.up ℤ)).app
        (quotient l E Q n)))

variable (X₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

/-- The actual termwise kappa recipe, using the specified absolute-Frobenius
trivialization and the canonical compositor, before derived localization.
Source: local normalization step 3
(blueprint: lem-trf-local-normalization-strict-realization). -/
def finiteKappa (hl : l ≠ D.p) (m : ℕ) (hm : 1 ≤ m) (n : ℕ) :
    finitePull l E (D.schemeFrobeniusIterate X₀ m) n ≅
      finitePull l E
        (HPow.hPow (α := End (D.geometricFiber X₀).left)
          (D.geometricGaloisFrobenius X₀) m) n :=
  letI : Fact (l ≠ D.p) := ⟨hl⟩
  eqToIso (congrArg (fun f ↦ finitePull l E f n)
    (D.schemeGaloisComparison_normal_form X₀
      (Padic.coefficientExtensionRing l E (n + 1))
      (FiniteFieldDatum.frobeniusCoherenceAnnihilator l E D n) m hm).choose_spec.choose) ≪≫
  (finiteComp l E _ _ n).symm ≪≫
  Functor.isoWhiskerLeft _
    (NatIso.mapHomologicalComplex
      ((absoluteFrobenius_proEtale_trivialization D.p D.prime
        (Padic.coefficientExtensionRing l E (n + 1))).choose_spec.2.choose_spec.2.choose
          (D.geometricFiber X₀).left (D.schemeGaloisComparison_normal_form X₀
      (Padic.coefficientExtensionRing l E (n + 1))
      (FiniteFieldDatum.frobeniusCoherenceAnnihilator l E D n) m hm).choose (D.a * m))
      (.up ℤ)) ≪≫
  Functor.rightUnitor _

attribute [local irreducible] finitePull finiteSections

/-- The finite return recipe in direct pullback coordinates. The power insertion
is identified with the successive insertions by the point-system composition law.
Source: local normalization step 2
(blueprint: lem-trf-local-normalization-strict-realization). -/
def finiteA (m n : ℕ) (z : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left)
    (hz : ((pointFrobeniusAut D) ^ m).hom ≫ z = z ≫
      HPow.hPow (α := End (D.geometricFiber X₀).left)
        (D.geometricGaloisFrobenius X₀) m)
    (Q : CochainComplex (integralTowerModules l E (D.geometricFiber X₀).left) ℤ) :
    (finiteSections D l E n).obj ((finitePull l E z n).obj (quotient l E Q n)) ⟶
      (finiteSections D l E n).obj ((finitePull l E
        (z ≫ HPow.hPow (α := End (D.geometricFiber X₀).left)
          (D.geometricGaloisFrobenius X₀) m) n).obj (quotient l E Q n)) :=
  finiteSuccessiveInsertion D l E n ((finitePull l E z n).obj (quotient l E Q n)) m ≫
    (finiteSections D l E n).map
      ((finiteComp l E ((pointFrobeniusAut D) ^ m).hom z n).hom.app
        (quotient l E Q n)) ≫
    (finiteSections D l E n).map
      (eqToHom (congrArg (fun f ↦ (finitePull l E f n).obj (quotient l E Q n)) hz))

set_option maxHeartbeats 800000 in
-- The nested natural-isomorphism composite requires additional elaboration heartbeats.
/-- The finite fixed-point/absolute-Frobenius recipe, in the same direct coordinates.
Source: local normalization step 3
(blueprint: lem-trf-local-normalization-strict-realization). -/
def finiteB (hl : l ≠ D.p) (m : ℕ) (hm : 1 ≤ m) (n : ℕ)
    (z : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left)
    (hz : z ≫ D.schemeFrobeniusIterate X₀ m = z)
    (Q : CochainComplex (integralTowerModules l E (D.geometricFiber X₀).left) ℤ) :
    (finiteSections D l E n).obj ((finitePull l E z n).obj (quotient l E Q n)) ⟶
      (finiteSections D l E n).obj ((finitePull l E
        (z ≫ HPow.hPow (α := End (D.geometricFiber X₀).left)
          (D.geometricGaloisFrobenius X₀) m) n).obj (quotient l E Q n)) :=
  (finiteSections D l E n).map
    (eqToHom (congrArg (fun f ↦ (finitePull l E f n).obj (quotient l E Q n)) hz.symm)) ≫
    (finiteSections D l E n).map
      ((finiteComp l E z (D.schemeFrobeniusIterate X₀ m) n).inv.app (quotient l E Q n)) ≫
    (finiteSections D l E n).map
      ((finitePull l E z n).map ((finiteKappa D l E X₀ hl m hm n).hom.app
        (quotient l E Q n))) ≫
    (finiteSections D l E n).map
      ((finiteComp l E z
        (HPow.hPow (α := End (D.geometricFiber X₀).left)
          (D.geometricGaloisFrobenius X₀) m) n).hom.app (quotient l E Q n))

attribute [local irreducible] FiniteFieldDatum.geometricFiber
  FiniteFieldDatum.schemeFrobeniusIterate
  FiniteFieldDatum.geometricGaloisFrobenius

/-- Point data with both return equalities, parametrized by the actual scheme maps.
This separates the generic bundle from expansion of the scheme category construction.
Source: local normalization hypotheses
(blueprint: lem-trf-local-normalization-strict-realization). -/
structure ReturnPoint {C : Type v} [Category.{w} C] {s X B : C}
    (base : X ⟶ B) (basePoint : s ⟶ B)
    (h : Aut s) (g phi : End X) (m : ℕ) where
  /-- The geometric point itself. -/
  z : s ⟶ X
  /-- It is a point over the specified base. -/
  overBase : z ≫ base = basePoint
  /-- Scheme-Frobenius fixedness. -/
  fixed : z ≫ phi = z
  /-- The semilinear Galois return square. -/
  returnSquare : (h ^ m).hom ≫ z = z ≫ g ^ m

/-- A k-point with the two return equalities of local normalization.
Source: local normalization hypotheses
(blueprint: lem-trf-local-normalization-strict-realization). -/
abbrev Point (m : ℕ) :=
  ReturnPoint (D.geometricFiber X₀).hom (𝟙 (Spec (.of D.k))) (pointFrobeniusAut D)
    (D.geometricGaloisFrobenius X₀) (D.schemeFrobeniusIterate X₀ m) m

/-- The common direct-coordinate target point map.
Source: local normalization, return-square coordinates
(blueprint: lem-trf-local-normalization-strict-realization). -/
abbrev target {m : ℕ} (Z : Point D X₀ m) :=
  Z.z ≫ HPow.hPow (α := End (D.geometricFiber X₀).left)
    (D.geometricGaloisFrobenius X₀) m

/-- Both strict arrows have precisely the original quotient section towers as endpoints.
Source: local normalization steps 2--3
(blueprint: lem-trf-local-normalization-strict-realization). -/
abbrev StrictMaps {m : ℕ} (Z : Point D X₀ m)
    (Q : CochainComplex (integralTowerModules l E (D.geometricFiber X₀).left) ℤ) :=
  (tower D l E Z.z Q ⟶ tower D l E (target D X₀ Z) Q) ×
    (tower D l E Z.z Q ⟶ tower D l E (target D X₀ Z) Q)

/-- The prescribed component family, retaining its chain maps rather than their classes.
Source: local normalization steps 2--3
(blueprint: lem-trf-local-normalization-strict-realization). -/
def Components (hl : l ≠ D.p) {m : ℕ} (hm : 1 ≤ m) (Z : Point D X₀ m)
    (Q : CochainComplex (integralTowerModules l E (D.geometricFiber X₀).left) ℤ)
    (M : StrictMaps D l E X₀ Z Q) : Prop :=
  ∀ n : ℕ,
    M.1.app (op n) = (levelModel D l E Z.z Q n).hom ≫
      (restrictSections l E n).map (finiteA D l E X₀ m n Z.z Z.returnSquare Q) ≫
      (levelModel D l E (target D X₀ Z) Q n).inv ∧
    M.2.app (op n) = (levelModel D l E Z.z Q n).hom ≫
      (restrictSections l E n).map (finiteB D l E X₀ hl m hm n Z.z Z.fixed Q) ≫
      (levelModel D l E (target D X₀ Z) Q n).inv

/-- There is exactly one strict pair with the specified recipes at every level.
Source: local normalization steps 1--3
(blueprint: lem-trf-local-normalization-strict-realization).
Proof: restriction, tensor-unit insertion and the module compositors commute with
all actual quotient maps. The absolute-Frobenius trivialization is restriction
along relative Frobenius, hence does too; its scalar formula sends x tensor a
to the restricted section tensored with the quotient of a. Sheafification and
its comma coprojections are natural for these maps. Thus both transition squares
commute as chain maps. Use these component maps to form natural transformations.
Natural transformations are determined by all their components, giving uniqueness. -/
theorem strictRecipes_existsUnique (hl : l ≠ D.p) {m : ℕ} (hm : 1 ≤ m)
    (Z : Point D X₀ m)
    (Q : CochainComplex (integralTowerModules l E (D.geometricFiber X₀).left) ℤ) :
    ∃! M : StrictMaps D l E X₀ Z Q, Components D l E X₀ hl hm Z Q M := by
  sorry

/-- The canonical strict recipes, determined uniquely by their actual chain components.
Source: local normalization steps 2--3
(blueprint: lem-trf-local-normalization-strict-realization). -/
def strictRecipes (hl : l ≠ D.p) {m : ℕ} (hm : 1 ≤ m) (Z : Point D X₀ m)
    (Q : CochainComplex (integralTowerModules l E (D.geometricFiber X₀).left) ℤ) :
    StrictMaps D l E X₀ Z Q :=
  (strictRecipes_existsUnique D l E X₀ hl hm Z Q).exists.choose

/-- Realize a strict arrow by the functorial Roos construction and the specified
whole-system point/representative comparison on both endpoints.
Source: local normalization steps 5--7
(blueprint: lem-trf-local-normalization-strict-realization). -/
def realize {m : ℕ} (Z : Point D X₀ m)
    (K : sfIntegralConstructibleCategory l E (D.geometricFiber X₀).left)
    (Q : (integralOperationsGoodComplex l E (D.geometricFiber X₀).left).FullSubcategory)
    (q : DerivedCategory.Q.obj Q.obj ≅ K.obj)
    (f : tower D l E Z.z Q.obj ⟶ tower D l E (target D X₀ Z) Q.obj) :
    (PointPullbackRepresentative.completedSections l E D.k Z.z).obj K.obj ⟶
      (PointPullbackRepresentative.completedSections l E D.k (target D X₀ Z)).obj K.obj :=
  (PointPullbackRepresentative.representative l E D.k Z.z K.obj Q q).hom ≫
    (PointPullbackRepresentative.moduleQ l E).map (integralOperationsRoosMap f) ≫
    (PointPullbackRepresentative.representative l E D.k (target D X₀ Z) K.obj Q q).inv


/-- The two recorded exact section functors differ only in their scalar presentations.
Source: local normalization step 5
(blueprint: lem-trf-local-normalization-strict-realization).
Proof: the constant-to-completion map in both definitions is the limit of the same
constant quotient maps. The identity on final-object sections is consequently linear.
It commutes with all module maps and is its own inverse. Every section determines
its value, proving uniqueness. -/
theorem sectionModel_existsUnique :
    ∃! e : pointIntegralSections l E D.k ≅ PointPullbackRepresentative.sections l E D.k,
      ∀ (M : integralTowerModules l E (Spec (.of D.k)))
        (x : (pointIntegralSections l E D.k).obj M), e.hom.app M x = x := by
  sorry

/-- The identity on sections with the canonical scalar actions, fixed uniquely above.
Source: local normalization step 5
(blueprint: lem-trf-local-normalization-strict-realization). -/
def sectionModel := (sectionModel_existsUnique D l E).exists.choose

/-- The canonical change from the small module localization to the standard one,
followed by the identity on final-object sections. No derived map is chosen.
Source: local normalization step 5, Stacks 05RU
(blueprint: lem-trf-local-normalization-strict-realization). -/
def sectionDerivedModel :
    pointFibreIntegralAmbient D l E ⋙
        sfSectionsCoefficientLift (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) ≅
      PointPullbackRepresentative.derivedSections l E D.k :=
  sfSectionsCoefficientLiftIso _ (pointIntegralSections l E D.k) ≪≫
    @Functor.mapDerivedCategoryNatIso _ _ _ _ _ _ _
      (PointPullbackRepresentative.moduleHasDerived l E) _ _ _ _ _ _ _ _
      (sectionModel D l E)

/-- The successive integral pullback objects U^j N, with their actual constructibility.
Source: local normalization recurrence, step 6
(blueprint: lem-trf-local-normalization-strict-realization). -/
def iteratedPointPullback (hl : l ≠ D.p) : ℕ →
    sfIntegralConstructibleCategory l E (Spec (.of D.k)) ⥤
      sfIntegralConstructibleCategory l E (Spec (.of D.k))
  | 0 => 𝟭 _
  | j + 1 => iteratedPointPullback hl j ⋙
      @constructibleIntegralPullback l _ E _ _ _ _ _ (pointFrobeniusAut D).hom
        (frobeniusPointPrimeInvertible D l hl) (frobeniusPointPrimeInvertible D l hl)

/-- The recurrence I^0=1, I^(j+1)=I^j followed by the specified integral iota.
Source: local normalization step 6
(blueprint: lem-trf-local-normalization-strict-realization). -/
def successiveIntegral (hl : l ≠ D.p)
    (N : sfIntegralConstructibleCategory l E (Spec (.of D.k))) :
    (j : ℕ) → (pointFibreIntegralAmbient D l E).obj N.obj ⟶
      (pointFibreIntegralAmbient D l E).obj
        (((iteratedPointPullback D l E hl j).obj N).obj)
  | 0 => 𝟙 _
  | j + 1 => successiveIntegral hl N j ≫
      frobeniusPointTransportIntegral D l hl E
        (((iteratedPointPullback D l E hl j).obj N).obj)

/-- Direct power pullback on the same intrinsic integral category.
Source: local normalization step 6
(blueprint: lem-trf-local-normalization-strict-realization). -/
def pointPowerPullback (hl : l ≠ D.p) (r : ℕ) :=
  @constructibleIntegralPullback l _ E _ _ _ _ _ ((pointFrobeniusAut D) ^ r).hom
    (frobeniusPointPrimeInvertible D l hl) (frobeniusPointPrimeInvertible D l hl)

/-- The canonical iterated-to-direct comparison, formed only from the specified c^E.
Source: local normalization steps 5--6
(blueprint: lem-trf-local-normalization-strict-realization). -/
def pointPowerModel (hl : l ≠ D.p) (B : IntegralComparisonSystem.{u} l)
    (N : sfIntegralConstructibleCategory l E (Spec (.of D.k))) :
    (j : ℕ) → ((iteratedPointPullback D l E hl j).obj N).obj ≅
      ((pointPowerPullback D l E hl j).obj N).obj
  | 0 =>
      (@integralComparisonUnit l _ E _ _ _ B (Spec (.of D.k))
        (frobeniusPointPrimeInvertible D l hl) N).symm ≪≫
      eqToIso (congrArg (fun f ↦ (integralDerivedPullback l E f).obj N.obj)
        (congrArg Iso.hom (pow_zero (pointFrobeniusAut D))).symm)
  | j + 1 =>
      (integralDerivedPullback l E (pointFrobeniusAut D).hom).mapIso
        (pointPowerModel hl B N j) ≪≫
      (IntegralPointTransportTower.integralCompositor D l E hl B j N.obj N.property).symm

/-- The canonical integral return square in direct power coordinates.
Source: local normalization steps 5 and 7
(blueprint: lem-trf-local-normalization-strict-realization). -/
def integralReturn (hl : l ≠ D.p) (B : IntegralComparisonSystem.{u} l)
    {m : ℕ} (Z : Point D X₀ m)
    (K : sfIntegralConstructibleCategory l E (D.geometricFiber X₀).left) :
    (integralDerivedPullback l E ((pointFrobeniusAut D) ^ m).hom).obj
        ((integralDerivedPullback l E Z.z).obj K.obj) ≅
      (integralDerivedPullback l E (target D X₀ Z)).obj K.obj :=
  (@integralComparisonComposition l _ E _ _ _ B _ _ _
    (D.schemeFrobeniusCoefficientInvertible X₀ l hl)
    (frobeniusPointPrimeInvertible D l hl) (frobeniusPointPrimeInvertible D l hl)
    ((pointFrobeniusAut D) ^ m).hom Z.z K).symm ≪≫
  eqToIso (congrArg (fun f ↦ (integralDerivedPullback l E f).obj K.obj) Z.returnSquare)

/-- The actual integral A map: successive specified point transports, then the
specified return-square compositor. It is defined independently of strict realization.
Source: local normalization steps 6--7
(blueprint: lem-trf-local-normalization-strict-realization). -/
def integralA (hl : l ≠ D.p) (B : IntegralComparisonSystem.{u} l)
    {m : ℕ} (Z : Point D X₀ m)
    (K : sfIntegralConstructibleCategory l E (D.geometricFiber X₀).left) :=
  successiveIntegral D l E hl
      ((@constructibleIntegralPullback l _ E _ _ _ _ _ Z.z
        (frobeniusPointPrimeInvertible D l hl)
        (D.schemeFrobeniusCoefficientInvertible X₀ l hl)).obj K) m ≫
    (pointFibreIntegralAmbient D l E).map
      ((pointPowerModel D l E hl B
        ((@constructibleIntegralPullback l _ E _ _ _ _ _ Z.z
          (frobeniusPointPrimeInvertible D l hl)
          (D.schemeFrobeniusCoefficientInvertible X₀ l hl)).obj K) m).hom) ≫
    (pointFibreIntegralAmbient D l E).map (integralReturn D l E X₀ hl B Z K).hom

/-- Put the independently defined integral map in the representative's section coordinates.
Source: local normalization steps 5--7
(blueprint: lem-trf-local-normalization-strict-realization). -/
def integralAInCoordinates (hl : l ≠ D.p) (B : IntegralComparisonSystem.{u} l)
    {m : ℕ} (Z : Point D X₀ m)
    (K : sfIntegralConstructibleCategory l E (D.geometricFiber X₀).left) :=
  (sectionDerivedModel D l E).inv.app ((integralDerivedPullback l E Z.z).obj K.obj) ≫
    (sfSectionsCoefficientLift _).map (integralA D l E X₀ hl B Z K) ≫
    (sectionDerivedModel D l E).hom.app
      ((integralDerivedPullback l E (target D X₀ Z)).obj K.obj)


/-- The quotient point complex in the tensor-pullback presentation of the finite recipes.
Source: local normalization steps 1--4
(blueprint: lem-trf-local-normalization-strict-realization). -/
abbrev finitePointComplex {Y : Scheme.{u}} (f : Spec (.of D.k) ⟶ Y)
    (Q : CochainComplex (integralTowerModules l E Y) ℤ) (n : ℕ) :=
  (finiteSections D l E n).obj ((finitePull l E f n).obj (quotient l E Q n))

/-- The actual quotient map, on underlying section groups, in finite tensor coordinates.
Source: local normalization steps 1--4
(blueprint: lem-trf-local-normalization-strict-realization). -/
def quotientSection {Y : Scheme.{u}} (f : Spec (.of D.k) ⟶ Y)
    (Q : CochainComplex (integralTowerModules l E Y) ℤ)
    (n j : ℕ) (h : j ≤ n) (i : ℤ) (x : (finitePointComplex D l E f Q n).X i) :
    (finitePointComplex D l E f Q j).X i :=
  (levelModel D l E f Q j).hom.f i
    (((tower D l E f Q).map (homOfLE h).op).f i
      ((levelModel D l E f Q n).inv.f i x))

/-- The uniquely normalized coefficient comparison on simultaneous point quotients.
It is the tensor associator on sections, with the actual quotient transition.
Source: local normalization step 4, Stacks 06YY
(blueprint: lem-trf-local-normalization-strict-realization).
Proof: tensor associativity sends (x tensor a) tensor b to x tensor bar(a)b,
with inverse x tensor b mapping to (x tensor 1) tensor b. Pullback commutes with
this tensor formula, and point sections do by the canonical finite-reduction
comparison. Each quotient of Q is K-flat with flat terms; its point pullback and
sections remain K-flat. Thus these ordinary comparisons compute the canonical
derived coefficient changes, including nonflat quotient maps. The tensor generators
span each degree, so their displayed values determine the chain isomorphism uniquely. -/
theorem coefficientComparison_existsUnique {Y : Scheme.{u}} (f : Spec (.of D.k) ⟶ Y)
    (Q : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (n j : ℕ) (h : j ≤ n) :
    ∃! e : (pointFiniteReductionComplexTensor l E (n + 1) (j + 1)
        (Nat.succ_le_succ h)).obj (finitePointComplex D l E f Q.obj n) ≅
        finitePointComplex D l E f Q.obj j,
      ∀ (i : ℤ) (a b : ULift.{u + 1} (Padic.coefficientExtensionRing l E (j + 1)))
        (x : (finitePointComplex D l E f Q.obj n).X i),
        e.hom.f i (pointFiniteReductionTensorGenerator l E (n + 1) (j + 1)
          (Nat.succ_le_succ h) (finitePointComplex D l E f Q.obj n) i a b x) =
          (a * b) • quotientSection D l E f Q.obj n j h i x := by
  sorry

/-- The canonical associator comparison, uniquely fixed on all tensor generators.
Source: local normalization step 4
(blueprint: lem-trf-local-normalization-strict-realization). -/
def coefficientComparison {Y : Scheme.{u}} (f : Spec (.of D.k) ⟶ Y)
    (Q : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (n j : ℕ) (h : j ≤ n) :
    (pointFiniteReductionComplexTensor l E (n + 1) (j + 1)
      (Nat.succ_le_succ h)).obj (finitePointComplex D l E f Q.obj n) ≅
        finitePointComplex D l E f Q.obj j :=
  (coefficientComparison_existsUnique D l E f Q n j h).exists.choose

attribute [local irreducible] coefficientComparison

/-- Compatibility with every canonical derived quotient: the ordinary associator
square and invertibility of the actual derived tensor counit are both retained.
Source: local normalization step 4
(blueprint: lem-trf-local-normalization-strict-realization). -/
def CoefficientCompatibility (hl : l ≠ D.p) {m : ℕ} (hm : 1 ≤ m)
    (Z : Point D X₀ m)
    (Q : (integralOperationsGoodComplex l E (D.geometricFiber X₀).left).FullSubcategory) :
    Prop :=
  ∀ (n j : ℕ) (h : j ≤ n),
    IsIso ((pointFiniteReductionModuleCounit l E (n + 1) (j + 1)
      (Nat.succ_le_succ h)).app (finitePointComplex D l E Z.z Q.obj n)) ∧
    IsIso ((pointFiniteReductionModuleCounit l E (n + 1) (j + 1)
      (Nat.succ_le_succ h)).app (finitePointComplex D l E (target D X₀ Z) Q.obj n)) ∧
    (pointFiniteReductionComplexTensor l E (n + 1) (j + 1)
      (Nat.succ_le_succ h)).map (finiteA D l E X₀ m n Z.z Z.returnSquare Q.obj) ≫
        (coefficientComparison D l E (target D X₀ Z) Q n j h).hom =
      (coefficientComparison D l E Z.z Q n j h).hom ≫
        finiteA D l E X₀ m j Z.z Z.returnSquare Q.obj ∧
    (pointFiniteReductionComplexTensor l E (n + 1) (j + 1)
      (Nat.succ_le_succ h)).map (finiteB D l E X₀ hl m hm n Z.z Z.fixed Q.obj) ≫
        (coefficientComparison D l E (target D X₀ Z) Q n j h).hom =
      (coefficientComparison D l E Z.z Q n j h).hom ≫
        finiteB D l E X₀ hl m hm j Z.z Z.fixed Q.obj

/-- Exact integral sections after the specified completed point pullback.
Source: local normalization step 9
(blueprint: lem-trf-local-normalization-strict-realization). -/
def integralJ {Y : Scheme.{u}} (f : Spec (.of D.k) ⟶ Y) :
    sfIntegralConstructibleCategory l E Y ⥤
      @DerivedCategory (ModuleCat.{u + 1}
        (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))) _ _
          (HasDerivedCategory.ofIsGrothendieckAbelian _) :=
  (sfIntegralConstructible l E Y).ι ⋙ integralDerivedPullback l E f ⋙
    pointFibreIntegralAmbient D l E

/-- The actual point composite is additive, including its normalized completed descent.
Source: local normalization steps 9--10
(blueprint: lem-trf-local-normalization-strict-realization).
Proof: inverse image, tensoring, products, the Roos differential and exact point sections
preserve addition. The normalized descent comparison carries this identity to the
localization on K-flat representatives, hence to every derived morphism. -/
theorem integralJ_additive {Y : Scheme.{u}} (f : Spec (.of D.k) ⟶ Y) :
    (integralJ D l E f).Additive := by
  sorry

/-- Additivity of the specified point functor, for the scalar-localization interface.
Source: local normalization step 10
(blueprint: lem-trf-local-normalization-strict-realization). -/
instance integralJAdditive {Y : Scheme.{u}} (f : Spec (.of D.k) ⟶ Y) :
    (integralJ D l E f).Additive := integralJ_additive D l E f

/-- Constant-scalar linearity of the actual composite point functor.
Source: local normalization step 10
(blueprint: lem-trf-local-normalization-strict-realization).
Proof: each finite inverse image, actual quotient map, Roos product map, and point
section map commutes with the constant integral scalar action. This persists through
quasi-isomorphisms and their inverses, hence every derived roof. The scalar action
on section modules is the same action with its canonical ULift coefficient map. -/
theorem integralJ_semilinear {Y : Scheme.{u}} (f : Spec (.of D.k) ⟶ Y) :
    ScalarLocalization.IsSemilinear
      ((ULift.ringEquiv : ULift.{u + 1} (Padic.coefficientExtensionIntegers l E) ≃+*
      Padic.coefficientExtensionIntegers l E).symm.toRingHom :
        Padic.coefficientExtensionIntegers l E →+*
        ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) (integralJ D l E f) := by
  sorry

/-- Raw localization of the point's module-valued category; no idempotents are adjoined.
Source: local normalization step 10
(blueprint: lem-trf-local-normalization-strict-realization). -/
abbrev rationalize := ScalarLocalization.localization
  (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))
  (@DerivedCategory (ModuleCat.{u + 1}
    (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))) _ _
      (HasDerivedCategory.ofIsGrothendieckAbelian _))
  (ULift.up (Padic.coefficientExtensionUniformizer l E))

/-- The actual rational point functor on every localized Hom module.
Source: local normalization step 10
(blueprint: lem-trf-local-normalization-strict-realization). -/
def rationalJ {Y : Scheme.{u}} (f : Spec (.of D.k) ⟶ Y) :=
  ScalarLocalization.extension
    (Padic.coefficientExtensionUniformizer l E)
    (ULift.up (Padic.coefficientExtensionUniformizer l E))
    ((ULift.ringEquiv : ULift.{u + 1} (Padic.coefficientExtensionIntegers l E) ≃+*
      Padic.coefficientExtensionIntegers l E).symm.toRingHom :
        Padic.coefficientExtensionIntegers l E →+*
      ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))
    (IsLocalization.Away.algebraMap_isUnit
      (ULift.up (Padic.coefficientExtensionUniformizer l E))) (integralJ D l E f)
    (integralJ_semilinear D l E f)

/-- The coefficient-field value of a fraction in the lifted integral coefficient ring.
Source: local normalization step 10, canonical coefficient identification
(blueprint: lem-trf-local-normalization-strict-realization). -/
def rationalScalar :=
  (sfRationalCoefficientEquiv l E).toRingHom.comp
    (ScalarLocalization.coefficientMap
      (ULift.up (Padic.coefficientExtensionUniformizer l E))
      (Padic.coefficientExtensionUniformizer l E)
      (ULift.ringEquiv : ULift.{u + 1} (Padic.coefficientExtensionIntegers l E) ≃+*
        Padic.coefficientExtensionIntegers l E).toRingHom
      (IsLocalization.Away.algebraMap_isUnit (Padic.coefficientExtensionUniformizer l E)))

/-- Tensor an arbitrary integral section morphism with E and use the recorded size descent.
Source: local normalization step 10, point-fibre coefficient normalization
(blueprint: lem-trf-local-normalization-strict-realization). -/
def rationalSectionMap (hl : l ≠ D.p)
    (N M : sfIntegralConstructibleCategory l E (Spec (.of D.k)))
    (f : (pointFibreIntegralAmbient D l E).obj N.obj ⟶
      (pointFibreIntegralAmbient D l E).obj M.obj) :
    (pointRationalFibre D l hl E).obj
        ((sfRationalConstructibleLocalization l E (Spec (.of D.k))).obj N) ⟶
      (pointRationalFibre D l hl E).obj
        ((sfRationalConstructibleLocalization l E (Spec (.of D.k))).obj M) :=
  (pointRationalFibreObjIso D l hl E _).hom ≫
    (pointFibreSizeDescent E).map
      (ObjectProperty.homMk
        ((@Functor.mapDerivedCategory _ _ _
          (HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} _) _ _ _
          (HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} _)
          (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (pointIntegralToField l E))
          _ _ _).map f) :
        pointFibreRationalLarge D l hl E N ⟶ pointFibreRationalLarge D l hl E M) ≫
    (pointRationalFibreObjIso D l hl E _).inv

/-- The canonical Hom comparison to pointRationalFibre coordinates, fixed on pure tensors.
Source: local normalization step 10 and the point-fibre rationalization formula
(blueprint: lem-trf-local-normalization-strict-realization).
Proof: integral point sections have bounded finitely generated complete cohomology.
Over the discrete valuation ring their bounded complexes are perfect. Hom out of
these complexes therefore commutes with flat localization at the uniformizer.
The canonical tensor map is an isomorphism; coefficient identification and the
recorded size-descent equivalence preserve it. On a pure tensor it is precisely
scalar multiplication after tensoring the section morphism with E. Pure tensors
generate, so this normalization determines the additive equivalence uniquely.
This concerns integral point sections, and assumes nothing about perfectness or
Tor amplitude of finite reductions. -/
theorem rationalPointHom_existsUnique (hl : l ≠ D.p)
    (N M : sfIntegralConstructibleCategory l E (Spec (.of D.k))) :
    ∃! e : ((rationalize l E).obj ((pointFibreIntegralAmbient D l E).obj N.obj) ⟶
        (rationalize l E).obj ((pointFibreIntegralAmbient D l E).obj M.obj)) ≃+
      ((pointRationalFibre D l hl E).obj
          ((sfRationalConstructibleLocalization l E (Spec (.of D.k))).obj N) ⟶
        (pointRationalFibre D l hl E).obj
          ((sfRationalConstructibleLocalization l E (Spec (.of D.k))).obj M)),
      ∀ (a : Localization.Away (ULift.up (Padic.coefficientExtensionUniformizer l E)))
        (f : (pointFibreIntegralAmbient D l E).obj N.obj ⟶
          (pointFibreIntegralAmbient D l E).obj M.obj),
        e (a • (rationalize l E).map f) =
          rationalScalar l E a • rationalSectionMap D l E hl N M f := by
  sorry

/-- The uniquely normalized comparison, including its inverse on rational fibre morphisms.
Source: local normalization step 10
(blueprint: lem-trf-local-normalization-strict-realization). -/
def rationalPointHom (hl : l ≠ D.p)
    (N M : sfIntegralConstructibleCategory l E (Spec (.of D.k))) :=
  (rationalPointHom_existsUnique D l E hl N M).exists.choose

/-- Successive rational transport uses the specified rational point-transport components.
Source: local normalization step 10 and def-weil-frobenius-point-transport
(blueprint: lem-trf-local-normalization-strict-realization). -/
def successiveRational (hl : l ≠ D.p)
    (N : sfIntegralConstructibleCategory l E (Spec (.of D.k))) :
    (j : ℕ) →
      (pointRationalFibre D l hl E).obj
          ((sfRationalConstructibleLocalization l E (Spec (.of D.k))).obj N) ⟶
        (pointRationalFibre D l hl E).obj
          ((sfRationalConstructibleLocalization l E (Spec (.of D.k))).obj
            ((iteratedPointPullback D l E hl j).obj N))
  | 0 => 𝟙 _
  | j + 1 => successiveRational hl N j ≫
      frobeniusPointTransportRational D l hl E
        ((sfRationalConstructibleLocalization l E (Spec (.of D.k))).obj
          ((iteratedPointPullback D l E hl j).obj N))

/-- Rational A in the recorded point-fibre category: rational transports then return.
Source: local normalization step 10
(blueprint: lem-trf-local-normalization-strict-realization). -/
def rationalAInFibre (hl : l ≠ D.p) (B : IntegralComparisonSystem.{u} l)
    {m : ℕ} (Z : Point D X₀ m)
    (K : sfIntegralConstructibleCategory l E (D.geometricFiber X₀).left) :=
  let N := (@constructibleIntegralPullback l _ E _ _ _ _ _ Z.z
    (frobeniusPointPrimeInvertible D l hl)
    (D.schemeFrobeniusCoefficientInvertible X₀ l hl)).obj K
  let M := (@constructibleIntegralPullback l _ E _ _ _ _ _ (target D X₀ Z)
    (frobeniusPointPrimeInvertible D l hl)
    (D.schemeFrobeniusCoefficientInvertible X₀ l hl)).obj K
  successiveRational D l E hl N m ≫
    rationalSectionMap D l E hl ((iteratedPointPullback D l E hl m).obj N) M
      ((pointFibreIntegralAmbient D l E).map
        ((pointPowerModel D l E hl B N m).hom ≫ (integralReturn D l E X₀ hl B Z K).hom))

/-- Rational A in raw module coordinates is the canonical inverse image of the
independently specified successive rational point-fibre recipe.
Source: local normalization step 10
(blueprint: lem-trf-local-normalization-strict-realization). -/
def rationalA (hl : l ≠ D.p) (B : IntegralComparisonSystem.{u} l)
    {m : ℕ} (Z : Point D X₀ m)
    (K : sfIntegralConstructibleCategory l E (D.geometricFiber X₀).left) :=
  (rationalPointHom D l E hl
    ((@constructibleIntegralPullback l _ E _ _ _ _ _ Z.z
      (frobeniusPointPrimeInvertible D l hl)
      (D.schemeFrobeniusCoefficientInvertible X₀ l hl)).obj K)
    ((@constructibleIntegralPullback l _ E _ _ _ _ _ (target D X₀ Z)
      (frobeniusPointPrimeInvertible D l hl)
      (D.schemeFrobeniusCoefficientInvertible X₀ l hl)).obj K)).symm
    (rationalAInFibre D l E X₀ hl B Z K)

/-- All local-normalization assertions on the same simultaneous quotient representative.
Source: local normalization steps 1--10
(blueprint: lem-trf-local-normalization-strict-realization). -/
def Laws (hl : l ≠ D.p) (B : IntegralComparisonSystem.{u} l)
    {m : ℕ} (hm : 1 ≤ m) (Z : Point D X₀ m) : Prop :=
  (∀ (K : sfIntegralConstructibleCategory l E (D.geometricFiber X₀).left)
      (Q : (integralOperationsGoodComplex l E (D.geometricFiber X₀).left).FullSubcategory)
      (q : DerivedCategory.Q.obj Q.obj ≅ K.obj),
    Components D l E X₀ hl hm Z Q.obj (strictRecipes D l E X₀ hl hm Z Q.obj) ∧
    CoefficientCompatibility D l E X₀ hl hm Z Q ∧
    realize D l E X₀ Z K Q q (strictRecipes D l E X₀ hl hm Z Q.obj).1 =
      integralAInCoordinates D l E X₀ hl B Z K ∧
    ((∀ n : ℕ, finiteA D l E X₀ m n Z.z Z.returnSquare Q.obj =
        finiteB D l E X₀ hl m hm n Z.z Z.fixed Q.obj) →
      (strictRecipes D l E X₀ hl hm Z Q.obj).1 =
        (strictRecipes D l E X₀ hl hm Z Q.obj).2 ∧
      integralAInCoordinates D l E X₀ hl B Z K =
        realize D l E X₀ Z K Q q (strictRecipes D l E X₀ hl hm Z Q.obj).2 ∧
      (ScalarLocalization.localization
        (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) _
        (ULift.up (Padic.coefficientExtensionUniformizer l E))).map
          (integralAInCoordinates D l E X₀ hl B Z K) =
        (ScalarLocalization.localization
          (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) _
          (ULift.up (Padic.coefficientExtensionUniformizer l E))).map
            (realize D l E X₀ Z K Q q (strictRecipes D l E X₀ hl hm Z Q.obj).2))) ∧
  (∀ K : sfIntegralConstructibleCategory l E (D.geometricFiber X₀).left,
    (rationalize l E).map (integralA D l E X₀ hl B Z K) =
      rationalA D l E X₀ hl B Z K) ∧
  (∀ (K K' : sfIntegralConstructibleCategory l E (D.geometricFiber X₀).left) (f : K ⟶ K'),
    (integralJ D l E Z.z).map f ≫ integralA D l E X₀ hl B Z K' =
      integralA D l E X₀ hl B Z K ≫ (integralJ D l E (target D X₀ Z)).map f) ∧
  (∀ (K K' : sfRationalConstructibleCategory l E (D.geometricFiber X₀).left) (f : K ⟶ K'),
    (rationalJ D l E Z.z).map f ≫ rationalA D l E X₀ hl B Z K'.obj =
      rationalA D l E X₀ hl B Z K.obj ≫ (rationalJ D l E (target D X₀ Z)).map f)

/-- Strict realization of local Frobenius normalization, with every quotient and all raw
rational morphisms. No reduction is required to be perfect or of finite Tor amplitude.

Source: main-20261015, sec-trace-formula/sk-thm-trace-transport,
prop-trf-karoubi-independence.proof.md, final transport sentence, local normalization
steps 5--7 (blueprint: lem-trf-local-normalization-strict-realization).

Proof, in the ten DAG steps:
1. Quotients of the one flat-term K-flat Q remain flat-term K-flat by change of rings;
finite pullbacks preserve this. Tensor associativity gives every derived quotient map.
2. Point restriction, insertion and the actual compositors commute with quotient maps.
Compose their natural chain maps to obtain the strict A map.
3. Write kappa in its specified absolute-Frobenius normal form. Relative-Frobenius
restriction, the coefficient tensor-unit map, inverse-image coprojections and
sheafification all commute with actual quotient-linear maps. Together with the fixed
point compositor this gives the strict B map.
4. On tensor generators both quotient-change paths give x tensor bar(a)b. Use the
canonical coefficient-change square for kappa and exact point-section reduction.
Bounded constructible reductions suffice; no finite Tor bound is needed.
5. Finite pullbacks of normalized effective systems are normalized and effective.
Use the whole-system counit and the two-coordinate point/representative comparison;
iterated pullbacks are identified by counit realization substitution.
6. The point-tower power realization identifies restriction/insertion with the actual
integral iota. The whole-tower counit characterization fixes this comparison, including
zero shifted-product normalization. Induct through I^0=1 and I^(j+1)=iota I^j.
7. The specified compositor realizes the strict return square. Functoriality of Rlim
then identifies A with integralA. The stipulated B realization is the realization of
its strict composite, with the identical endpoint comparisons in realize.
8. Equality of every chain component gives equality of strict natural transformations.
Apply the Rlim functor and the same endpoint comparisons to obtain integral equality.
9. Induct through the successive integral iota using its naturality; then use the
naturality of the specified return-square compositor for integralA.
10. Raw scalar localization preserves equality, identity and composition. It carries
each iota to its scalar extension and hence carries the successive recipe to rationalA.
Naturality on integral maps extends to pure tensors by scalar bilinearity, and to every
localized morphism by additivity. No Karoubi completion or Tor-amplitude hypothesis occurs. -/
theorem localNormalizationStrictRealization (hl : l ≠ D.p)
    (B : IntegralComparisonSystem.{u} l) [IsSeparated X₀.hom]
    {m : ℕ} (hm : 1 ≤ m) (Z : Point D X₀ m) : Laws D l E X₀ hl B hm Z := by
  sorry

end WeilConjectures.LocalNormalization
