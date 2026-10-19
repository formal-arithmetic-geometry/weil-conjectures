/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.EtaleCoefficientSystemAdjoint
public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
public import Sheaf.Paper.ExceptionalCoefficientComparison
public import Sheaf.Paper.NormalizedEtaleOriginWitnesses
public import Sheaf.CategoryTheory.ConstantRingModuleSheaves
public import Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded
public import Mathlib.CategoryTheory.Triangulated.Subcategory

import Sheaf.AlgebraicGeometry.AffineSpaceAmbientAdjunction
import Sheaf.AlgebraicGeometry.OpenDirectImageFiniteCoefficients
import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import Sheaf.AlgebraicGeometry.OpenDirectImageClassicalAmplitude
import Sheaf.AlgebraicGeometry.AffineSpaceTopTrace
import Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality
import Sheaf.AlgebraicGeometry.ProperDerivedDirectImageCoproducts
import Sheaf.AlgebraicGeometry.ProperProjectionFormula
import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
import Sheaf.AlgebraicGeometry.EtaleClosedSupportTriangle
import Sheaf.AlgebraicGeometry.ExceptionalConstantTensor
import Sheaf.AlgebraicGeometry.FiniteCohomologicalDimensionDirectImageCoproducts
import Sheaf.AlgebraicGeometry.ResidueTorAmplitudeTest
import Sheaf.AlgebraicGeometry.FiniteRingCompactSupportFiniteness
import Sheaf.CategoryTheory.GrothendieckDerivedBrownRightAdjoint
import WeilConjectures.SixFunctors.Etale.Derived.Triangulated
import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Sheaf.Paper.CoefficientEvaluationDerivedLeftAdjoint
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.CategoryTheory.SystemLevelLeftExtension
import Sheaf.Paper.SfAffineChartFactorizationGluing
import Sheaf.Paper.FiniteCoefficientFlatModel
import Sheaf.Paper.FiniteCoefficientReductionFlatModel
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import Sheaf.Paper.ProjectionMateExact
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Sheaf.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.SixFunctors.Finite.Stalk
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.AlgebraicGeometry.EtaleClosedSupportTorAmplitude
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
import WeilConjectures.ConstructibleSheaf.KernelCokernel

/-! # Finite exceptional adjunction on normalized systems

Source: Bhatt--Scholze, Lemma 6.7.18, and the ordinary derived system construction
in the proof of blueprint lem-per-artin-gabber-affine-curve
(blueprint: lem-per-finite-exceptional-system-adjunction).

The index `n : ℕ` denotes the positive coefficient level `n + 1`. The system category
is the existing category of strict semilinear systems. Its full normalized subcategory
imposes bounded constructibility and finite Tor amplitude separately at every level.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
namespace AlgebraicGeometry
namespace FiniteExceptionalSystems

-- Keep the recorded localization when other geometric derived instances are imported.
attribute [instance 4000] strictEtaleLevelDerived strictEtaleSystemDerived

variable (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The positive coefficient quotient, with its existing construction unchanged.
Source: Bhatt--Scholze 6.7.18 (blueprint: lem-per-finite-exceptional-system-adjunction). -/
abbrev Coeff (n : ℕ) := Padic.coefficientExtensionRing l E (n + 1)

/-- Finiteness at every positive level.
Source: Bhatt--Scholze 6.7.18 (blueprint: lem-per-finite-exceptional-system-adjunction). -/
instance coefficientFinite (n : ℕ) : Finite (Coeff l E n) :=
  Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))

/-- The quotient map induced by the identity of the valuation ring.
Source: Bhatt--Scholze 6.7.18 (blueprint: lem-per-finite-exceptional-system-adjunction). -/
def quotient {m n : ℕ} (h : n ≤ m) : Coeff l E m →+* Coeff l E n :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))

/-- Quotient maps compose strictly.
Source: Bhatt--Scholze 6.7.18 (blueprint: lem-per-finite-exceptional-system-adjunction).
Proof: both maps send the class of an integer to its class in the final quotient;
quotient induction proves equality. -/
theorem quotient_comp {p m n : ℕ} (h : m ≤ p) (k : n ≤ m) :
    quotient l E (k.trans h) = (quotient l E k).comp (quotient l E h) := by
  sorry

/-- The self-quotient is the identity.
Source: Bhatt--Scholze 6.7.18 (blueprint: lem-per-finite-exceptional-system-adjunction).
Proof: quotient induction identifies both maps on every class. -/
theorem quotient_id (n : ℕ) : quotient l E (le_refl n) = RingHom.id _ := by
  sorry

/-- Actual coefficient extension, using the recorded derived scalar adjunction.
Source: Bhatt--Scholze 6.7.18 (blueprint: lem-per-finite-exceptional-system-adjunction). -/
abbrev Q (T : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :=
  Etale.scalarExtension (quotient l E h) T

/-- The shift comparison induced by the canonical scalar adjunction.
Source: Stacks 06YY (blueprint: lem-per-finite-exceptional-system-adjunction). -/
instance quotientShift (T : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    (Q l E T h).CommShift ℤ :=
  (Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars T.smallEtaleTopology (quotient l E h))).leftAdjointCommShift ℤ

/-- Canonical tensor reassociation, fixed by scalar restriction and its adjunction.
Source: Bhatt--Scholze 6.7.18 (blueprint: lem-per-finite-exceptional-system-adjunction). -/
def assoc (T : Scheme.{u}) {p m n : ℕ} (h : m ≤ p) (k : n ≤ m) :
    Q l E T h ⋙ Q l E T k ≅ Q l E T (k.trans h) :=
  ProEtale.pbcFixedScalarExtensionComp T.smallEtaleTopology _ _ _ (quotient_comp l E h k)

/-- The canonical identity-extension comparison.
Source: Bhatt--Scholze 6.7.18 (blueprint: lem-per-finite-exceptional-system-adjunction). -/
def self (T : Scheme.{u}) (n : ℕ) : Q l E T (le_refl n) ≅ 𝟭 _ :=
  ProEtale.normalizedOriginScalarUnit T.smallEtaleTopology _ (quotient_id l E n)

/-- Exactly bounded constructibility and finite Tor amplitude, using the recorded predicates.
Source: Bhatt--Scholze 6.7.18 (blueprint: lem-per-finite-exceptional-system-adjunction). -/
def Ctf (T : Scheme.{u}) (n : ℕ) : ObjectProperty (Etale.DerivedCategoryModule (Coeff l E n) T) :=
  fun M ↦ Etale.DerivedCategory.isBoundedConstructible (Coeff l E n) T M ∧
    ∃ a b : ℤ, Etale.DerivedCategory.hasTorAmplitudeIn (Coeff l E n) T a b M

/-- The already defined strict-system evaluation package for this coefficient tower.
Source: Bhatt--Scholze 6.7.18 (blueprint: lem-per-finite-exceptional-system-adjunction). -/
abbrev Evaluation (T : Scheme.{u}) :=
  StrictEtaleEvaluation T (Padic.coefficientExtensionIntegers l E)
    (Padic.coefficientExtensionUniformizer l E)

/-- The strict module-sheaf category at a positive coefficient level.
Source: Bhatt--Scholze 6.7.18 (blueprint: lem-per-finite-exceptional-system-adjunction). -/
abbrev Level (T : Scheme.{u}) (n : ℕ) :=
  strictEtaleLevel T (Padic.coefficientExtensionIntegers l E)
    (Padic.coefficientExtensionUniformizer l E) n

/-- Restriction to constant scalars in the existing constant commutative ring sheaf.
This retains sections and maps, so it is the canonical presentation change.
Source: Stacks 03CY; Bhatt--Scholze 6.7.18
(blueprint: lem-per-finite-exceptional-system-adjunction). -/
def levelRestriction (T : Scheme.{u}) (n : ℕ) :
    Level l E T n ⥤ Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (Coeff l E n)) :=
  SheafOfModules.restrictScalars
      (CategoryTheory.realizationRingIso T.smallEtaleTopology (Coeff l E n)).inv ⋙
    CategoryTheory.constantRingModuleRestriction T.smallEtaleTopology (Coeff l E n)

/-- Constant-scalar restriction is additive and exact, and an equivalence.
Source: Stacks 03CY; Bhatt--Scholze 6.7.18
(blueprint: lem-per-finite-exceptional-system-adjunction).
Proof: a fixed-ring module action extends uniquely to the sheafification of its
constant ring presheaf by gluing. This inverse keeps the underlying abelian sheaf
and every map. The identity on sections gives the unit and counit. Kernels and
sheafified cokernels are unchanged, proving additivity and exactness. -/
theorem levelRestriction_exact (T : Scheme.{u}) (n : ℕ) :
    (levelRestriction l E T n).Additive ∧
      PreservesFiniteLimits (levelRestriction l E T n) ∧
      PreservesFiniteColimits (levelRestriction l E T n) ∧
      (levelRestriction l E T n).IsEquivalence := by
  sorry

/-- Additivity of the canonical presentation change.
Source: Stacks 03CY (blueprint: lem-per-finite-exceptional-system-adjunction). -/
instance levelRestriction_additive (T : Scheme.{u}) (n : ℕ) :
    (levelRestriction l E T n).Additive := (levelRestriction_exact l E T n).1

/-- Left exactness of the canonical presentation change.
Source: Stacks 03CY (blueprint: lem-per-finite-exceptional-system-adjunction). -/
instance levelRestriction_limits (T : Scheme.{u}) (n : ℕ) :
    PreservesFiniteLimits (levelRestriction l E T n) := (levelRestriction_exact l E T n).2.1

/-- Right exactness of the canonical presentation change.
Source: Stacks 03CY (blueprint: lem-per-finite-exceptional-system-adjunction). -/
instance levelRestriction_colimits (T : Scheme.{u}) (n : ℕ) :
    PreservesFiniteColimits (levelRestriction l E T n) := (levelRestriction_exact l E T n).2.2.1

/-- The exact presentation change on ordinary unbounded derived categories.
Source: Stacks 03CY (blueprint: lem-per-finite-exceptional-system-adjunction). -/
def realization (T : Scheme.{u}) (n : ℕ) := (levelRestriction l E T n).mapDerivedCategory

/-- Normalized systems with bounded constructible finite-Tor evaluations.
The existential bounds occur inside `∀ n`, never outside it.
Source: Bhatt--Scholze 6.7.18 and the system construction in the blueprint proof
(blueprint: lem-per-finite-exceptional-system-adjunction). -/
def NormalizedCtf (T : Scheme.{u}) (P : Evaluation l E T) :
    ObjectProperty (DerivedCategory (strictEtaleCoefficientSystem T
      (Padic.coefficientExtensionIntegers l E) (Padic.coefficientExtensionUniformizer l E))) :=
  fun M ↦ SheafOfModules.IsNormalizedCoefficientSystem
    (J := T.smallEtaleTopology) _ _ P M ∧
      ∀ n : ℕ, Ctf l E T n ((realization l E T n).obj ((P.evaluation n).obj M))

/-- The full subcategory has the induced triangulation.
Source: Bhatt--Scholze 6.7.18 and the system construction in the blueprint proof
(blueprint: lem-per-finite-exceptional-system-adjunction).
Proof: exact evaluation and scalar extension commute with shifts and triangles.
For a triangle, two invertible reduction maps imply the third is invertible.
Constructibility is Serre and finite Tor amplitude is stable under triangles.
At each level enlarge the two finite intervals; no simultaneous bound is needed. -/
theorem normalizedCtf_triangulated (T : Scheme.{u}) (P : Evaluation l E T) :
    (NormalizedCtf l E T P).IsTriangulated := by
  sorry

attribute [instance] normalizedCtf_triangulated

/-- The ordinary finite compact-support functor attached to the chosen compactification.
Source: Bhatt--Scholze 6.7.18 (blueprint: lem-per-finite-exceptional-system-adjunction). -/
abbrev F {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (n : ℕ) :=
  Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (Coeff l E n)) c

/-- The finite adjunctions and their specified quotient mates. All maps are actual natural
transformations on ordinary derived categories. Invertibility of the exceptional mate
is required exactly on bounded constructible finite-Tor inputs.
Source: Bhatt--Scholze 6.7.18 and its counit-transpose normalization
(blueprint: lem-per-finite-exceptional-system-adjunction). -/
structure FiniteData {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) where
  right : ∀ n : ℕ, Etale.DerivedCategoryModule (Coeff l E n) Y ⥤
    Etale.DerivedCategoryModule (Coeff l E n) X
  adjunction : ∀ n : ℕ, F l E c n ⊣ right n
  [rightAdditive : ∀ n : ℕ, (right n).Additive]
  [rightShift : ∀ n : ℕ, (right n).CommShift ℤ]
  rightExact : ∀ n : ℕ, (right n).IsTriangulated
  rightLinear : ∀ n : ℕ, (right n).Linear (Coeff l E n)
  leftCtf : ∀ (n : ℕ) (K : Etale.DerivedCategoryModule (Coeff l E n) X),
    Ctf l E X n K → Ctf l E Y n ((F l E c n).obj K)
  rightCtf : ∀ (n : ℕ) (K : Etale.DerivedCategoryModule (Coeff l E n) Y),
    Ctf l E Y n K → Ctf l E X n ((right n).obj K)
  scalarCtf : ∀ (T : Scheme.{u}) {m n : ℕ} (h : n ≤ m)
    (K : Etale.DerivedCategoryModule (Coeff l E m) T),
    Ctf l E T m K → Ctf l E T n ((Q l E T h).obj K)
  projection : ∀ {m n : ℕ} (h : n ≤ m),
    F l E c m ⋙ Q l E Y h ≅ Q l E X h ⋙ F l E c n
  projection_normalized : ∀ {m n : ℕ} (h : n ≤ m)
    (K : Etale.DerivedCategoryModule (Coeff l E m) X),
    (projection h).hom.app K = Etale.ExceptionalCoefficients.compactSupportMap
      (quotient l E h) c K
  comparison : ∀ {m n : ℕ} (h : n ≤ m), right m ⋙ Q l E X h ⟶ Q l E Y h ⋙ right n
  comparison_isIso : ∀ {m n : ℕ} (h : n ≤ m)
    (K : Etale.DerivedCategoryModule (Coeff l E m) Y),
    Ctf l E Y m K → IsIso ((comparison h).app K)
  counit : ∀ {m n : ℕ} (h : n ≤ m)
    (K : Etale.DerivedCategoryModule (Coeff l E m) Y),
    (projection h).hom.app ((right m).obj K) ≫
        (F l E c n).map ((comparison h).app K) ≫
        (adjunction n).counit.app ((Q l E Y h).obj K) =
      (Q l E Y h).map ((adjunction m).counit.app K)
  unit : ∀ {m n : ℕ} (h : n ≤ m)
    (K : Etale.DerivedCategoryModule (Coeff l E m) X),
    (Q l E X h).map ((adjunction m).unit.app K) ≫
        (comparison h).app ((F l E c m).obj K) ≫
        (right n).map ((projection h).hom.app K) =
      (adjunction n).unit.app ((Q l E X h).obj K)
  projection_id : ∀ (n : ℕ) (K : Etale.DerivedCategoryModule (Coeff l E n) X),
    (projection (le_refl n)).hom.app K ≫ (F l E c n).map ((self l E X n).hom.app K) =
      (self l E Y n).hom.app ((F l E c n).obj K)
  comparison_id : ∀ (n : ℕ) (K : Etale.DerivedCategoryModule (Coeff l E n) Y),
    (comparison (le_refl n)).app K ≫ (right n).map ((self l E Y n).hom.app K) =
      (self l E X n).hom.app ((right n).obj K)
  projection_comp : ∀ {p m n : ℕ} (h : m ≤ p) (k : n ≤ m)
    (K : Etale.DerivedCategoryModule (Coeff l E p) X),
    (Q l E Y k).map ((projection h).hom.app K) ≫
        (projection k).hom.app ((Q l E X h).obj K) ≫
        (F l E c n).map ((assoc l E X h k).hom.app K) =
      (assoc l E Y h k).hom.app ((F l E c p).obj K) ≫
        (projection (k.trans h)).hom.app K
  comparison_comp : ∀ {p m n : ℕ} (h : m ≤ p) (k : n ≤ m)
    (K : Etale.DerivedCategoryModule (Coeff l E p) Y),
    (Q l E X k).map ((comparison h).app K) ≫
        (comparison k).app ((Q l E Y h).obj K) ≫
        (right n).map ((assoc l E Y h k).hom.app K) =
      (assoc l E X h k).hom.app ((right p).obj K) ≫ (comparison (k.trans h)).app K
  unit_shift : ∀ n : ℕ, NatTrans.CommShift (adjunction n).unit ℤ
  counit_shift : ∀ n : ℕ, NatTrans.CommShift (adjunction n).counit ℤ
  projection_shift : ∀ {m n : ℕ} (h : n ≤ m), NatTrans.CommShift (projection h).hom ℤ
  comparison_shift : ∀ {m n : ℕ} (h : n ≤ m), NatTrans.CommShift (comparison h) ℤ

/-- The already recorded system compact-support construction, specialized to the actual tower.
Source: Bhatt--Scholze 6.7.18 and the blueprint system construction
(blueprint: lem-per-finite-exceptional-system-adjunction). -/
abbrev Support {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  StrictEtaleCompactSupport (Padic.coefficientExtensionIntegers l E)
    (Padic.coefficientExtensionUniformizer l E) c

/-- Shift on simultaneous open extension is the localization of the termwise shift.
Source: Zheng, Construction 5.15 (blueprint: lem-per-finite-exceptional-system-adjunction). -/
instance supportOpenShift {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    (S : Support l E c) : S.derivedOpen.CommShift ℤ :=
  letI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso _ (.up ℤ))
      (S.val.openExtension.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
      S.derivedOpen := ⟨S.val.openFactors⟩
  Functor.commShiftOfLocalization DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ)) ℤ
    (S.val.openExtension.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) S.derivedOpen

/-- Shift on the proper inverse image is localized from its termwise exact functor.
Source: Zheng, Construction 5.15 (blueprint: lem-per-finite-exceptional-system-adjunction). -/
instance supportInverseShift {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    (S : Support l E c) : S.properDerived.system.inverse.CommShift ℤ :=
  letI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso _ (.up ℤ))
      (S.properImage.inverse.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
      S.properDerived.system.inverse := ⟨S.properDerived.system.inverseFactors⟩
  Functor.commShiftOfLocalization DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ)) ℤ
    (S.properImage.inverse.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    S.properDerived.system.inverse

/-- Shift on proper direct image is the adjunction-induced shift.
Source: Zheng, Construction 5.15 (blueprint: lem-per-finite-exceptional-system-adjunction). -/
instance supportDirectShift {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    (S : Support l E c) : S.properDerived.system.direct.CommShift ℤ :=
  S.properDerived.system.adjunction.rightAdjointCommShift ℤ

/-- Compact-support shift is the composite of the canonical open and proper shifts.
Source: Zheng, Construction 5.15 (blueprint: lem-per-finite-exceptional-system-adjunction). -/
instance supportShift {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    (S : Support l E c) : S.functor.CommShift ℤ :=
  inferInstanceAs ((S.derivedOpen ⋙ S.properDerived.system.direct).CommShift ℤ)

/-- Restrict the actual simultaneous compact-support functor to the specified full subcategories.
Source: blueprint system construction after Bhatt--Scholze 6.7.18
(blueprint: lem-per-finite-exceptional-system-adjunction). -/
def systemLeft {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    (PX : Evaluation l E X) (PY : Evaluation l E Y) (S : Support l E c)
    (h : ∀ M, NormalizedCtf l E X PX M → NormalizedCtf l E Y PY (S.functor.obj M)) :=
  (NormalizedCtf l E Y PY).lift ((NormalizedCtf l E X PX).ι ⋙ S.functor)
    (fun M ↦ h M.obj M.property)

/-- Restriction uses the existing induced shift on a triangulated full subcategory.
Source: Zheng, Construction 5.15 (blueprint: lem-per-finite-exceptional-system-adjunction). -/
instance systemLeftShift {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    (PX : Evaluation l E X) (PY : Evaluation l E Y) (S : Support l E c)
    (h : ∀ M, NormalizedCtf l E X PX M → NormalizedCtf l E Y PY (S.functor.obj M)) :
    (systemLeft l E PX PY S h).CommShift ℤ :=
  inferInstanceAs (((NormalizedCtf l E Y PY).lift
    ((NormalizedCtf l E X PX).ι ⋙ S.functor) (fun M ↦ h M.obj M.property)).CommShift ℤ)

/-- Evaluations on the full normalized subcategory, in ordinary fixed-ring coefficients.
Source: blueprint system construction after Bhatt--Scholze 6.7.18
(blueprint: lem-per-finite-exceptional-system-adjunction). -/
def eval (T : Scheme.{u}) (P : Evaluation l E T) (n : ℕ) :=
  (NormalizedCtf l E T P).ι ⋙ P.evaluation n ⋙ realization l E T n

/-- Canonical scalar-restriction transport between the two coefficient presentations.
The section equation and the localization equation fix both comparisons before any
exceptional adjunction is considered.
Source: Stacks 03CY, 06YY; Bhatt--Scholze 6.7.18
(blueprint: lem-per-finite-exceptional-system-adjunction). -/
structure Presentation (T : Scheme.{u}) (P : Evaluation l E T) where
  ordinary : ∀ {m n : ℕ} (h : n ≤ m),
    SheafOfModules.coefficientRestriction (J := T.smallEtaleTopology)
        (Padic.coefficientExtensionIntegers l E) (Padic.coefficientExtensionUniformizer l E) h ⋙
        levelRestriction l E T m ≅
      levelRestriction l E T n ⋙ Sheaf.restrictScalars T.smallEtaleTopology (quotient l E h)
  sections : ∀ {m n : ℕ} (h : n ≤ m) (M : Level l E T n) (U : T.Etaleᵒᵖ)
    (x : (((SheafOfModules.coefficientRestriction (J := T.smallEtaleTopology)
      (Padic.coefficientExtensionIntegers l E) (Padic.coefficientExtensionUniformizer l E) h ⋙
        levelRestriction l E T m).obj M).obj.obj U)),
    HEq (((ordinary h).hom.app M).hom.app U x) x
  derived : ∀ {m n : ℕ} (h : n ≤ m),
    (P.scalar h).restriction ⋙ realization l E T m ≅
      realization l E T n ⋙ Sheaf.derivedRestrictScalars T.smallEtaleTopology (quotient l E h)
  representative : ∀ {m n : ℕ} (h : n ≤ m) (K : CochainComplex (Level l E T n) ℤ),
    (derived h).hom.app (DerivedCategory.Q.obj K) ≫
        (Sheaf.derivedRestrictScalars T.smallEtaleTopology (quotient l E h)).map
          ((Functor.mapDerivedCategoryFactors (levelRestriction l E T n)).hom.app K) ≫
        (Functor.mapDerivedCategoryFactors
          (Sheaf.restrictScalars T.smallEtaleTopology (quotient l E h))).hom.app
            (((levelRestriction l E T n).mapHomologicalComplex (.up ℤ)).obj K) =
      (realization l E T m).map ((P.scalar h).restrictionFactors.hom.app K) ≫
        (Functor.mapDerivedCategoryFactors (levelRestriction l E T m)).hom.app
          (((SheafOfModules.coefficientRestriction (J := T.smallEtaleTopology)
            (Padic.coefficientExtensionIntegers l E)
            (Padic.coefficientExtensionUniformizer l E) h).mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (ordinary h) (.up ℤ)).hom.app K)

/-- Actual transition-adjoint, after the canonical coefficient presentation change.
Source: Stacks 06YY; Bhatt--Scholze 6.7.18
(blueprint: lem-per-finite-exceptional-system-adjunction). -/
def reduction (T : Scheme.{u}) (P : Evaluation l E T) (A : Presentation l E T P)
    {m n : ℕ} (h : n ≤ m)
    (M : DerivedCategory (strictEtaleCoefficientSystem T
      (Padic.coefficientExtensionIntegers l E) (Padic.coefficientExtensionUniformizer l E))) :=
  ((Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars T.smallEtaleTopology (quotient l E h))).homEquiv _ _).symm
      ((realization l E T m).map ((P.transition h).app M) ≫
        (A.derived h).hom.app ((P.evaluation n).obj M))

/-- Canonical presentation change for a geometric inverse/direct-image adjunction.
The direct comparison is the specified underlying-set comparison on every section;
the ordinary inverse is its adjunction mate. Localization fixes the derived inverse
on every complex, and the derived counit fixes the derived direct comparison.
Source: Stacks 03CY; Zheng, Construction 5.15
(blueprint: lem-per-finite-exceptional-system-adjunction). -/
structure GeometricComparison {T U : Scheme.{u}} (g : T ⟶ U)
    (I : StrictEtaleOrdinaryImage (Padic.coefficientExtensionIntegers l E)
      (Padic.coefficientExtensionUniformizer l E) g)
    (PU : Evaluation l E U) (PT : Evaluation l E T)
    (D : SheafOfModules.CoefficientSystemDerivedImage
      (J := U.smallEtaleTopology) (K := T.smallEtaleTopology)
      (Padic.coefficientExtensionIntegers l E) (Padic.coefficientExtensionUniformizer l E)
      _ _ _ I PU PT) where
  ordinaryDirect : ∀ n : ℕ, I.right n ⋙ levelRestriction l E U n ≅
    levelRestriction l E T n ⋙ Etale.lowerStar (ModuleCat.{u + 1} (Coeff l E n)) g
  sections : ∀ (n : ℕ) (M : Level l E T n) (V : U.Etaleᵒᵖ)
    (x : (((I.right n ⋙ levelRestriction l E U n).obj M).obj.obj V)),
    HEq (((ordinaryDirect n).hom.app M).hom.app V x)
      (((I.rightUnderlying n).hom.app M).hom.app V x)
  ordinaryInverse : ∀ n : ℕ, (I.lift n).modules ⋙ levelRestriction l E T n ≅
    levelRestriction l E U n ⋙ Etale.upperStar (ModuleCat.{u + 1} (Coeff l E n)) g
  transpose : ∀ (n : ℕ) (M : Level l E U n) (N : Level l E T n)
    (h : (I.lift n).modules.obj M ⟶ N),
    (levelRestriction l E U n).map ((I.levelAdj n).homEquiv M N h) ≫
        (ordinaryDirect n).hom.app N =
      (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} (Coeff l E n)) g).homEquiv _ _
        ((ordinaryInverse n).inv.app M ≫ (levelRestriction l E T n).map h)
  inverse : ∀ n : ℕ, (D.level n).inverse ⋙ realization l E T n ≅
    realization l E U n ⋙
      (Etale.upperStar (ModuleCat.{u + 1} (Coeff l E n)) g).mapDerivedCategory
  representative : ∀ (n : ℕ) (K : CochainComplex (Level l E U n) ℤ),
    (inverse n).hom.app (DerivedCategory.Q.obj K) ≫
        (Etale.upperStar (ModuleCat.{u + 1} (Coeff l E n)) g).mapDerivedCategory.map
          ((levelRestriction l E U n).mapDerivedCategoryFactors.hom.app K) ≫
        (Etale.upperStar (ModuleCat.{u + 1} (Coeff l E n)) g).mapDerivedCategoryFactors.hom.app
            (((levelRestriction l E U n).mapHomologicalComplex (.up ℤ)).obj K) =
      (realization l E T n).map ((D.level n).inverseFactors.hom.app K) ≫
        (levelRestriction l E T n).mapDerivedCategoryFactors.hom.app
          ((((I.lift n).modules).mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (ordinaryInverse n) (.up ℤ)).hom.app K)
  direct : ∀ n : ℕ, (D.level n).direct ⋙ realization l E U n ≅
    realization l E T n ⋙
      (Etale.lowerStar (ModuleCat.{u + 1} (Coeff l E n)) g).rightDerivedFunctor
  counit : ∀ (n : ℕ) (K : DerivedCategory (Level l E T n)),
    (inverse n).hom.app ((D.level n).direct.obj K) ≫
        (Etale.upperStar (ModuleCat.{u + 1} (Coeff l E n)) g).mapDerivedCategory.map
          ((direct n).hom.app K) ≫
        (Etale.mapDerivedUpperStarLowerStarAdjunction
          (ModuleCat.{u + 1} (Coeff l E n)) g).counit.app ((realization l E T n).obj K) =
      (realization l E T n).map ((D.level n).adjunction.counit.app K)

/-- The open/proper comparisons defining finite compact-support presentation change.
The open comparison is the mate of the normalized derived inverse comparison.
Source: Stacks 03CY; Zheng, Construction 5.15
(blueprint: lem-per-finite-exceptional-system-adjunction). -/
structure LevelComparison {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    (S : Support l E c) where
  openGeometry : GeometricComparison l E c.i S.openImage S.PZ S.PX S.openDerived
  properGeometry : GeometricComparison l E c.g S.properImage S.PY S.PZ S.properDerived
  openIso : ∀ n : ℕ, S.levelDerivedOpen n ⋙ realization l E c.Z n ≅
    realization l E X n ⋙
      (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} (Coeff l E n)) c.i).mapDerivedCategory
  open_counit : ∀ (n : ℕ) (K : DerivedCategory (Level l E c.Z n)),
    (openIso n).hom.app ((S.openDerived.level n).inverse.obj K) ≫
        (Etale.openImmersionLowerShriek
          (ModuleCat.{u + 1} (Coeff l E n)) c.i).mapDerivedCategory.map
            ((openGeometry.inverse n).hom.app K) ≫
        (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} (Coeff l E n)) c.i).counit.app
            ((realization l E c.Z n).obj K) =
      (realization l E c.Z n).map ((S.levelDerivedOpenAdjunction n).counit.app K)

/-- The canonical finite compact-support comparison: first the proper comparison,
then the open comparison, with no independently chosen isomorphism.
Source: Zheng, Construction 5.15 (blueprint: lem-per-finite-exceptional-system-adjunction). -/
def levelRealization {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    (S : Support l E c) (A : LevelComparison l E S) (n : ℕ) :
    S.levelFunctor n ⋙ realization l E Y n ≅ realization l E X n ⋙ F l E c n :=
  Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (A.properGeometry.direct n) ≪≫
    (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (A.openIso n) _ ≪≫
    Functor.associator _ _ _

/-- The system adjunction and its evaluation normalization. Its unit, counit and triangle
identities are morphisms and equalities in the full subcategories of the ordinary derived
categories of strict systems. Exactness uses their induced triangulations.
Source: blueprint system construction after Bhatt--Scholze 6.7.18
(blueprint: lem-per-finite-exceptional-system-adjunction). -/
structure SystemData {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    (PX : Evaluation l E X) (PY : Evaluation l E Y)
    (S : Support l E c) (D : FiniteData l E c)
    (hPX : PX = S.PX) (hPY : PY = S.PY) where
  preserves : ∀ M, NormalizedCtf l E X PX M →
    NormalizedCtf l E Y PY (S.functor.obj M)
  right : (NormalizedCtf l E Y PY).FullSubcategory ⥤
    (NormalizedCtf l E X PX).FullSubcategory
  adjunction : systemLeft l E PX PY S preserves ⊣ right
  [rightAdditive : right.Additive]
  [rightShift : right.CommShift ℤ]
  rightExact : right.IsTriangulated
  leftExact : (systemLeft l E PX PY S preserves).IsTriangulated
  actionX : StrictEtaleScalarAction X (Padic.coefficientExtensionIntegers l E)
    (Padic.coefficientExtensionUniformizer l E)
  actionY : StrictEtaleScalarAction Y (Padic.coefficientExtensionIntegers l E)
    (Padic.coefficientExtensionUniformizer l E)
  linear : ∀ (r : Padic.coefficientExtensionIntegers l E)
    (M : (NormalizedCtf l E Y PY).FullSubcategory),
    (right.map (ObjectProperty.homMk ((actionY.derived r).app M.obj))).hom =
      (actionX.derived r).app (right.obj M).obj
  levelComparison : LevelComparison l E S
  leftEvaluation : ∀ n : ℕ,
    systemLeft l E PX PY S preserves ⋙ eval l E Y PY n ≅ eval l E X PX n ⋙ F l E c n
  /-- The evaluation is fixed by the existing system comparison and the canonical
  open/proper presentation change, including the endpoint identifications. -/
  leftEvaluation_pinned : ∀ (n : ℕ) (M : (NormalizedCtf l E X PX).FullSubcategory),
    (leftEvaluation n).hom.app M =
      (realization l E Y n).map
        (eqToHom (congrArg (fun P : Evaluation l E Y ↦
            (P.evaluation n).obj (S.functor.obj M.obj)) hPY) ≫
          (S.evaluation n).hom.app M.obj ≫
          (S.levelFunctor n).map (eqToHom (congrArg (fun P : Evaluation l E X ↦
            (P.evaluation n).obj M.obj) hPX.symm))) ≫
        (levelRealization l E S levelComparison n).hom.app ((PX.evaluation n).obj M.obj)
  rightEvaluation : ∀ n : ℕ, right ⋙ eval l E X PX n ≅ eval l E Y PY n ⋙ D.right n
  unit : ∀ (n : ℕ) (M : (NormalizedCtf l E X PX).FullSubcategory),
    (eval l E X PX n).map (adjunction.unit.app M) ≫
        (rightEvaluation n).hom.app ((systemLeft l E PX PY S preserves).obj M) ≫
        (D.right n).map ((leftEvaluation n).hom.app M) =
      (D.adjunction n).unit.app ((eval l E X PX n).obj M)
  counit : ∀ (n : ℕ) (M : (NormalizedCtf l E Y PY).FullSubcategory),
    (F l E c n).map ((rightEvaluation n).hom.app M) ≫
        (D.adjunction n).counit.app ((eval l E Y PY n).obj M) =
      (leftEvaluation n).inv.app (right.obj M) ≫
        (eval l E Y PY n).map (adjunction.counit.app M)
  presentationX : Presentation l E X PX
  presentationY : Presentation l E Y PY
  right_transition : ∀ {m n : ℕ} (h : n ≤ m)
    (M : (NormalizedCtf l E Y PY).FullSubcategory),
    (Q l E X h).map ((rightEvaluation m).hom.app M) ≫
        (D.comparison h).app ((eval l E Y PY m).obj M) ≫
        (D.right n).map (reduction l E Y PY presentationY h M.obj) =
      reduction l E X PX presentationX h (right.obj M).obj ≫
        (rightEvaluation n).hom.app M
  left_transition : ∀ {m n : ℕ} (h : n ≤ m)
    (M : (NormalizedCtf l E X PX).FullSubcategory),
    (Q l E Y h).map ((leftEvaluation m).hom.app M) ≫
        (D.projection h).hom.app ((eval l E X PX m).obj M) ≫
        (F l E c n).map (reduction l E X PX presentationX h M.obj) =
      reduction l E Y PY presentationY h ((systemLeft l E PX PY S preserves).obj M).obj ≫
        (leftEvaluation n).hom.app M

/-- A simultaneous choice for every compactification, with refinement comparisons and
adjunction conjugation. The comparison cocycles are identities before evaluation;
their evaluations are the existing ordinary canonical compactification comparisons.
Source: Bhatt--Scholze 6.7.18; blueprint system construction, refinement step
(blueprint: lem-per-finite-exceptional-system-adjunction). -/
structure Family {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] where
  support : ∀ c : Compactification f, Support l E c
  PX : Evaluation l E X
  PY : Evaluation l E Y
  /-- The system evaluations are the endpoint evaluations carried by every
  compact-support record, so compactification choices cannot twist them. -/
  support_evaluation : ∀ c : Compactification f,
    PX = (support c).PX ∧ PY = (support c).PY
  finite : ∀ c : Compactification f, FiniteData l E c
  systems : ∀ c : Compactification f, SystemData l E PX PY (support c) (finite c)
    (support_evaluation c).1 (support_evaluation c).2
  leftComparison : ∀ c d : Compactification f,
    systemLeft l E PX PY (support c) (systems c).preserves ≅
      systemLeft l E PX PY (support d) (systems d).preserves
  left_id : ∀ c : Compactification f, leftComparison c c = Iso.refl _
  left_comp : ∀ c d e : Compactification f,
    leftComparison c d ≪≫ leftComparison d e = leftComparison c e
  left_evaluation : ∀ (c d : Compactification f) (n : ℕ)
    (M : (NormalizedCtf l E X PX).FullSubcategory),
    (eval l E Y PY n).map ((leftComparison c d).hom.app M) ≫
        ((systems d).leftEvaluation n).hom.app M =
      ((systems c).leftEvaluation n).hom.app M ≫
        (Etale.rightDerivedLowerShriekOfCompactificationIso (Coeff l E n) c d).hom.app
          ((eval l E X PX n).obj M)
  rightComparison : ∀ c d : Compactification f, (systems c).right ≅ (systems d).right
  right_counit : ∀ (c d : Compactification f)
    (M : (NormalizedCtf l E Y PY).FullSubcategory),
    (systemLeft l E PX PY (support d) (systems d).preserves).map
        ((rightComparison c d).hom.app M) ≫ (systems d).adjunction.counit.app M =
      (leftComparison c d).inv.app ((systems c).right.obj M) ≫
        (systems c).adjunction.counit.app M
  right_id : ∀ c : Compactification f, rightComparison c c = Iso.refl _
  right_comp : ∀ c d e : Compactification f,
    rightComparison c d ≪≫ rightComparison d e = rightComparison c e
  finiteRightComparison : ∀ (c d : Compactification f) (n : ℕ),
    (finite c).right n ≅ (finite d).right n
  finite_counit : ∀ (c d : Compactification f) (n : ℕ)
    (K : Etale.DerivedCategoryModule (Coeff l E n) Y),
    (F l E d n).map ((finiteRightComparison c d n).hom.app K) ≫
        ((finite d).adjunction n).counit.app K =
      (Etale.rightDerivedLowerShriekOfCompactificationIso (Coeff l E n) c d).inv.app
          (((finite c).right n).obj K) ≫ ((finite c).adjunction n).counit.app K
  right_evaluation : ∀ (c d : Compactification f) (n : ℕ)
    (M : (NormalizedCtf l E Y PY).FullSubcategory),
    (eval l E X PX n).map ((rightComparison c d).hom.app M) ≫
        ((systems d).rightEvaluation n).hom.app M =
      ((systems c).rightEvaluation n).hom.app M ≫
        (finiteRightComparison c d n).hom.app ((eval l E Y PY n).obj M)

/-- Finite exceptional adjunction on normalized coefficient systems over an arbitrary field.
Source: Bhatt--Scholze, Lemma 6.7.18, pp. 57--58; the system adjunction is the separate
agent-formulated construction in the blueprint lem-per-artin-gabber-affine-curve proof
(blueprint: lem-per-finite-exceptional-system-adjunction).

Proof plan:
1. The coefficient valuation ring is a DVR with finite residue field. Its positive
quotients are finite and killed by a power of l, which is invertible over k.
Finite-type k-schemes and the compactification schemes are Noetherian.
2. Form simultaneous proper direct image after exact open extension on strict systems.
Evaluation computes ordinary compact support. It preserves coproducts componentwise;
Brown representability gives an ambient right adjoint with both triangle identities.
3. Scalar adjunction transposes the proper/open scalar unit to the canonical projection
comparison. The projection formula and open tensor comparison make it invertible.
K-flat tensor reassociation gives identity and quotient-cocycle equations.
4. Finite compact-support finiteness, bounded flat constructible models and the residue
Tor test show that compact support and coefficient reduction preserve Ctf.
5. Restrict the ordinary ambient exceptional right adjoint. Its scalar action comes by
transposition, and its unique adjunction-compatible shift structure makes it exact.
The exceptional coefficient arrow is the counit transpose of the inverse projection.
6. Normalize affine-space adjunctions using the projective-line decomposition: the
Kummer class and the unit commute with coefficient extension, hence so does the trace.
The ordered coordinate composite gives the affine-space counit, including dimension zero.
7. Affine-space exceptional pullback is pullback, Tate twist and shift. Flat models
show Ctf preservation and identify its coefficient comparison with the specified mate.
8. For a closed immersion use the finite cohomological dimension and constructibility
of the open complement. The closed Tor theorem gives a finite output Tor interval.
9. Compare the closed support triangles after coefficient reduction. The proper and
open coefficient comparisons identify the actual first map with the exceptional mate
by the counit equation. Two invertible maps in the triangle imply its invertibility.
10. A finite affine-chart factorization into closed immersion and affine-space projection
proves preservation and invertibility locally. Finite-cover descent supplies intervals
at each level; the empty source gives the zero object.
11. Mate pasting recomposes the specified local coefficient maps. Transposing both
composites proves identity, cocycle and unit/counit equations; uniqueness gives shifts.
12. Left extension from a coefficient level intertwines simultaneous compact support
with finite compact support. This follows by its scalar-unit transpose at every level.
The compatible truncation maps are identities before evaluation.
13. Apply the left-extension/evaluation and compact-support/exceptional Hom bijections.
Yoneda identifies evaluation of the ambient system adjoint with the finite adjoint,
including units and counits. Precomposition with truncation computes actual transitions.
14. Invertibility of the finite mates and input reductions proves normalization of the
output. Restrict the ambient adjunction to the full normalized Ctf subcategories.
Its triangles hold there before evaluation, its scalar transpose makes it R-linear,
and its adjunction-compatible shift makes it exact. No level-independent bound is used.
15. Proper/open adjunction words construct refinement comparisons on systems.
Mate pasting proves their cocycle before evaluation; their components are the ordinary
canonical comparisons. Conjugating adjunctions gives the counit-preserving right
comparisons and their cocycle, compatible with evaluation. No inverse limit is taken. -/
theorem finiteExceptionalSystemAdjunction
    (k : Type u) [Field k] (_hl : IsUnit (l : k))
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    Nonempty (Family l E f) := by
  sorry

end FiniteExceptionalSystems
end AlgebraicGeometry
