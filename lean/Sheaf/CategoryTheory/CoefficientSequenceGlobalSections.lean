/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.SystemRingedSequenceSite
public import Sheaf.CategoryTheory.SystemDerivedTransition
public import Sheaf.CategoryTheory.TowerDerivedEvaluationNormalization
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Sheaf.CategoryTheory.RingedToposMorphism
import Sheaf.CategoryTheory.KInjectiveTotalDerived
import Sheaf.CategoryTheory.RestrictionRingedToposModuleDirectImage
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.ProperBaseChange.SingletonSiteModuleComparison
import Sheaf.CategoryTheory.SmallModuleDiagramsGrothendieck
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective

/-! # Derived sections of strict coefficient sequences

Source: Stacks Project, Cohomology on Sites, Tags 0941 and 0D6E
(blueprint: lem-coef-sequence-global-sections-evaluation).
Natural number n denotes positive level n+1. All derived categories are unbounded.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe u v w a av b bv dA dD
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]

/-- The recorded module category at one coefficient ring.
Source: Stacks 03DA (blueprint: lem-coef-sequence-global-sections-evaluation). -/
abbrev sequenceCoefficientModules (R : Sheaf J CommRingCat.{w}) :=
  ringedSiteModules.{w} (derivedChangeRingIndependentCoefficients J R)

/-- Actual scalar restriction at one coefficient map.
Source: Stacks 03CZ (blueprint: lem-coef-sequence-global-sections-evaluation). -/
abbrev sequenceCoefficientRestriction {R S : Sheaf J CommRingCat.{w}} (f : R ⟶ S) :=
  restrictScalars.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map f)

/-- Limits indexed by the essentially small site exist in the coefficient universe.
Source: Stacks 01FT (blueprint: lem-coef-sequence-global-sections-evaluation). -/
instance sequenceAbSiteLimits : HasLimitsOfShape Cᵒᵖ AddCommGrpCat.{w} :=
  hasLimitsOfShape_of_essentiallySmall _ _

/-- Global sections are the limit of the underlying abelian presheaf, including maps.
Source: Stacks 01FT (blueprint: lem-coef-sequence-global-sections-evaluation). -/
def sequenceCoefficientSections (R : Sheaf J CommRingCat.{w}) :
    sequenceCoefficientModules R ⥤ AddCommGrpCat.{w} :=
  toSheaf (derivedChangeRingIndependentCoefficients J R) ⋙
    sheafToPresheaf J AddCommGrpCat.{w} ⋙ lim

/-- Global sections preserve addition, as a finite-product-preserving functor.
Source: Stacks 01FT (blueprint: lem-coef-sequence-global-sections-evaluation). -/
instance sequenceCoefficientSectionsAdditive (R : Sheaf J CommRingCat.{w}) :
    (sequenceCoefficientSections R).Additive :=
  by
    dsimp only [sequenceCoefficientSections]
    exact Functor.additive_of_preserves_binary_products _

/-- Termwise global sections retain every actual tower arrow.
Source: Stacks 0941 (blueprint: lem-coef-sequence-global-sections-evaluation). -/
def sequenceTowerSections (A : Sheaf J CommRingCat.{w}) :
    (ℕᵒᵖ ⥤ sequenceCoefficientModules A) ⥤ (ℕᵒᵖ ⥤ AddCommGrpCat.{w}) :=
  (Functor.whiskeringRight _ _ _).obj (sequenceCoefficientSections A)

/-- Standard localization for constant-coefficient towers.
Source: Stacks 05RU (blueprint: lem-coef-sequence-global-sections-evaluation). -/
instance sequenceConstantTowerHasDerived (A : Sheaf J CommRingCat.{w}) :
    HasDerivedCategory (ℕᵒᵖ ⥤ sequenceCoefficientModules A) :=
  HasDerivedCategory.standard _

/-- Standard localization for the abelian target.
Source: Stacks 05RU (blueprint: lem-coef-sequence-global-sections-evaluation). -/
instance sequenceAbHasDerived : HasDerivedCategory AddCommGrpCat.{w} :=
  HasDerivedCategory.standard _

/-- Standard localization for the strict abelian tower target.
Source: Stacks 05RU (blueprint: lem-coef-sequence-global-sections-evaluation). -/
instance sequenceAbTowerHasDerived : HasDerivedCategory (ℕᵒᵖ ⥤ AddCommGrpCat.{w}) :=
  HasDerivedCategory.standard _

/-- A total right derived pair, with its universal unit and K-injective computation.
Source: Stacks 070I, 070Y (blueprint: lem-coef-sequence-global-sections-evaluation). -/
structure SequenceSectionsDerivedPair
    {A : Type a} [Category.{av} A] [Abelian A] [HasDerivedCategory.{dA} A]
    {D : Type b} [Category.{bv} D] [Abelian D] [HasDerivedCategory.{dD} D]
    (F : A ⥤ D) [F.Additive] where
  functor : DerivedCategory A ⥤ DerivedCategory D
  unit : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
    DerivedCategory.Q ⋙ functor
  universal : functor.IsRightDerivedFunctor unit (HomologicalComplex.quasiIso A (.up ℤ))
  computes : ∀ I : CochainComplex A ℤ, I.IsKInjective → IsIso (unit.app I)

/-- The exact termwise restriction, specified on objects, maps and all transitions.
These equations determine the functor, rather than supplying an arbitrary exact map.
Source: Stacks 03CZ, 0941 (blueprint: lem-coef-sequence-global-sections-evaluation). -/
structure SequenceCoefficientRestrictionData
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (A : Sheaf J CommRingCat.{w})
    (α : (Functor.const ℕᵒᵖ).obj A ⟶ B) where
  functor : StrictRingSystem B ⥤ (ℕᵒᵖ ⥤ sequenceCoefficientModules A)
  additive : functor.Additive
  limits : PreservesFiniteLimits functor
  colimits : PreservesFiniteColimits functor
  evaluation : ∀ n : ℕ, functor ⋙ (CategoryTheory.evaluation ℕᵒᵖ _).obj (op n) ≅
    systemEvaluation B n ⋙ sequenceCoefficientRestriction (α.app (op n))
  evaluation_sections : ∀ (n : ℕ) (M : StrictRingSystem B) (V : Cᵒᵖ)
    (x : ((functor.obj M).obj (op n)).val.obj V),
    HEq (((evaluation n).hom.app M).val.app V x) x
  transitions : ∀ (M : StrictRingSystem B) {m n : ℕ} (h : m ≤ n) (V : Cᵒᵖ)
    (x : ((functor.obj M).obj (op n)).val.obj V),
    HEq (((evaluation m).hom.app M).val.app V
      (((functor.obj M).map (homOfLE h).op).val.app V x))
      ((M.transition h).val.app V (((evaluation n).hom.app M).val.app V x))

/-- The given exact restriction has its specified additive structure.
Source: Stacks 03CZ (blueprint: lem-coef-sequence-global-sections-evaluation). -/
instance sequenceRestrictionAdditive
    {B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} {A : Sheaf J CommRingCat.{w}}
    {α : (Functor.const ℕᵒᵖ).obj A ⟶ B} (r : SequenceCoefficientRestrictionData B A α) :
    r.functor.Additive := r.additive

/-- The given restriction preserves finite limits.
Source: Stacks 03CZ (blueprint: lem-coef-sequence-global-sections-evaluation). -/
instance sequenceRestrictionLimits
    {B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} {A : Sheaf J CommRingCat.{w}}
    {α : (Functor.const ℕᵒᵖ).obj A ⟶ B} (r : SequenceCoefficientRestrictionData B A α) :
    PreservesFiniteLimits r.functor := r.limits

/-- The given restriction preserves finite colimits.
Source: Stacks 03CZ (blueprint: lem-coef-sequence-global-sections-evaluation). -/
instance sequenceRestrictionColimits
    {B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} {A : Sheaf J CommRingCat.{w}}
    {α : (Functor.const ℕᵒᵖ).obj A ⟶ B} (r : SequenceCoefficientRestrictionData B A α) :
    PreservesFiniteColimits r.functor := r.colimits

/-- Termwise sections preserve addition.
Source: Stacks 0941 (blueprint: lem-coef-sequence-global-sections-evaluation). -/
instance sequenceTowerSectionsAdditive (A : Sheaf J CommRingCat.{w}) :
    (sequenceTowerSections A).Additive := by
  dsimp only [sequenceTowerSections]
  infer_instance

/-- The evaluation comparison for exact restriction is its localized ordinary comparison.
Source: Stacks 015F (blueprint: lem-coef-sequence-global-sections-evaluation). -/
def sequenceRestrictionDerivedEvaluation
    {B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} {A : Sheaf J CommRingCat.{w}}
    {α : (Functor.const ℕᵒᵖ).obj A ⟶ B} (r : SequenceCoefficientRestrictionData B A α)
    (n : ℕ) :
    r.functor.mapDerivedCategory ⋙
        ((CategoryTheory.evaluation ℕᵒᵖ (sequenceCoefficientModules A)).obj
          (op n)).mapDerivedCategory ≅
      derivedSystemEvaluation B n ⋙
        (sequenceCoefficientRestriction (α.app (op n))).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso r.functor
    ((CategoryTheory.evaluation ℕᵒᵖ _).obj (op n))).symm ≪≫
    Functor.mapDerivedCategoryNatIso (r.evaluation n) ≪≫
    Functor.mapDerivedCategoryCompIso (systemEvaluation B n)
      (sequenceCoefficientRestriction (α.app (op n)))

/-- The two finite comparisons, with the actual total derived functors as their endpoints.
Source: Stacks 0941, 0D6E (blueprint: lem-coef-sequence-global-sections-evaluation). -/
structure SequenceSectionsComparisons
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (A : Sheaf J CommRingCat.{w})
    (α : (Functor.const ℕᵒᵖ).obj A ⟶ B) where
  restriction : SequenceCoefficientRestrictionData B A α
  finite : ∀ R : Sheaf J CommRingCat.{w},
    SequenceSectionsDerivedPair (sequenceCoefficientSections R)
  tower : SequenceSectionsDerivedPair (sequenceTowerSections A)
  evaluation : ∀ n : ℕ, tower.functor ⋙
      ((CategoryTheory.evaluation ℕᵒᵖ AddCommGrpCat.{w}).obj (op n)).mapDerivedCategory ≅
    ((CategoryTheory.evaluation ℕᵒᵖ (sequenceCoefficientModules A)).obj
      (op n)).mapDerivedCategory ⋙ (finite A).functor
  scalar : ∀ {R S : Sheaf J CommRingCat.{w}} (f : R ⟶ S),
    (finite S).functor ≅
      (sequenceCoefficientRestriction f).mapDerivedCategory ⋙ (finite R).functor

/-- G is a composite of actual functors on ordinary derived categories.
Source: Stacks 0941, 0D6E (blueprint: lem-coef-sequence-global-sections-evaluation). -/
def SequenceSectionsComparisons.global
    {B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} {A : Sheaf J CommRingCat.{w}}
    {α : (Functor.const ℕᵒᵖ).obj A ⟶ B} (d : SequenceSectionsComparisons B A α) :
    DerivedCategory (StrictRingSystem B) ⥤ DerivedCategory (ℕᵒᵖ ⥤ AddCommGrpCat.{w}) :=
  d.restriction.functor.mapDerivedCategory ⋙ d.tower.functor

/-- The first comparison: restrict scalars exactly, then evaluate the same tower resolution.
Source: Stacks 0941 (blueprint: lem-coef-sequence-global-sections-evaluation). -/
def SequenceSectionsComparisons.restrictedEvaluation
    {B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} {A : Sheaf J CommRingCat.{w}}
    {α : (Functor.const ℕᵒᵖ).obj A ⟶ B} (d : SequenceSectionsComparisons B A α) (n : ℕ) :
    d.global ⋙ ((CategoryTheory.evaluation ℕᵒᵖ AddCommGrpCat.{w}).obj
        (op n)).mapDerivedCategory ≅
      derivedSystemEvaluation B n ⋙
        (sequenceCoefficientRestriction (α.app (op n))).mapDerivedCategory ⋙
          (d.finite A).functor :=
  Functor.isoWhiskerLeft d.restriction.functor.mapDerivedCategory (d.evaluation n) ≪≫
    Functor.isoWhiskerRight (sequenceRestrictionDerivedEvaluation d.restriction n)
      (d.finite A).functor

/-- The second comparison is the inverse of the normalized scalar composition comparison.
Source: Stacks 0D6E (blueprint: lem-coef-sequence-global-sections-evaluation). -/
def SequenceSectionsComparisons.finiteEvaluation
    {B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} {A : Sheaf J CommRingCat.{w}}
    {α : (Functor.const ℕᵒᵖ).obj A ⟶ B} (d : SequenceSectionsComparisons B A α) (n : ℕ) :
    d.global ⋙ ((CategoryTheory.evaluation ℕᵒᵖ AddCommGrpCat.{w}).obj
        (op n)).mapDerivedCategory ≅
      derivedSystemEvaluation B n ⋙ (d.finite (B.obj (op n))).functor :=
  d.restrictedEvaluation n ≪≫
    Functor.isoWhiskerLeft (derivedSystemEvaluation B n) (d.scalar (α.app (op n))).symm

/-- Normalization by derived units and compatibility with every actual transition.
No condition on K-injectivity of varying-coefficient evaluations occurs here.
Source: Stacks 0941, 0D6E (blueprint: lem-coef-sequence-global-sections-evaluation). -/
structure SequenceSectionsComparisons.Normalized
    {B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} {A : Sheaf J CommRingCat.{w}}
    {α : (Functor.const ℕᵒᵖ).obj A ⟶ B} (d : SequenceSectionsComparisons B A α) : Prop where
  /-- The first comparison evaluates precisely the unit on the same K-injective tower. -/
  evaluation_unit : ∀ (n : ℕ)
    (I : CochainComplex (ℕᵒᵖ ⥤ sequenceCoefficientModules A) ℤ), I.IsKInjective →
    ((CategoryTheory.evaluation ℕᵒᵖ AddCommGrpCat.{w}).obj (op n)).mapDerivedCategoryFactors.inv.app
        (((sequenceTowerSections A).mapHomologicalComplex (.up ℤ)).obj I) ≫
      ((CategoryTheory.evaluation ℕᵒᵖ AddCommGrpCat.{w}).obj (op n)).mapDerivedCategory.map
        (d.tower.unit.app I) ≫
      (d.evaluation n).hom.app (DerivedCategory.Q.obj I) ≫
      (d.finite A).functor.map
        (((CategoryTheory.evaluation ℕᵒᵖ (sequenceCoefficientModules A)).obj
          (op n)).mapDerivedCategoryFactors.hom.app I) =
      (d.finite A).unit.app
        ((((CategoryTheory.evaluation ℕᵒᵖ (sequenceCoefficientModules A)).obj
          (op n)).mapHomologicalComplex (.up ℤ)).obj I)
  /-- The second comparison is the canonical derived direct-image composition map. -/
  scalar_unit : ∀ {R S : Sheaf J CommRingCat.{w}} (f : R ⟶ S)
    (K : CochainComplex (sequenceCoefficientModules S) ℤ),
    (d.finite S).unit.app K ≫ (d.scalar f).hom.app (DerivedCategory.Q.obj K) ≫
      (d.finite R).functor.map
        ((sequenceCoefficientRestriction f).mapDerivedCategoryFactors.hom.app K) =
    (d.finite R).unit.app
      (((sequenceCoefficientRestriction f).mapHomologicalComplex (.up ℤ)).obj K)
  /-- The evaluated tower comparison commutes with all constant-coefficient transitions. -/
  evaluation_transition : ∀ {m n : ℕ} (h : m ≤ n)
    (M : DerivedCategory (ℕᵒᵖ ⥤ sequenceCoefficientModules A)),
    (towerDerivedEvaluationTransition AddCommGrpCat.{w} (homOfLE h).op).app
        (d.tower.functor.obj M) ≫ (d.evaluation m).hom.app M =
      (d.evaluation n).hom.app M ≫ (d.finite A).functor.map
        ((towerDerivedEvaluationTransition (sequenceCoefficientModules A)
          (homOfLE h).op).app M)
  /-- Under both comparisons, the actual strict tower arrow is the derived-sections arrow
  of the original semilinear transition, followed by inverse scalar composition. -/
  finite_transition : ∀ {m n : ℕ} (h : m ≤ n) (M : DerivedCategory (StrictRingSystem B)),
    (towerDerivedEvaluationTransition AddCommGrpCat.{w} (homOfLE h).op).app
        (d.global.obj M) ≫ (d.finiteEvaluation m).hom.app M =
      (d.finiteEvaluation n).hom.app M ≫
        (d.finite (B.obj (op n))).functor.map ((systemDerivedTransition B h).app M) ≫
        (d.scalar (B.map (homOfLE h).op)).inv.app ((derivedSystemEvaluation B m).obj M)

/-- Unbounded termwise derived global sections of strict coefficient systems exist,
with the two specified natural comparisons and their actual transition normalization.
Source: Stacks Project, Cohomology on Sites, Tags 0941 and 0D6E
(blueprint: lem-coef-sequence-global-sections-evaluation).

Proof plan:
1. Restriction changes only the scalar action, hence preserves sectionwise kernels and
   sheafified sectionwise cokernels (`def-weil-sheaf-of-modules-category`). Compatibility
   of α makes all transitions A-linear. Thus U⁰ is exact componentwise, and localizes to U
   (`lem-weil-tower-category-levelwise-abelian`,
   `lem-weil-pbc-exact-functor-derived-factorization`, `def-pc-sheaf-restrict-scalars`).
2. Constant-A towers form a Grothendieck category by
   `lem-weil-pbc-small-module-diagrams-grothendieck`. Apply
   `lem-weil-pbc-kinjective-functorial-existence` to get a simultaneous resolution.
   Individual coefficient categories have resolutions by `prop-pur-kinjective-resolutions-exist`.
   No cohomological bounds or exactness of infinite products are required.
3. Termwise sections are additive and preserve homotopies and mapping cones. Apply
   `lem-weil-pbc-kinjective-total-derived` to obtain the total derived pair on towers.
   Its composite with exact U is the actual functor G on the ordinary derived category.
4. A constant-A K-injective tower evaluates to K-injectives by
   `lem-weil-tower-evaluation-kinjective`. Its resolution maps evaluate to quasi-isomorphisms.
   The two derived units identify both evaluations with sections of the same resolution.
   `lem-weil-pbc-kinjective-hom-derived` gives naturality on derived morphisms; the same
   calculation on transition maps proves evaluation_transition.
5. Scalar restriction is the direct image of the identity ringed-topos morphism by
   `lem-weil-pbc-restriction-ringed-topos-module-direct-image`. Compose with the global-sections
   morphism to the singleton Z-ringed site (`def-weil-pbc-ringed-topos-morphism`,
   `def-weil-pbc-constant-sheaf`, `lem-weil-pbc-singleton-site-module-comparison`). The comparison
   of `lem-weil-pbc-ringed-topoi-derived-pushforward-composition` is invertible. Its unit equation
   is scalar_unit; uniqueness in `lem-weil-pbc-kinjective-total-derived` fixes this comparison.
6. For composable coefficient maps, both the direct scalar comparison and the composite
   scalar comparisons have the same derived-unit equation. Uniqueness makes them equal.
   The identity comparison is likewise the identity, with the canonical restriction identifications.
7. Naturality and this composition equality identify the derived-sections transition with
   the inverse scalar comparison after the sections map of J_n → Res J_m. Combining with
   Step 4 proves finite_transition. All comparisons are natural isomorphisms of functors,
   including identity and iterated transitions. No varying-ring evaluation is claimed to
   preserve K-injectives. -/
theorem coefficientSequenceGlobalSectionsEvaluation
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (A : Sheaf J CommRingCat.{w})
    (α : (Functor.const ℕᵒᵖ).obj A ⟶ B) :
    ∃ d : SequenceSectionsComparisons B A α, d.Normalized := by
  sorry

end SheafOfModules
