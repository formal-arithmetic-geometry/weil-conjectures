/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityNormalizedTowers
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod

public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
/-!
# The reduction tower is normalized

Source: blueprint main-20261015, sec-smooth-purity,
`sk-def-sp-normalized-towers/sk-def-sp-normalized-towers-reduction.md`
(blueprint: det-sp-reduction-tower-normalized).

The source is the sectionwise realization of the pulled-back condensed integer ring.
Its comparison with the completed ring is fixed on the underlying abelian sheaf by
`sfb_integral_coefficient_limit`. Positive exponent n+1 is represented by n : ℕ.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false

universe u

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

/-- The existing condensed integral coefficients, as an abelian sheaf on the point.
Source: blueprint, completed integral coefficients
(blueprint: det-sp-reduction-tower-normalized). -/
abbrev spIntegralCondensed := (sfbCondensedIntegers l E).X

/-- Commutativity of the continuous-function integral coefficients, with their existing
ring-object structure. Source: blueprint, integral coefficients
(blueprint: det-sp-reduction-tower-normalized). -/
instance spIntegralCondensedComm : IsCommMonObj (spIntegralCondensed l E) :=
  letI := spectralNorm.normedField (Padic l) E
  Profinite.isCommMonObj_continuousMapRingObjOfUniverse
    (Padic.coefficientExtensionIntegers l E)

/-- The section-ring realization of the actual pulled-back integral coefficient sheaf.
Source: blueprint, R_T; Stacks 00YV
(blueprint: det-sp-reduction-tower-normalized). -/
abbrev spIntegralSectionRing :=
  InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology T)
    (condensedRingObj (spIntegralCondensed l E) T)

/-- Modules over R_T, using the recorded sectionwise/internal equivalence.
Source: blueprint, ordinary unbounded derived source
(blueprint: det-sp-reduction-tower-normalized). -/
abbrev spIntegralSectionModules :=
  ringedSiteModules.{u + 1}
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (spIntegralSectionRing l E T))

/-- The standard localization of integral section-module complexes.
Source: blueprint, D(R_T) (blueprint: det-sp-reduction-tower-normalized). -/
instance spIntegralSectionHasDerived : HasDerivedCategory (spIntegralSectionModules l E T) :=
  HasDerivedCategory.standard _

/-- The recorded equivalence, with unchanged underlying sections and linear maps.
Source: blueprint, identification of coefficient-module presentations; Stacks 00YV
(blueprint: det-sp-reduction-tower-normalized). -/
abbrev spIntegralModuleEquivalence :=
  InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} (Scheme.ProEt.topology T)
    (condensedRingObj (spIntegralCondensed l E) T)

/-- The exact inverse equivalence on ordinary unbounded derived categories.
Source: blueprint, Dbc and Tor amplitude over the pulled-back integral ring
(blueprint: det-sp-reduction-tower-normalized). -/
def spIntegralInternalization :
    DerivedCategory (spIntegralSectionModules l E T) ⥤
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (spIntegralCondensed l E) T)) :=
  letI := Functor.additive_of_preserves_binary_products
    (spIntegralModuleEquivalence l E T).inverse
  (spIntegralModuleEquivalence l E T).inverse.mapDerivedCategory

/-- The canonical integral comparison selected by its projection normalization on
profinite test objects. The existence theorem determines this object uniquely after
its finite-label representation is chosen; it is not a choice of an arbitrary map.
Source: blueprint, completed integral sheaf; integral-limit clause (3)
(blueprint: det-sp-reduction-tower-normalized). -/
def spIntegralAbComparison :
    (condensedRingObj (spIntegralCondensed l E) T) ≅ sfbCompletedIntegersAb l E T :=
  (sfb_integral_coefficient_limit l E T).choose_spec.choose_spec.choose_spec.2.2.2.2.2.choose

/-- The canonical ell-power projection, retaining the commutative ring structure.
Source: blueprint, R_T -> R_(T,n+1), coefficient-limit normalization
(blueprint: det-sp-reduction-tower-normalized). -/
def spIntegralEllProjection (n : ℕ) :
    WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T ⟶
      (spCoefficientCommRings l E T).obj (op n) :=
  (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).preimage
    ((sp_completed_coefficient_limit l E T).exists.choose.hom ≫
      limit.π (spCoefficientRings l E T) (op n))

/-- The actual scalar map defining M/ell^(n+1), in the section-ring presentation.
Source: blueprint, derived reduction formula
(blueprint: det-sp-reduction-tower-normalized). -/
abbrev spIntegralReductionScalar
    (e : spIntegralSectionRing l E T ≅
      WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T) (n : ℕ) :=
  e.hom ≫ spIntegralEllProjection l E T n

/-- The ordinary localization of strict tower complexes in the localization chosen
by the recorded coefficient-tower lemma.
Source: blueprint, D(Tow) (blueprint: det-sp-reduction-tower-normalized). -/
abbrev spTowerLocalization (D : SpCoefficientTowersAbelian l E T) :
    CochainComplex (spCoefficientTowers l E T) ℤ ⥤ spDerivedCoefficientTowers l E T D :=
  @DerivedCategory.Q (spCoefficientTowers l E T) _ _ D.hasDerived

/-- The level condition of the canonical reduction construction.
Source: blueprint, normalized-towers-reduction
(blueprint: det-sp-reduction-tower-normalized). -/
def spReductionOrdinaryLevels (D : SpCoefficientTowersAbelian l E T)
    (coefficient : spIntegralSectionRing l E T ≅
      WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T)
    (ordinary : spIntegralSectionModules l E T ⥤ spCoefficientTowers l E T) :=
  ∀ n : ℕ, ordinary ⋙ spCoefficientEvaluation l E T D.equivalence n ≅
    (D.scalar (spIntegralReductionScalar l E T coefficient n)).model.E

/-- The local tensor generator transported to the strict ordinary reduction tower.
Naming this map keeps the kernel from repeatedly comparing the sectionwise scalar-model
presentations in the transition predicate. It is the same scalar-first pure tensor.
Source: blueprint, quotient-induced transition formula
(blueprint: det-sp-reduction-tower-normalized). -/
def spReductionGenerator (D : SpCoefficientTowersAbelian l E T)
    (coefficient : spIntegralSectionRing l E T ≅
      WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T)
    (ordinary : spIntegralSectionModules l E T ⥤ spCoefficientTowers l E T)
    (level : spReductionOrdinaryLevels l E T D coefficient ordinary)
    (M : spIntegralSectionModules l E T) (n : ℕ) (U : T.ProEtᵒᵖ)
    (c : ((spCoefficientCommRings l E T).obj (op n)).obj.obj U)
    (x : M.val.obj U) :
    ((D.equivalence.functor.obj (ordinary.obj M)).level n).val.obj U :=
  ((level n).inv.app M).val.app U
    (systemModelTmul (D.scalar
      (spIntegralReductionScalar l E T coefficient n)).model M U c x)

/-- The section function of the actual strict transition, after forgetting restriction
of scalars. Its underlying additive sections are unchanged. Keeping the ring tower
abstract here avoids unfolding its concrete constant quotient rings in kernel conversion.
Source: blueprint, quotient-induced transitions
(blueprint: det-sp-reduction-tower-normalized). -/
def spStrictTransitionSection
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (C : StrictRingSystem.{u + 1, u, u + 1} B) {m n : ℕ} (h : m ≤ n)
    (U : T.ProEtᵒᵖ) (x : (C.level n).val.obj U) : (C.level m).val.obj U :=
  (C.transition h).val.app U x

/-- The transition condition of the canonical reduction construction.
Source: blueprint, normalized-towers-reduction
(blueprint: det-sp-reduction-tower-normalized). -/
def IsSpReductionTransition (D : SpCoefficientTowersAbelian l E T)
    (coefficient : spIntegralSectionRing l E T ≅
      WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T)
    (ordinary : spIntegralSectionModules l E T ⥤ spCoefficientTowers l E T)
    (level : spReductionOrdinaryLevels l E T D coefficient ordinary) : Prop :=
  ∀ (M : spIntegralSectionModules l E T) {m n : ℕ} (h : m ≤ n)
    (U : T.ProEtᵒᵖ) (c : ((spCoefficientCommRings l E T).obj (op n)).obj.obj U)
    (x : M.val.obj U),
    spStrictTransitionSection T (spCoefficientCommRings l E T)
      (D.equivalence.functor.obj (ordinary.obj M)) h U
      (spReductionGenerator l E T D coefficient ordinary level M n U c x) =
    spReductionGenerator l E T D coefficient ordinary level M m U
      (((spCoefficientCommRings l E T).map (homOfLE h).op).hom.app U c) x

/-- The evaluation condition of the canonical reduction construction.
Source: blueprint, normalized-towers-reduction
(blueprint: det-sp-reduction-tower-normalized). -/
def spReductionDerivedEvaluations (D : SpCoefficientTowersAbelian l E T)
    (coefficient : spIntegralSectionRing l E T ≅
      WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T)
    (red : DerivedCategory (spIntegralSectionModules l E T) ⥤
      spDerivedCoefficientTowers l E T D) :=
  ∀ n : ℕ, red ⋙ spDerivedCoefficientEvaluation l E T D n ≅
    (D.scalar (spIntegralReductionScalar l E T coefficient n)).model.T

/-- Evaluation retains the canonical comparison on K-flat representatives. In particular,
the level identifications cannot be rescaled independently.
Source: blueprint, construction by K-flat descent
(blueprint: def-sp-reduction-tower-data). -/
def IsSpReductionEvaluationNormalized (D : SpCoefficientTowersAbelian l E T)
    (coefficient : spIntegralSectionRing l E T ≅
      WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T)
    (ordinary : spIntegralSectionModules l E T ⥤ spCoefficientTowers l E T)
    [ordinary.Additive]
    (level : spReductionOrdinaryLevels l E T D coefficient ordinary)
    (red : DerivedCategory (spIntegralSectionModules l E T) ⥤
      spDerivedCoefficientTowers l E T D)
    (counit : DerivedCategory.Q ⋙ red ⟶
      ordinary.mapHomologicalComplex (.up ℤ) ⋙ spTowerLocalization l E T D)
    (evaluation : spReductionDerivedEvaluations l E T D coefficient red) : Prop :=
  ∀ n : ℕ,
    letI := D.hasDerived
    letI := D.equivalenceAdditive
    letI := D.evaluationLimits n
    letI := D.evaluationColimits n
    letI : (spCoefficientEvaluation l E T D.equivalence n).Additive :=
      Functor.additive_of_preserves_binary_products _
    ∀ P : CochainComplex (spIntegralSectionModules l E T) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (R := spIntegralSectionRing l E T) P →
      (evaluation n).hom.app (DerivedCategory.Q.obj P) ≫
          (D.scalar (spIntegralReductionScalar l E T coefficient n)).model.ε.app P =
        (spDerivedCoefficientEvaluation l E T D n).map (counit.app P) ≫
          (spCoefficientEvaluation l E T D.equivalence n).mapDerivedCategoryFactors.hom.app
            ((ordinary.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex (level n) (.up ℤ)).hom.app P)

/-- The constructible condition of the canonical reduction construction.
Source: blueprint, normalized-towers-reduction
(blueprint: det-sp-reduction-tower-normalized). -/
def IsSpReductionConstructible (D : SpCoefficientTowersAbelian l E T)
    (red : DerivedCategory (spIntegralSectionModules l E T) ⥤
      spDerivedCoefficientTowers l E T D) : Prop :=
  CompactSpace T → QuasiSeparatedSpace T →
    ∀ M : DerivedCategory (spIntegralSectionModules l E T),
      constantModelBoundedConstructible (spIntegralCondensed l E) T
        ((spIntegralInternalization l E T).obj M) →
      DerivedCategory.finiteTorAmplitude _ ((spIntegralInternalization l E T).obj M) ∧
      spNormalizedConstructibleTorTowers l E T D (red.obj M) ∧
      ∀ (a b : ℤ), a ≤ b →
        DerivedCategory.torAmplitudeIn _ a b ((spIntegralInternalization l E T).obj M) →
        ∀ n : ℕ,
          Scheme.HasProEtaleTorAmplitude T
            (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n + 1))
            ((spDerivedCoefficientEvaluation l E T D n).obj (red.obj M)) a b ∧
          ∀ i : ℤ, (i < a ∨ b < i) → IsZero
            ((@DerivedCategory.homologyFunctor
              (Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T
                (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n + 1))))
              _ _ (HasDerivedCategory.standard _) i).obj
              ((spDerivedCoefficientEvaluation l E T D n).obj (red.obj M)))

/-- The reduction construction and its assertions. The ordinary functor is fixed by
its level tensor identifications and by its quotient formula on local tensor generators.
The derived functor is its universal left derived functor, computing on K-flat complexes.
This specifies a strict object of D(Tow), rather than only an inverse system in D(R_T).
Source: blueprint, construction, normalization, and final Tor-bound sentence
(blueprint: det-sp-reduction-tower-normalized). -/
structure SpReductionTower (D : SpCoefficientTowersAbelian l E T) where
  /-- The integral ring identification, with its underlying sheaf map fixed below. -/
  coefficient : spIntegralSectionRing l E T ≅
    WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T
  /-- It is precisely the canonical pulled-back/completed coefficient comparison. -/
  coefficient_normalized : ∀ (U : T.ProEtᵒᵖ)
    (x : (condensedRingObj (spIntegralCondensed l E) T).obj.obj U),
    coefficient.hom.hom.app U x = (spIntegralAbComparison l E T).hom.hom.app U x
  /-- Degreewise reduction, with genuine module-sheaf tower values. -/
  ordinary : spIntegralSectionModules l E T ⥤ spCoefficientTowers l E T
  /-- The ordinary reduction functor is additive. -/
  [additive : ordinary.Additive]
  /-- At every positive level it is the existing sheafified scalar extension. -/
  level : spReductionOrdinaryLevels l E T D coefficient ordinary

  /-- The strict transition is induced by the quotient of coefficients, on every
  local tensor generator; tensor generation and sheafification determine the map. -/
  transition : IsSpReductionTransition l E T D coefficient ordinary level

  /-- Functorial reduction on the ordinary unbounded derived categories. -/
  red : DerivedCategory (spIntegralSectionModules l E T) ⥤
    spDerivedCoefficientTowers l E T D
  /-- The universal comparison to degreewise reduction. -/
  counit : DerivedCategory.Q ⋙ red ⟶
    ordinary.mapHomologicalComplex (.up ℤ) ⋙ spTowerLocalization l E T D
  /-- Localization makes this the derived reduction of the specified strict functor. -/
  universal : red.IsLeftDerivedFunctor counit
    (HomologicalComplex.quasiIso (spIntegralSectionModules l E T) (.up ℤ))
  /-- K-flat representatives compute the strict reduction tower. -/
  computes : ∀ P : CochainComplex (spIntegralSectionModules l E T) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (R := spIntegralSectionRing l E T) P →
      IsIso (counit.app P)
  /-- The evaluated functors are exactly derived extension to the quotient coefficients. -/
  evaluation : spReductionDerivedEvaluations l E T D coefficient red
  /-- These are the comparisons descended from the specified ordinary tensor levels. -/
  evaluation_normalized : IsSpReductionEvaluationNormalized l E T D coefficient ordinary
    level red counit evaluation

  /-- Every actual transition-adjoint reduction map is an isomorphism, without qcqs. -/
  normalized : ∀ M : DerivedCategory (spIntegralSectionModules l E T),
    IsSpNormalizedTower l E T D (red.obj M)
  /-- On qcqs schemes bounded constructible integral objects give normalized finite-Tor
  constructible towers and themselves have finite Tor amplitude. Every Tor interval of
  M bounds both Tor amplitude and cohomological support at every positive level. -/
  constructible : IsSpReductionConstructible l E T D red

/-- The K-flat normalization uniquely determines the derived evaluation comparisons.
Source: uniqueness of localization comparisons, Stacks Tag 06XN
(blueprint: def-sp-reduction-tower-data).

Proof: cancel the scalar computation counit on a K-flat representative. The two
normalization equations then give equal evaluation components. Resolve an arbitrary
complex by a K-flat complex; naturality and invertibility of its localized resolution
extend equality to that complex. Localization detects equality of natural transformations,
and extensionality of natural isomorphisms finishes the proof. -/
theorem SpReductionTower.evaluation_unique (D : SpCoefficientTowersAbelian l E T)
    (R : SpReductionTower l E T D)
    (evaluation : spReductionDerivedEvaluations l E T D R.coefficient R.red)
    (h : letI := R.additive
      IsSpReductionEvaluationNormalized l E T D R.coefficient R.ordinary
        R.level R.red R.counit evaluation) : evaluation = R.evaluation := by
  let := R.additive
  funext n
  apply Iso.ext
  let := D.hasDerived
  let := D.equivalenceAdditive
  let := D.evaluationLimits n
  let := D.evaluationColimits n
  let : (spCoefficientEvaluation l E T D.equivalence n).Additive :=
    Functor.additive_of_preserves_binary_products _
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (spIntegralSectionModules l E T) (.up ℤ))
  intro K
  obtain ⟨P, s, hP, _, hs, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := spIntegralSectionRing l E T) K
  have : QuasiIso s := hs
  have he : (evaluation n).hom.app (DerivedCategory.Q.obj P) =
      (R.evaluation n).hom.app (DerivedCategory.Q.obj P) := by
    have := (D.scalar (spIntegralReductionScalar l E T R.coefficient n)).model.computes P hP
    apply (cancel_mono
      ((D.scalar (spIntegralReductionScalar l E T R.coefficient n)).model.ε.app P)).1
    exact (h n P hP).trans (R.evaluation_normalized n P hP).symm
  apply (cancel_epi ((R.red ⋙ spDerivedCoefficientEvaluation l E T D n).map
    (DerivedCategory.Q.map s))).1
  rw [(evaluation n).hom.naturality, (R.evaluation n).hom.naturality, he]

end AlgebraicGeometry.ProEtale
