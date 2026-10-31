/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.CompletedPullbackTensorComparison
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorIso
public import WeilConjectures.AlgebraicGeometry.SemilinearDerivedSections
public import WeilConjectures.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage

import Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.AlgebraicGeometry.IsomorphismReductionTower
import WeilConjectures.AlgebraicGeometry.PurInverseImageTensorHom
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimitSupplement
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import WeilConjectures.SixFunctors.RingedDerivedMonoidalComparisons
public import WeilConjectures.AlgebraicGeometry.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
import WeilConjectures.AlgebraicGeometry.FiniteFreeCompletedScalarComparison
import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses
import WeilConjectures.Algebra.Homology.KFlatSupplement
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Evaluation
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import Mathlib.Algebra.BigOperators.Ring.Finset
public import WeilConjectures.AlgebraicGeometry.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorHom
import WeilConjectures.AlgebraicGeometry.PodReindexingHomCoefficientDescent
import WeilConjectures.AlgebraicGeometry.CompletedOperationTowerSubstitution
import WeilConjectures.AlgebraicGeometry.ConstantCompletionEquivalence
import WeilConjectures.AlgebraicGeometry.WeilCompletedTensorReflector
public import WeilConjectures.AlgebraicGeometry.SfRationalizationKaroubi
public import WeilConjectures.AlgebraicGeometry.GeneralAlgebraicallyClosedCoefficients
import WeilConjectures.AlgebraicGeometry.PurNormalizedReconstructionAdjunctionCalculus
import WeilConjectures.AlgebraicGeometry.SfDerivedCompleteLegacyComparison

import all WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorIso
import WeilConjectures.AlgebraicGeometry.CommonStageTensorBraidingNaturality
import all WeilConjectures.AlgebraicGeometry.PodReindexingEvaluationShiftComposition

public import WeilConjectures.AlgebraicGeometry.PodHomComplexShiftRepresentatives
public import WeilConjectures.AlgebraicGeometry.DerivedAutomorphismHomEvaluationContinuationA

/-! # Internal Hom and evaluation under coefficient-site isomorphisms

Source: Stacks Project, Modules on Sites, Tag 0GMX; the derived and completed
normalization is the enhancement in the node's sixteen proof steps, supplying
main-20261015 prop-pod-dual-tate-data-compatibility Steps 1, 2, 4 and 5.
(blueprint: lem-pod-derived-automorphism-hom-evaluation).

Finite inputs are unbounded. Integral inputs have exactly the recorded
Hom-constructibility condition. Completed inverse image is constructed from
all coefficient projections; its comparison with tower pullback uses the
actual completion unit and a resolution-normalized total-limit comparison.
System maps and their identities are stated before evaluation or realization.
Rational maps are localized; algebraically closed maps use every common stage.

## Main definitions

* `podFiniteHomComparison`: transpose of pullback of finite evaluation.
* `podPartialHomComparison`: the same construction on permitted Hom pairs.
* `podCompletedRingMap`: completed coefficient transport from all projections.
* `podCompletedToTower`: the completion-unit comparison with tower pullback.

## Main statements

* `derivedAutomorphismHomEvaluation`: the four evaluation-defined natural isomorphisms.
* The `*_laws`, `*_shift`, `*_comp` declarations give all coherent identities.
* `podHomReductionSquare`: the actual system-level reduction square.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v a b c d
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] AlgebraicGeometry.Scheme.residueField
  HasDerivedCategory.standard
attribute [-instance] isoReductionAbSheafify isoReductionAbBijective isoReductionSiteSmall

section ReductionNormalization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]

/-- The canonical reduction/reindexing map: the actual reduction/limit adjunct
of exact inverse image of the unit, followed by the inverse limit comparison.
Source: node proof steps 8 and 13
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podReductionReindexingMap (K : DerivedCategory (integralTowerModules l E Y)) :
    (pullbackTensorCalculus l E X).reduction.obj
        ((podCompletedDerivedInverseImage l E g).obj K) ⟶
      (pullbackTensorSequenceDerived l E g).obj
        ((pullbackTensorCalculus l E Y).reduction.obj K) :=
  ((pullbackTensorCalculus l E X).adjunction.homEquiv _ _).symm
    ((podCompletedDerivedInverseImage l E g).map
        ((pullbackTensorCalculus l E Y).adjunction.unit.app K) ≫
      (podLimitReindexing l E g).inv.app ((pullbackTensorCalculus l E Y).reduction.obj K))

/-- The canonical reduction adjunct is invertible and natural for every ambient
complex, without asserting invertibility of the completion unit.
Source: node proof steps 8 and 13.
Proof: the two reduction functors are ordinary quotient systems on a flat-term
K-flat representative. Reindexing commutes with every quotient and strict
transition. Their identity-on-sections map is the displayed adjunct, by the
actual reduction unit and projection equations. Inverse reindexing gives an
inverse system map before localization. Naturality holds on representatives
and descends to every derived arrow.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podReductionReindexingMap_laws :
    (∀ K, IsIso (podReductionReindexingMap l E g K)) ∧
    ∀ (K L : DerivedCategory (integralTowerModules l E Y)) (f : K ⟶ L),
      (pullbackTensorCalculus l E X).reduction.map
          ((podCompletedDerivedInverseImage l E g).map f) ≫
        podReductionReindexingMap l E g L =
      podReductionReindexingMap l E g K ≫
        (pullbackTensorSequenceDerived l E g).map
          ((pullbackTensorCalculus l E Y).reduction.map f) := by
  sorry

/-- The reduction comparison is the isomorphism of that very canonical adjunct.
Source: node proof step 13 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podReductionReindexing (K : DerivedCategory (integralTowerModules l E Y)) :=
  @asIso _ _ _ _ (podReductionReindexingMap l E g K)
    ((podReductionReindexingMap_laws l E g).1 K)

/-- Exact inverse image to tower pullback: inverse image of the actual completion
unit, the inverse total-limit comparison, and the inverse recorded Roos model.
Source: node proof step 8 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podCompletedToTower (K : DerivedCategory (integralTowerModules l E Y)) :
    (podCompletedDerivedInverseImage l E g).obj K ⟶ (integralDerivedPullback l E g).obj K :=
  (podCompletedDerivedInverseImage l E g).map
      ((pullbackTensorCalculus l E Y).adjunction.unit.app K) ≫
    (podLimitReindexing l E g).inv.app ((pullbackTensorCalculus l E Y).reduction.obj K) ≫
    (pullbackTensorIntegralPullbackModel l E g).inv.app K

attribute [local irreducible] pullbackTensorCalculus
  podCompletedDerivedInverseImage integralDerivedPullback podLimitReindexing
  pullbackTensorIntegralPullbackModel completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence

/-- The identification with tower-defined pullback is natural, and is invertible
on exactly the complete constructible inputs used here.
Source: node proof step 8.
Proof: all three factors are natural. For a constructible complete K, the
canonical quotient-tower unit is invertible by the finite-free completed
scalar theorem for E/E. The other two factors are isomorphisms already.
The total-limit comparison's resolution and projection equations imply
commutation with every reduction projection.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podCompletedToTower_laws :
    (∀ (K L : DerivedCategory (integralTowerModules l E Y)) (f : K ⟶ L),
      (podCompletedDerivedInverseImage l E g).map f ≫ podCompletedToTower l E g L =
        podCompletedToTower l E g K ≫ (integralDerivedPullback l E g).map f) ∧
    (∀ K : sfIntegralConstructibleCategory l E Y, IsIso (podCompletedToTower l E g K.obj)) := by
  constructor
  · intro K L f
    let SY := pullbackTensorCalculus l E Y
    let F := podCompletedDerivedInverseImage l E g
    have hη := congrArg F.map (SY.adjunction.unit.naturality f)
    have hlim := (podLimitReindexing l E g).inv.naturality (SY.reduction.map f)
    have hrho := (pullbackTensorIntegralPullbackModel l E g).inv.naturality f
    dsimp only [Functor.comp_map, Functor.id_map] at hη hlim hrho
    simp only [Functor.map_comp] at hη
    dsimp only [podCompletedToTower]
    change F.map f ≫ F.map (SY.adjunction.unit.app L) ≫ _ ≫ _ = _
    rw [← Category.assoc (F.map f), hη]
    rw [Category.assoc, ← Category.assoc (F.map
      ((coefficientSequenceLimit l E Y).map (SY.reduction.map f))), hlim]
    simpa only [Category.assoc, pullbackTensorReferencePullback, Functor.comp_map] using
      congrArg (fun k ↦ F.map (SY.adjunction.unit.app K) ≫
        (podLimitReindexing l E g).inv.app (SY.reduction.obj K) ≫ k) hrho
  · intro K
    obtain ⟨p, hpl, hp⟩ := Nat.exists_infinite_primes (l + 1)
    let : Fact p.Prime := ⟨hp⟩
    let D : FiniteFieldDatum.{0} := {
      p := p, a := 1, q := p, prime := hp, exponent_pos := le_refl 1,
      cardinality_eq := (pow_one p).symm, k₀ := ZMod p,
      card_base := by simp [Nat.card_eq_fintype_card]
      k := AlgebraicClosure (ZMod p) }
    have hlp : l ≠ D.p := by change l ≠ p; omega
    have hK : IntegralOnSlice.IsComplete l E Y none K.obj :=
      ⟨D, hlp, (sfDerivedComplete_iff_legacy l E Y D hlp K.obj).mp K.property.1⟩
    have : IsIso ((pullbackTensorCalculus l E Y).adjunction.unit.app K.obj) :=
      (purNormalizedReconstructionOfScheme l E Y (pullbackTensorCalculus l E Y)).2 K.obj hK
    dsimp only [podCompletedToTower]
    infer_instance

/-- The canonical complete-input identification, retaining its specified map.
Source: node proof step 8 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podCompletedToTowerIso (K : sfIntegralConstructibleCategory l E Y) :=
  @asIso _ _ _ _ (podCompletedToTower l E g K.obj) ((podCompletedToTower_laws l E g).2 K)

variable [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

/-- The integral Hom comparison expressed through the exact completed-ring
inverse image, with the canonical complete-input identifications inserted.
Source: node proof steps 8, 11, 13
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podIntegralReindexedHom (P : (constructibleIntegralHomPairs l E Y).FullSubcategory) :
    (podCompletedDerivedInverseImage l E g).obj
        ((integralDerivedInternalHom l E Y).obj (op P.obj.1.unop.obj, P.obj.2.obj)) ⟶
      (integralDerivedInternalHom l E X).obj
        (op ((podCompletedDerivedInverseImage l E g).obj P.obj.1.unop.obj),
          (podCompletedDerivedInverseImage l E g).obj P.obj.2.obj) :=
  (podCompletedToTowerIso l E g ((constructibleIntegralHom l E Y).obj P)).hom ≫
    (podIntegralHomComparison l E g P).hom ≫
    (integralDerivedInternalHom l E X).map
      (Prod.mkHom (podCompletedToTowerIso l E g P.obj.1.unop).hom.op
        (podCompletedToTowerIso l E g P.obj.2).inv)

/-- The reduction/internal-Hom comparison square commutes as an actual derived
system square, hence also under the specified functorial total-limit realization.
Source: node proof step 13.
Proof: beta is the transpose of reduced evaluation on one simultaneous system
resolution. Reindexing carries that evaluation and its transpose to the same
chain map. The reduction/reindexing maps are its actual unit adjuncts, so
unit/counit identities identify the two composites before localization.
The normalized integral closed equation extends the same evaluation across
completion, giving the displayed top map. Apply the functorial total limit
to obtain the realized square and its evaluation/transposition identities.
This uses neither equality detection by evaluations nor invertibility of beta.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podHomReductionSquare
    (P : (constructibleIntegralHomPairs l E Y).FullSubcategory) :
    (pullbackTensorCalculus l E X).reduction.map (podIntegralReindexedHom l E g P) ≫
      coefficientBaseChangeHom (pullbackTensorCalculus l E X).integralClosed
        (pullbackTensorCalculus l E X).systemClosed
        (pullbackTensorCalculus l E X).reduction (pullbackTensorCalculus l E X).reductionTensor
        ((podCompletedDerivedInverseImage l E g).obj P.obj.1.unop.obj)
        ((podCompletedDerivedInverseImage l E g).obj P.obj.2.obj) =
    (podReductionReindexing l E g
      ((integralDerivedInternalHom l E Y).obj (op P.obj.1.unop.obj, P.obj.2.obj))).hom ≫
      (pullbackTensorSequenceDerived l E g).map
        (coefficientBaseChangeHom (pullbackTensorCalculus l E Y).integralClosed
          (pullbackTensorCalculus l E Y).systemClosed (pullbackTensorCalculus l E Y).reduction
          (pullbackTensorCalculus l E Y).reductionTensor P.obj.1.unop.obj P.obj.2.obj) ≫
      podSystemHomComparison l E g
        ((pullbackTensorCalculus l E Y).reduction.obj P.obj.1.unop.obj)
        ((pullbackTensorCalculus l E Y).reduction.obj P.obj.2.obj) ≫
      (coefficientSequenceInternalHom l E X).map
        (Prod.mkHom (podReductionReindexing l E g P.obj.1.unop.obj).hom.op
          (podReductionReindexing l E g P.obj.2.obj).inv) := by
  sorry
end ReductionNormalization

section SignedShifts
attribute [local irreducible] homComplexFunctor
universe r s t w
variable {C : Type s} [Category.{t} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max s t r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max s t r}]
  (A : Sheaf J CommRingCat.{max s t r})
  [HasDerivedCategory.{w} (PodModules.{r, s, t} J A)]

/-- The canonical cohomological shift identifications, with their precise
signed representative normalization; no universe equality is imposed.
Source: node proof step 6, Stacks 08JA.
Proof: localize the signed Hom-complex shift on K-injective targets and insert
its canonical representative comparisons. Shifts preserve K-injectives. The
formula is natural in both chain arguments and preserves homotopies, hence
descends to arbitrary derived arrows. Every object has such a representative,
so naturality and the representative equation determine the family uniquely.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podDerivedHomShift_existsUnique :
    ∃! σ : ∀ (M N : DerivedCategory (PodModules.{r, s, t} J A)) (m n : ℤ),
        ((derivedInternalHomOfUniverses.{s, t, r, w} J A).obj (op M, N))⟦n - m⟧ ≅
          (derivedInternalHomOfUniverses.{s, t, r, w} J A).obj (op (M⟦m⟧), N⟦n⟧),
      (∀ (M N M' N' : DerivedCategory (PodModules.{r, s, t} J A)) (m n : ℤ)
        (f : M' ⟶ M) (h : N ⟶ N'),
        ((derivedInternalHomOfUniverses.{s, t, r, w} J A).map (Prod.mkHom f.op h))⟦n - m⟧' ≫
            (σ M' N' m n).hom =
          (σ M N m n).hom ≫ (derivedInternalHomOfUniverses.{s, t, r, w} J A).map
            (Prod.mkHom (f⟦m⟧').op (h⟦n⟧'))) ∧
      ∀ (K I : CochainComplex (PodModules.{r, s, t} J A) ℤ) [I.IsKInjective] (m n : ℤ),
        (σ (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj I) m n).hom ≫
            (derivedInternalHomOfUniverses.{s, t, r, w} J A).map
              (Prod.mkHom ((DerivedCategory.Q.commShiftIso m).hom.app K).op
                ((DerivedCategory.Q.commShiftIso n).inv.app I)) ≫
            (podKInjectiveHomModel.{r, s, t, w} J A (K⟦m⟧) (I⟦n⟧)).hom =
          ((podKInjectiveHomModel.{r, s, t, w} J A K I).hom)⟦n - m⟧' ≫
            (DerivedCategory.Q.commShiftIso (n - m)).inv.app
              (homComplex.{s, t, max s t r, max s t r} (R := A) K I) ≫
            DerivedCategory.Q.map (podHomComplexShift.{r, s, t} J A K I m n).hom := by
  sorry

/-- The signed canonical shift comparison, fixed on representatives above.
Source: Stacks 08JA (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podDerivedHomShift := (podDerivedHomShift_existsUnique.{r, s, t, w} J A).exists.choose
end SignedShifts

section FiniteCoherence
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y Z : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

/-- The finite signed shift identification is the fixed representative map.
Source: node proof step 6 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podFiniteHomShift (W : Scheme.{u}) (n : ℕ) :=
  podDerivedHomShift.{u, u+1, u} (ProEt.topology W) (integralCoefficientCommRingSheaf l E W n)

/-- The comparison commutes with shifts in both arguments, in every integer degree.
Source: node proof step 6, Stacks 08JA.
Proof: exact inverse image acts termwise and preserves the Hom product projections.
It preserves the sign (-1)^(m*k) and reindexing p to p+m in the defining shift map.
Thus the equality holds on the signed Hom complexes. Insert the canonical
K-injective models and exact pullback shift comparisons, then localize.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podFiniteHomComparison_shift (n : ℕ)
    (M N : proEtaleDerivedCategory Y (finiteCoefficientRing l E (n + 1))) (a b : ℤ) :
    (podFiniteHomComparison l E g n M N)⟦b - a⟧' ≫
        (podFiniteHomShift l E X n
          ((finiteDerivedPullback l E n g).obj M)
          ((finiteDerivedPullback l E n g).obj N) a b).hom =
      ((finiteDerivedPullback l E n g).commShiftIso (b - a)).inv.app
          ((finiteIntrinsicDerivedInternalHom l E Y n).obj (op M, N)) ≫
        (finiteDerivedPullback l E n g).map (podFiniteHomShift l E Y n M N a b).hom ≫
        podFiniteHomComparison l E g n (M⟦a⟧) (N⟦b⟧) ≫
        (finiteIntrinsicDerivedInternalHom l E X n).map
          (Prod.mkHom (((finiteDerivedPullback l E n g).commShiftIso a).inv.app M).op
            (((finiteDerivedPullback l E n g).commShiftIso b).hom.app N)) := by
  sorry

/-- The canonical scheme-composition comparison, induced by intrinsic pullback's
published composition and exact derived factorization.
Source: node proof step 7 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podFinitePullbackComp (h : Z ⟶ X) (n : ℕ) :
    finiteDerivedPullback l E n (h ≫ g) ≅
      finiteDerivedPullback l E n g ⋙ finiteDerivedPullback l E n h :=
  Functor.mapDerivedCategoryNatIso
      (sfIntrinsicPullbackComp (finiteCoefficientRing l E (n + 1)) h g) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

omit [IsIso g] in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem finite_tensor_app (n : ℕ)
    (M N : proEtaleDerivedCategory Y (finiteCoefficientRing l E (n + 1))) :
    (finitePullbackTensorConstructionIso l E g n).hom.app (M, N) =
      (canonicalFinitePullbackTensor l E g n M N).hom := by
  rfl

attribute [local irreducible] finiteIntrinsicClosed podFiniteHomComparison

/-- Hom comparisons commute with composition of scheme isomorphisms.
Source: node proof step 7, Stacks 0GMX.
Proof: on sections, inverse image under a composite reindexes by the composite
site functor. Both Hom maps send a local homomorphism to this same reindexed
homomorphism. The published pullback comparison is exactly the unit-normalized
reindexing comparison. Tensor and evaluation have the same composition rule.
Taking their closed transposes gives the equation, before localization and
therefore in the unbounded derived category.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podFiniteHomComparison_comp (h : Z ⟶ X) [IsIso h]
    [∀ z : Z, Invertible (l : Z.residueField z)] (n : ℕ)
    (M N : proEtaleDerivedCategory Y (finiteCoefficientRing l E (n + 1))) :
    (podFinitePullbackComp l E g h n).hom.app
          ((finiteIntrinsicDerivedInternalHom l E Y n).obj (op M, N)) ≫
        (finiteDerivedPullback l E n h).map (podFiniteHomComparison l E g n M N) ≫
        podFiniteHomComparison l E h n
          ((finiteDerivedPullback l E n g).obj M) ((finiteDerivedPullback l E n g).obj N) =
      podFiniteHomComparison l E (h ≫ g) n M N ≫
        (finiteIntrinsicDerivedInternalHom l E Z n).map
          (Prod.mkHom ((podFinitePullbackComp l E g h n).inv.app M).op
            ((podFinitePullbackComp l E g h n).hom.app N)) := by
  let F := finiteDerivedPullback l E n g
  let G := finiteDerivedPullback l E n h
  let V := finiteDerivedPullback l E n (h ≫ g)
  let TY := finiteIntrinsicDerivedTensor l E Y n
  let TX := finiteIntrinsicDerivedTensor l E X n
  let TZ := finiteIntrinsicDerivedTensor l E Z n
  let HY := finiteIntrinsicDerivedInternalHom l E Y n
  let HX := finiteIntrinsicDerivedInternalHom l E X n
  let HZ := finiteIntrinsicDerivedInternalHom l E Z n
  let μg := finitePullbackTensorConstructionIso l E g n
  let μh := finitePullbackTensorConstructionIso l E h n
  let μv := finitePullbackTensorConstructionIso l E (h ≫ g) n
  let μ : TY ⋙ (F ⋙ G) ≅ ((F ⋙ G).prod (F ⋙ G)) ⋙ TZ :=
    NatIso.ofComponents (fun MN ↦ G.mapIso (μg.app MN) ≪≫
      μh.app (F.obj MN.1, F.obj MN.2)) (by
        intro MN MN' f
        have hf := μg.hom.naturality f
        have hg := μh.hom.naturality ((F.prod F).map f)
        dsimp only [Functor.comp_map, Functor.prod_map, Functor.prod_obj] at hf hg ⊢
        dsimp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
        rw [← Category.assoc, ← G.map_comp, hf, G.map_comp, Category.assoc]
        simpa only [Category.assoc] using
          congrArg (G.map (μg.hom.app MN) ≫ ·) hg)
  have he := (podFiniteHomComparison_laws l E g n).2.2.1
  have he' := (podFiniteHomComparison_laws l E h n).2.2.1
  have hev := (podFiniteHomComparison_laws l E (h ≫ g) n).2.2.1
  symm
  apply PodReindexingCoherence.hom_transport TY HY HZ (finiteIntrinsicClosed l E Z n)
    V (F ⋙ G) μv μ (podFiniteHomComparison l E (h ≫ g) n)
    (fun M N ↦ G.map (podFiniteHomComparison l E g n M N) ≫
      podFiniteHomComparison l E h n (F.obj M) (F.obj N))
    (finiteIntrinsicEvaluation l E Y n) hev ?_ (podFinitePullbackComp l E g h n) ?_ M N
  · intro M N
    simpa only [μ, NatIso.ofComponents_hom_app, Iso.trans_hom, Functor.mapIso_hom,
      Iso.app_hom, Functor.comp_obj, Functor.comp_map, Category.assoc,
      TZ, finiteIntrinsicDerivedTensor] using
      PodReindexingCoherence.composite_evaluation F G TY TX TZ HY HX HZ μg μh
        (podFiniteHomComparison l E g n) (podFiniteHomComparison l E h n)
        (finiteIntrinsicEvaluation l E Y n) (finiteIntrinsicEvaluation l E X n)
        (finiteIntrinsicEvaluation l E Z n) he he' M N
  · intro M N
    simpa only [μ, NatIso.ofComponents_hom_app, Iso.trans_hom, Functor.mapIso_hom,
      Iso.app_hom, Category.assoc, TY, TZ, μv, μg, μh, F, G, V,
      finiteIntrinsicDerivedTensor, canonicalFinitePullbackTensor,
      podFinitePullbackComp, sfIntrinsicDerivedPullbackComp,
      finite_tensor_app] using
      canonicalFinitePullbackTensor_composition l E g h n M N
end FiniteCoherence

section IntegralShiftCoherence
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

/-- Ambient completed-ring Hom has the same signed representative shift.
Source: node proof step 6 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podIntegralAmbientHomShift (W : Scheme.{u}) :=
  podDerivedHomShift.{u, u+1, u} (ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W)

set_option linter.unusedSectionVars false in
/-- The permitted integral pairs are stable under both argument shifts.
Source: node proof step 6, Stacks 08JA.
Proof: shift stability of the constructible subcategory gives both inputs.
The signed ambient Hom shift identifies the new Hom with a shift of the old
constructible Hom; shift stability and isomorphism closure give its property.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podIntegralPair_shift_property
    (P : (constructibleIntegralHomPairs l E Y).FullSubcategory) (a b : ℤ) :
    constructibleIntegralHomPairs l E Y (op (P.obj.1.unop⟦a⟧), P.obj.2⟦b⟧) := by
  exact PodCoefficientDescent.shifted_pair_permitted l E Y P a b

/-- The actual shifted pair, with its established Hom constructibility.
Source: Stacks 08JA (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podIntegralShiftPair
    (P : (constructibleIntegralHomPairs l E Y).FullSubcategory) (a b : ℤ) :
    (constructibleIntegralHomPairs l E Y).FullSubcategory :=
  ⟨(op (P.obj.1.unop⟦a⟧), P.obj.2⟦b⟧), podIntegralPair_shift_property l E P a b⟩

/-- Shift compatibility in exact completed-ring coordinates. Conjugating by the
canonical completion-unit comparison gives the tower-defined integral square.
Source: node proof steps 6, 8 and 11.
Proof: reindexing preserves every signed Hom projection exactly as at finite
coefficients. The complete-input comparison and its reduction/limit adjunct
are maps of exact functors and commute with these shifts. Insert their
normalizations in the signed representative equality. The restricted Hom
pair shift is the same ambient shift, so the displayed equation results.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podIntegralReindexedHom_shift
    (P : (constructibleIntegralHomPairs l E Y).FullSubcategory) (a b : ℤ) :
    (podIntegralReindexedHom l E g P)⟦b - a⟧' ≫
        (podIntegralAmbientHomShift l E X
          ((podCompletedDerivedInverseImage l E g).obj P.obj.1.unop.obj)
          ((podCompletedDerivedInverseImage l E g).obj P.obj.2.obj) a b).hom =
      ((podCompletedDerivedInverseImage l E g).commShiftIso (b - a)).inv.app
          ((integralDerivedInternalHom l E Y).obj (op P.obj.1.unop.obj, P.obj.2.obj)) ≫
        (podCompletedDerivedInverseImage l E g).map
          (podIntegralAmbientHomShift l E Y P.obj.1.unop.obj P.obj.2.obj a b).hom ≫
        (podCompletedDerivedInverseImage l E g).map
          ((integralDerivedInternalHom l E Y).map
            (Prod.mkHom (((sfIntegralConstructible l E Y).ι.commShiftIso a).hom.app
              P.obj.1.unop).op
              (((sfIntegralConstructible l E Y).ι.commShiftIso b).inv.app P.obj.2))) ≫
        podIntegralReindexedHom l E g (podIntegralShiftPair l E P a b) ≫
        (integralDerivedInternalHom l E X).map
          (Prod.mkHom ((((podCompletedDerivedInverseImage l E g).commShiftIso a).inv.app
              P.obj.1.unop.obj) ≫ (podCompletedDerivedInverseImage l E g).map
                (((sfIntegralConstructible l E Y).ι.commShiftIso a).inv.app P.obj.1.unop)).op
            ((podCompletedDerivedInverseImage l E g).map
                (((sfIntegralConstructible l E Y).ι.commShiftIso b).hom.app P.obj.2) ≫
              ((podCompletedDerivedInverseImage l E g).commShiftIso b).hom.app P.obj.2.obj)) := by
  sorry
end IntegralShiftCoherence

section IntegralComposition
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y Z : Scheme.{u}} (g : X ⟶ Y) [IsIso g] (h : Z ⟶ X) [IsIso h]

/-- Composition of exact completed inverse image is fixed on all local sections.
Source: node proof steps 1 and 7, Stacks 00WX.
Proof: composition of the two postcomposition functors agrees with postcomposition
by the composite, using associativity of scheme arrows. The identity on the
unchanged local sections is linear because both coefficient transports have
identical finite projections. It is a natural isomorphism; pointwise equality
on all local sections proves uniqueness.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podCompletedModuleComp_existsUnique :
    ∃! e : podCompletedModuleInverseImage l E (h ≫ g) ≅
        podCompletedModuleInverseImage l E g ⋙ podCompletedModuleInverseImage l E h,
      ∀ (M : integralTowerModules l E Y) (U : Z.ProEt)
        (x : ((podCompletedModuleInverseImage l E (h ≫ g)).obj M).val.obj (op U)),
        HEq (((e.hom.app M).val.app (op U)) x) x := by
  sorry

/-- The unique identity-on-sections completed composition comparison.
Source: Stacks 00WX (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podCompletedModuleComp := (podCompletedModuleComp_existsUnique l E g h).exists.choose

/-- Derive that same ordinary comparison, using the fixed exact factorizations.
Source: node proof steps 2 and 7
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podCompletedDerivedComp : podCompletedDerivedInverseImage l E (h ≫ g) ≅
    podCompletedDerivedInverseImage l E g ⋙ podCompletedDerivedInverseImage l E h :=
  letI := podCompletedModuleAdditive l E g
  letI := podCompletedModuleAdditive l E h
  letI := podCompletedModuleAdditive l E (h ≫ g)
  letI := podCompletedModuleLimits l E g
  letI := podCompletedModuleLimits l E h
  letI := podCompletedModuleLimits l E (h ≫ g)
  letI := podCompletedModuleColimits l E g
  letI := podCompletedModuleColimits l E h
  letI := podCompletedModuleColimits l E (h ≫ g)
  Functor.mapDerivedCategoryNatIso (podCompletedModuleComp l E g h) ≪≫
    Functor.mapDerivedCategoryCompIso (podCompletedModuleInverseImage l E g)
      (podCompletedModuleInverseImage l E h)

variable [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]
  [∀ z : Z, Invertible (l : Z.residueField z)]

/-- Published integral tower composition has the actual completion-unit normalization.
Source: node proof steps 7--8.
Proof: conjugate the derived identity-on-sections composition by the three
complete-input identifications. Their maps are fixed by completion units and
total-limit reindexing. Hence this is the canonical tower composition, natural
by their naturality. Its component formula determines it uniquely.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podIntegralPullbackComp_normalization
    (M : sfIntegralConstructibleCategory l E Y) :
    HEq (((pullbackTensorIntegralComposition l E g h).hom.app M).hom)
      ((podCompletedToTowerIso l E (h ≫ g) M).inv ≫
        (podCompletedDerivedComp l E g h).hom.app M.obj ≫
        (podCompletedDerivedInverseImage l E h).map (podCompletedToTowerIso l E g M).hom ≫
        (podCompletedToTowerIso l E h ((constructibleIntegralPullback l E g).obj M)).hom) := by
  sorry

/-- Integral comparisons commute with composition, using canonical tower composition.
Source: node proof steps 7, 8 and 11.
Proof: reindexing Hom twice equals reindexing once by the composite on each
product projection. Its evaluation formula therefore agrees before localization.
Conjugate by the completion-unit comparisons. Their normalization gives exactly
the displayed composition maps, including the contravariant first argument.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podIntegralHomComparison_comp
    (P : (constructibleIntegralHomPairs l E Y).FullSubcategory) :
    (pullbackTensorIntegralComposition l E g h).hom.app ((constructibleIntegralHom l E Y).obj P) ≫
        (constructibleIntegralPullback l E h).map (podIntegralHomComparison l E g P) ≫
        podIntegralHomComparison l E h
          ((podPairPullback (constructibleIntegralPullback l E g) _ _
            (podIntegralPairs_pullback l E g)).obj P) =
      podIntegralHomComparison l E (h ≫ g) P ≫
        (constructibleIntegralHom l E Z).map
          (ObjectProperty.homMk
            (X := (podPairPullback (constructibleIntegralPullback l E (h ≫ g)) _ _
              (podIntegralPairs_pullback l E (h ≫ g))).obj P)
            (Y := (podPairPullback (constructibleIntegralPullback l E h) _ _
              (podIntegralPairs_pullback l E h)).obj
                ((podPairPullback (constructibleIntegralPullback l E g) _ _
                  (podIntegralPairs_pullback l E g)).obj P))
            (Prod.mkHom ((pullbackTensorIntegralComposition l E g h).inv.app P.obj.1.unop).op
              ((pullbackTensorIntegralComposition l E g h).hom.app P.obj.2))) := by
  sorry
end IntegralComposition

/-- Evaluation equation of the coefficient base-change map: precomposed with the
tensor comparison, the transpose `c` followed by evaluation is the image of evaluation.
Source: Stacks 0GMX; the map of def-pur-coefficient-base-change-hom.
Proof: `c` is the closed transpose of `μ⁻¹ ≫ F(ev)`; the counit identity of the
right-tensor/internal-Hom adjunction gives `(c ⊗ 1) ≫ ev = μ⁻¹ ≫ F(ev)`, and
precomposing with `μ` cancels `μ⁻¹`.
(blueprint: stage3-derived-automorphism-continuation-b). -/
theorem baseChangeHom_evaluation
    {A : Type a} {B : Type c} [Category.{b} A] [Category.{d} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor) (P Q : A) :
    μ.hom.app (HA.obj (op P, Q), P) ≫
      SB.tensor.map (Prod.mkHom (coefficientBaseChangeHom SA SB F μ P Q) (𝟙 _)) ≫
      SB.evaluation (F.obj P) (F.obj Q) = F.map (SA.evaluation P Q) := by
  let := SB.monoidal
  have h := ((SB.adjunction (F.obj P)).homEquiv _ _).symm_apply_apply
    (μ.inv.app (HA.obj (op P, Q), P) ≫ F.map (SA.evaluation P Q))
  rw [Adjunction.homEquiv_counit] at h
  change (MonoidalCategory.tensorRight (F.obj P)).map
    (coefficientBaseChangeHom SA SB F μ P Q) ≫ SB.evaluation (F.obj P) (F.obj Q) = _ at h
  change μ.hom.app (HA.obj (op P, Q), P) ≫
    (MonoidalCategoryStruct.tensorHom
      (coefficientBaseChangeHom SA SB F μ P Q) (𝟙 (F.obj P))) ≫
    SB.evaluation (F.obj P) (F.obj Q) = F.map (SA.evaluation P Q)
  erw [MonoidalCategory.tensorHom_id]
  erw [h]
  exact Iso.hom_inv_id_app_assoc μ _ _

section SystemFibers
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]

/-- Reindexing preserves normalized coefficient systems, including all transitions.
Source: node proof step 12, Stacks 0941.
Proof: reindex the simultaneous flat-term system representative. Each quotient
comparison is the unit-normalized finite inverse image, and every transition
is unchanged. Reindexing the inverse data gives normalization of the result.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podSystemNormalized (M : coefficientSequenceDerived l E Y)
    (hM : IsNormalizedCoefficientSequence l E Y M) :
    IsNormalizedCoefficientSequence l E X ((pullbackTensorSequenceDerived l E g).obj M) := by
  sorry

variable [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

/-- The actual system Hom comparison has the prescribed finite fibers.
Source: node proof steps 12--13.
Proof: on one simultaneous normalized system model, evaluate the Hom-product
reindexing chain map. Its projections are precisely the finite Hom reindexing
map. The fiber maps are induced by that same evaluation and transposition,
not independent choices. Their representative equations yield this square in
the finite derived category; the original equality of system maps was already
established before any evaluation.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podSystemHomComparison_fiber
    (M N : coefficientSequenceDerived l E Y)
    (hM : IsNormalizedCoefficientSequence l E Y M)
    (hN : IsNormalizedCoefficientSequence l E Y N) (n : ℕ) :
    (coefficientSequenceDerivedEvaluation l E X n).map (podSystemHomComparison l E g M N) ≫
        ((pullbackTensorCalculus l E X).fiberHom
          ((pullbackTensorSequenceDerived l E g).obj M)
          ((pullbackTensorSequenceDerived l E g).obj N)
          (podSystemNormalized l E g M hM) (podSystemNormalized l E g N hN) n).hom =
      (pullbackTensorDerivedEvaluation l E g n).hom.app
          ((coefficientSequenceInternalHom l E Y).obj (op M, N)) ≫
        (finiteDerivedPullback l E n g).map
          ((pullbackTensorCalculus l E Y).fiberHom M N hM hN n).hom ≫
        podFiniteHomComparison l E g n
          ((coefficientSequenceDerivedEvaluation l E Y n).obj M)
          ((coefficientSequenceDerivedEvaluation l E Y n).obj N) ≫
        (finiteIntrinsicDerivedInternalHom l E X n).map
          (Prod.mkHom ((pullbackTensorDerivedEvaluation l E g n).hom.app M).op
            ((pullbackTensorDerivedEvaluation l E g n).inv.app N)) := by
  sorry

set_option linter.unusedSectionVars false in
/-- The system evaluation identity holds in its functorial total-limit realization.
Source: node proof steps 12--13.
Proof: apply the functorial derived limit to the already established system
map equality. Functoriality preserves its composites. The specified total-limit
models identify these images with the realized evaluation maps; no equality
reflection from separately evaluated levels occurs.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podSystemHomComparison_realizedEvaluation
    (M N : coefficientSequenceDerived l E Y) :
    (coefficientSequenceLimit l E X).map
      ((pullbackTensorSystemComparison l E g).hom.app
          ((coefficientSequenceInternalHom l E Y).obj (op M, N), M) ≫
        (pullbackTensorCalculus l E X).systemClosed.tensor.map
          (Prod.mkHom (podSystemHomComparison l E g M N) (𝟙 _)) ≫
        (pullbackTensorCalculus l E X).systemClosed.evaluation
          ((pullbackTensorSequenceDerived l E g).obj M)
          ((pullbackTensorSequenceDerived l E g).obj N)) =
      (coefficientSequenceLimit l E X).map
        ((pullbackTensorSequenceDerived l E g).map
          ((pullbackTensorCalculus l E Y).systemClosed.evaluation M N)) := by
  apply congrArg ((coefficientSequenceLimit l E X).map)
  exact baseChangeHom_evaluation
    (pullbackTensorCalculus l E Y).systemClosed
    (pullbackTensorCalculus l E X).systemClosed (pullbackTensorSequenceDerived l E g)
    (pullbackTensorSystemComparison l E g) M N

end SystemFibers

/-- The argument-first evaluation convention of the statement, obtained by the
specified Koszul symmetry from the recorded Hom-first closed structure.
Source: Stacks 08J9 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podArgumentFirstEvaluation {C : Type a} [Category.{b} C] [Preadditive C]
    {T : C × C ⥤ C} {J : ObjectProperty (Cᵒᵖ × C)} {H : J.FullSubcategory ⥤ C}
    (S : PodPartialClosed T J H)
    (β : ∀ M N : C, T.obj (M, N) ≅ T.obj (N, M)) (P : J.FullSubcategory) :=
  (β P.obj.1.unop (H.obj P)).hom ≫ S.evaluation P

/-- Evaluation and every transpose in exactly the argument-first convention.
Source: Stacks 0GMX (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def PodArgumentFirstLaws {C : Type a} {D : Type c}
    [Category.{b} C] [Category.{d} D] [Preadditive C] [Preadditive D]
    {TC : C × C ⥤ C} {TD : D × D ⥤ D}
    {J : ObjectProperty (Cᵒᵖ × C)} {K : ObjectProperty (Dᵒᵖ × D)}
    {HC : J.FullSubcategory ⥤ C} {HD : K.FullSubcategory ⥤ D}
    (SC : PodPartialClosed TC J HC) (SD : PodPartialClosed TD K HD)
    (F : C ⥤ D) (h : ∀ P : J.FullSubcategory, K ((F.op.prod F).obj P.obj))
    (μ : ∀ L M : C, F.obj (TC.obj (L, M)) ≅ TD.obj (F.obj L, F.obj M))
    (βC : ∀ M N : C, TC.obj (M, N) ≅ TC.obj (N, M))
    (βD : ∀ M N : D, TD.obj (M, N) ≅ TD.obj (N, M)) : Prop :=
  (∀ P : J.FullSubcategory,
    (μ P.obj.1.unop (HC.obj P)).hom ≫
      TD.map (Prod.mkHom (𝟙 _) (podPartialHomComparison SC SD F h μ P)) ≫
      podArgumentFirstEvaluation SD βD ((podPairPullback F J K h).obj P) =
    F.map (podArgumentFirstEvaluation SC βC P)) ∧
  ∀ (L : C) (P : J.FullSubcategory) (b : TC.obj (P.obj.1.unop, L) ⟶ P.obj.2),
    SD.transpose _ _ ((βD (F.obj L) (F.obj P.obj.1.unop)).hom ≫
        (μ P.obj.1.unop L).inv ≫ F.map b) =
      F.map (SC.transpose L P ((βC L P.obj.1.unop).hom ≫ b)) ≫
        podPartialHomComparison SC SD F h μ P

private theorem argumentFirst_of_braiding
    {C : Type a} {D : Type c}
    [Category.{b} C] [Category.{d} D] [Preadditive C] [Preadditive D]
    {TC : C × C ⥤ C} {TD : D × D ⥤ D}
    {J : ObjectProperty (Cᵒᵖ × C)} {K : ObjectProperty (Dᵒᵖ × D)}
    {HC : J.FullSubcategory ⥤ C} {HD : K.FullSubcategory ⥤ D}
    (SC : PodPartialClosed TC J HC) (SD : PodPartialClosed TD K HD)
    (F : C ⥤ D) (h : ∀ P : J.FullSubcategory, K ((F.op.prod F).obj P.obj))
    (μ : ∀ L M : C, F.obj (TC.obj (L, M)) ≅ TD.obj (F.obj L, F.obj M))
    (βC : ∀ M N : C, TC.obj (M, N) ≅ TC.obj (N, M))
    (βD : ∀ M N : D, TD.obj (M, N) ≅ TD.obj (N, M))
    (hc : PodPartialHomCompatibility SC SD F h μ)
    (hn : ∀ (M M' N N' : D) (f : M ⟶ M') (g : N ⟶ N'),
      TD.map (Prod.mkHom f g) ≫ (βD M' N').hom =
        (βD M N).hom ≫ TD.map (Prod.mkHom g f))
    (hb : ∀ M N : C, F.map (βC M N).hom ≫ (μ N M).hom =
      (μ M N).hom ≫ (βD (F.obj M) (F.obj N)).hom) :
    PodArgumentFirstLaws SC SD F h μ βC βD := by
  constructor
  · intro P
    have hn' := congrArg
      (fun k ↦ (μ P.obj.1.unop (HC.obj P)).hom ≫ k ≫
        SD.evaluation ((podPairPullback F J K h).obj P))
      (hn _ _ _ _ (𝟙 (F.obj P.obj.1.unop)) (podPartialHomComparison SC SD F h μ P))
    have hb' := congrArg (fun k ↦ k ≫
      TD.map (Prod.mkHom (podPartialHomComparison SC SD F h μ P) (𝟙 _)) ≫
      SD.evaluation ((podPairPullback F J K h).obj P))
      (hb P.obj.1.unop (HC.obj P))
    have he := congrArg (fun k ↦ F.map (βC P.obj.1.unop (HC.obj P)).hom ≫ k)
      (hc.evaluation P)
    change (μ P.obj.1.unop (HC.obj P)).hom ≫
      TD.map (Prod.mkHom (𝟙 _) (podPartialHomComparison SC SD F h μ P)) ≫
      (βD (F.obj P.obj.1.unop) (HD.obj ((podPairPullback F J K h).obj P))).hom ≫
      SD.evaluation ((podPairPullback F J K h).obj P) =
        F.map ((βC P.obj.1.unop (HC.obj P)).hom ≫ SC.evaluation P)
    simp only [Category.assoc] at hn' hb' he
    simpa only [Functor.map_comp] using hn'.trans (hb'.symm.trans he)
  · intro L P f
    have hs : (βD (F.obj L) (F.obj P.obj.1.unop)).hom ≫ (μ P.obj.1.unop L).inv =
        (μ L P.obj.1.unop).inv ≫ F.map (βC L P.obj.1.unop).hom := by
      apply (cancel_epi (μ L P.obj.1.unop).hom).mp
      simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
        Category.id_comp, Category.comp_id] using
        congrArg (fun k ↦ k ≫ (μ P.obj.1.unop L).inv) (hb L P.obj.1.unop).symm
    rw [← Category.assoc, hs, Category.assoc, ← F.map_comp]
    exact hc.transpose L P ((βC L P.obj.1.unop).hom ≫ f)

section ArgumentFirstStages
attribute [local irreducible] pullbackTensorBraiding canonicalFinitePullbackTensor
  finiteIntrinsicClosed finiteIntrinsicTensorModels podFiniteHomComparison
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

/-- Integral and rational equations in the node's argument-first convention.
Source: node proof steps 4--5, 11 and 14.
Proof: precompose the Hom-first evaluation equation with the canonical Koszul
braiding. Its naturality moves c to the second factor; tensor pullback respects
this braiding by the published signed comparison equation. Transpose after
the same swap. Localization preserves these composites and their identities.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podArgumentFirst_integral_rational :
    PodArgumentFirstLaws (podIntegralClosed l E Y) (podIntegralClosed l E X)
      (constructibleIntegralPullback l E g) (podIntegralPairs_pullback l E g)
      (canonicalIntegralPullbackTensor l E g)
      (pullbackTensorIntegralBraiding l E Y) (pullbackTensorIntegralBraiding l E X) ∧
    PodArgumentFirstLaws (podRationalClosed l E Y) (podRationalClosed l E X)
      (rationalDerivedPullback l E g) (podRationalPairs_pullback l E g)
      (canonicalRationalPullbackTensor l E g)
      (pullbackTensorRationalBraiding l E Y) (pullbackTensorRationalBraiding l E X) := by
  constructor
  · exact argumentFirst_of_braiding _ _ _ _ _ _ _ (podIntegralHomComparison_laws l E g)
      (integralBraiding_natural l E X) (canonicalIntegralPullbackTensor_braiding_spec l E g)
  · exact argumentFirst_of_braiding _ _ _ _ _ _ _ (podRationalHomComparison_laws l E g).1
      (rationalBraiding_natural l E X) (canonicalRationalPullbackTensor_braiding_spec l E g)

/-- Finite evaluation with argument first is the actual signed swap followed by
recorded evaluation. Source: node proof step 4
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podFiniteArgumentFirstEvaluation (W : Scheme.{u}) (n : ℕ)
    (M N : proEtaleDerivedCategory W (finiteCoefficientRing l E (n + 1))) :=
  (pullbackTensorBraiding (ProEt.topology W) (integralCoefficientCommRingSheaf l E W n)
      (finiteIntrinsicClosed l E W n) (finiteIntrinsicTensorModels l E W n)).hom.app
      (M, (finiteIntrinsicDerivedInternalHom l E W n).obj (op M, N)) ≫
    finiteIntrinsicEvaluation l E W n M N

/-- The finite argument-first evaluation equation is the displayed equation of
the node. Source: node proof steps 4--5.
Proof: combine the Hom-first equation with signed braiding naturality and its
published tensor-pullback square. Both paths evaluate the same local map on
the same local section, including the Koszul sign on homogeneous complexes.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podArgumentFirst_finite (n : ℕ)
    (M N : proEtaleDerivedCategory Y (finiteCoefficientRing l E (n + 1))) :
    (canonicalFinitePullbackTensor l E g n M
        ((finiteIntrinsicDerivedInternalHom l E Y n).obj (op M, N))).hom ≫
      (finiteIntrinsicDerivedTensor l E X n).map
        (Prod.mkHom (𝟙 _) (podFiniteHomComparison l E g n M N)) ≫
      podFiniteArgumentFirstEvaluation l E X n
        ((finiteDerivedPullback l E n g).obj M) ((finiteDerivedPullback l E n g).obj N) =
    (finiteDerivedPullback l E n g).map (podFiniteArgumentFirstEvaluation l E Y n M N) := by
  let F := finiteDerivedPullback l E n g
  let HY := finiteIntrinsicDerivedInternalHom l E Y n
  let βY : finiteIntrinsicDerivedTensor l E Y n ≅
      pullbackTensorSwap _ ⋙ finiteIntrinsicDerivedTensor l E Y n :=
    pullbackTensorBraiding.{u} (ProEt.topology Y)
    (integralCoefficientCommRingSheaf l E Y n)
    (finiteIntrinsicClosed l E Y n) (finiteIntrinsicTensorModels l E Y n)
  let βX : finiteIntrinsicDerivedTensor l E X n ≅
      pullbackTensorSwap _ ⋙ finiteIntrinsicDerivedTensor l E X n :=
    pullbackTensorBraiding.{u} (ProEt.topology X)
    (integralCoefficientCommRingSheaf l E X n)
    (finiteIntrinsicClosed l E X n) (finiteIntrinsicTensorModels l E X n)
  have hn := βX.hom.naturality
    (Prod.mkHom (𝟙 (F.obj M)) (podFiniteHomComparison l E g n M N))
  have hb := canonicalFinitePullbackTensor_braiding l E g n M (HY.obj (op M, N))
  have he := (podFiniteHomComparison_laws l E g n).2.2.1 M N
  change _ ≫ _ ≫ (βX.hom.app _ ≫ _) = F.map (βY.hom.app _ ≫ _)
  dsimp only [Functor.comp_map, pullbackTensorSwap] at hn
  have hn' := congrArg
    (fun k ↦ (canonicalFinitePullbackTensor l E g n M (HY.obj (op M, N))).hom ≫
      k ≫ finiteIntrinsicEvaluation l E X n (F.obj M) (F.obj N)) hn
  have hb' := congrArg (fun k ↦ k ≫
    (finiteIntrinsicDerivedTensor l E X n).map
      (Prod.mkHom (podFiniteHomComparison l E g n M N) (𝟙 _)) ≫
    finiteIntrinsicEvaluation l E X n (F.obj M) (F.obj N)) hb
  have hlast := congrArg
    (fun k ↦ F.map (βY.hom.app (M, HY.obj (op M, N))) ≫ k) he
  have hmiddle : _ := hb'.symm
  simp only [Category.assoc] at hn' hmiddle hlast
  simpa only [Functor.map_comp] using hn'.trans (hmiddle.trans hlast)
/-- The finite transpose equation with the tensor arguments in the node's order.
Source: node proof steps 4--5.
Proof: swap the two tensor factors by their fixed signed braiding, apply finite
transposition, and use the tensor-pullback braiding square. The two swaps give
exactly the argument-first adjunction, so currying yields the displayed map.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podArgumentFirst_finite_transpose (n : ℕ)
    (L M N : proEtaleDerivedCategory Y (finiteCoefficientRing l E (n + 1)))
    (b : (finiteIntrinsicDerivedTensor l E Y n).obj (M, L) ⟶ N) :
    finiteIntrinsicTranspose l E X n _ _ _
      ((pullbackTensorBraiding (ProEt.topology X) (integralCoefficientCommRingSheaf l E X n)
          (finiteIntrinsicClosed l E X n) (finiteIntrinsicTensorModels l E X n)).hom.app
          ((finiteDerivedPullback l E n g).obj L, (finiteDerivedPullback l E n g).obj M) ≫
        (canonicalFinitePullbackTensor l E g n M L).inv ≫
        (finiteDerivedPullback l E n g).map b) =
      (finiteDerivedPullback l E n g).map
        (finiteIntrinsicTranspose l E Y n L M N
          ((pullbackTensorBraiding (ProEt.topology Y) (integralCoefficientCommRingSheaf l E Y n)
              (finiteIntrinsicClosed l E Y n) (finiteIntrinsicTensorModels l E Y n)).hom.app
              (L, M) ≫ b)) ≫
        podFiniteHomComparison l E g n M N := by
  let F := finiteDerivedPullback l E n g
  let βY : finiteIntrinsicDerivedTensor l E Y n ≅
      pullbackTensorSwap _ ⋙ finiteIntrinsicDerivedTensor l E Y n :=
    pullbackTensorBraiding.{u} (ProEt.topology Y)
    (integralCoefficientCommRingSheaf l E Y n)
    (finiteIntrinsicClosed l E Y n) (finiteIntrinsicTensorModels l E Y n)
  let βX : finiteIntrinsicDerivedTensor l E X n ≅
      pullbackTensorSwap _ ⋙ finiteIntrinsicDerivedTensor l E X n :=
    pullbackTensorBraiding.{u} (ProEt.topology X)
    (integralCoefficientCommRingSheaf l E X n)
    (finiteIntrinsicClosed l E X n) (finiteIntrinsicTensorModels l E X n)
  have hb := canonicalFinitePullbackTensor_braiding l E g n L M
  have hs : βX.hom.app (F.obj L, F.obj M) ≫
      (canonicalFinitePullbackTensor l E g n M L).inv =
      (canonicalFinitePullbackTensor l E g n L M).inv ≫ F.map (βY.hom.app (L, M)) := by
    apply (cancel_epi (canonicalFinitePullbackTensor l E g n L M).hom).mp
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
      Category.id_comp, Category.comp_id] using
      congrArg (fun k ↦ k ≫ (canonicalFinitePullbackTensor l E g n M L).inv) hb.symm
  change finiteIntrinsicTranspose l E X n _ _ _
    (βX.hom.app _ ≫ (canonicalFinitePullbackTensor l E g n M L).inv ≫ F.map b) = _
  rw [← Category.assoc, hs, Category.assoc, ← F.map_comp]
  exact (podFiniteHomComparison_laws l E g n).2.2.2 L M N (βY.hom.app (L, M) ≫ b)
end ArgumentFirstStages

section ArgumentFirstCommon
variable (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
  [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

/-- The displayed argument-first equations at algebraically closed coefficients.
Source: node proof step 16.
Proof: put the inputs and each arrow over one finite field. The prescribed
common braiding, tensor comparison and transpose are the rational maps there.
Apply the rational argument-first equations. Their scalar compatibility gives
the equality in the actual common-stage Hom group, for every representative.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podArgumentFirst_common :
    PodArgumentFirstLaws (podCommonClosed l Ω Y) (podCommonClosed l Ω X)
      (commonStageDerivedPullback l Ω g) (podCommonPairs_pullback l Ω g)
      (canonicalCommonStagePullbackTensor l Ω g)
      (pullbackTensorCommonBraiding l Ω Y) (pullbackTensorCommonBraiding l Ω X) := by
  exact argumentFirst_of_braiding _ _ _ _ _ _ _ (podCommonHomComparison_laws l Ω g)
    (commonStageTensorBraiding_naturality l Ω X
      (fun E _ _ _ ↦ rationalBraiding_natural l E X))
    (canonicalCommonStagePullbackTensor_braiding_spec l Ω g)
end ArgumentFirstCommon

section FieldComposition
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y Z : Scheme.{u}} (g : X ⟶ Y) [IsIso g] (h : Z ⟶ X) [IsIso h]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]
  [∀ z : Z, Invertible (l : Z.residueField z)]

/-- Composition at E uses the published localized integral composition maps.
Source: node proof steps 7 and 14.
Proof: localize the integral composition equation. Every comparison component
and composition identification is the prescribed localized component. The
localization functor preserves composites, hence gives the displayed equality.
No restriction on localized arrows enters, since naturality is additive and
balanced and already holds for all of them.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podRationalHomComparison_comp
    (P : (constructibleRationalHomPairs l E Y).FullSubcategory) :
    (pullbackTensorRationalComposition l E g h
        ((rationalDerivedInternalHom l E Y).obj P)).hom ≫
        (rationalDerivedPullback l E h).map (podRationalHomComparison l E g P) ≫
        podRationalHomComparison l E h
          ((podPairPullback (rationalDerivedPullback l E g) _ _
            (podRationalPairs_pullback l E g)).obj P) =
      podRationalHomComparison l E (h ≫ g) P ≫
        (rationalDerivedInternalHom l E Z).map
          (ObjectProperty.homMk
            (X := (podPairPullback (rationalDerivedPullback l E (h ≫ g)) _ _
              (podRationalPairs_pullback l E (h ≫ g))).obj P)
            (Y := (podPairPullback (rationalDerivedPullback l E h) _ _
              (podRationalPairs_pullback l E h)).obj
                ((podPairPullback (rationalDerivedPullback l E g) _ _
                  (podRationalPairs_pullback l E g)).obj P))
            (Prod.mkHom (pullbackTensorRationalComposition l E g h P.obj.1.unop).inv.op
              (pullbackTensorRationalComposition l E g h P.obj.2).hom)) := by
  sorry
end FieldComposition

section CommonComposition
variable (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
  [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  {X Y Z : Scheme.{u}} (g : X ⟶ Y) [IsIso g] (h : Z ⟶ X) [IsIso h]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]
  [∀ z : Z, Invertible (l : Z.residueField z)]

/-- Common-stage composition holds in the actual Hom-colimit category.
Source: node proof steps 7 and 16.
Proof: use a common finite coefficient stage for the pair, comparisons and
composition arrows. The specified common-stage transpose and tensor comparison
identify c with the rational c. The published common composition is represented
by the rational composition. Apply the rational equation and take its class;
scalar-extension compatibility makes this independent of all enlargements.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podCommonHomComparison_comp
    (P : (commonStageHomPairs l Ω Y).FullSubcategory) :
    (pullbackTensorCommonComposition l Ω g h
        ((commonStageDerivedInternalHom l Ω Y).obj P)).hom ≫
        (commonStageDerivedPullback l Ω h).map (podCommonHomComparison l Ω g P) ≫
        podCommonHomComparison l Ω h
          ((podPairPullback (commonStageDerivedPullback l Ω g) _ _
            (podCommonPairs_pullback l Ω g)).obj P) =
      podCommonHomComparison l Ω (h ≫ g) P ≫
        (commonStageDerivedInternalHom l Ω Z).map
          (ObjectProperty.homMk
            (X := (podPairPullback (commonStageDerivedPullback l Ω (h ≫ g)) _ _
              (podCommonPairs_pullback l Ω (h ≫ g))).obj P)
            (Y := (podPairPullback (commonStageDerivedPullback l Ω h) _ _
              (podCommonPairs_pullback l Ω h)).obj
                ((podPairPullback (commonStageDerivedPullback l Ω g) _ _
                  (podCommonPairs_pullback l Ω g)).obj P))
            (Prod.mkHom (pullbackTensorCommonComposition l Ω g h P.obj.1.unop).inv.op
              (pullbackTensorCommonComposition l Ω g h P.obj.2).hom)) := by
  sorry
end CommonComposition

section RestrictedShiftMaps
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

/-- Restrict the canonical signed ambient Hom shift to the permitted pairs.
Source: node proof step 6, Stacks 08JA.
Proof: all three objects are constructible by shift closure and the shifted-pair
property. The inclusion is fully faithful, so the displayed ambient isomorphism
and its inverse lift uniquely. The inclusion shift comparison reconciles its
chosen shift object with the ambient shifted complex.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podIntegralHomShift_existsUnique
    (P : (constructibleIntegralHomPairs l E Y).FullSubcategory) (a b : ℤ) :
    ∃! e : ((constructibleIntegralHom l E Y).obj P)⟦b - a⟧ ≅
        (constructibleIntegralHom l E Y).obj (podIntegralShiftPair l E P a b),
      e.hom.hom = ((sfIntegralConstructible l E Y).ι.commShiftIso (b - a)).hom.app
          ((constructibleIntegralHom l E Y).obj P) ≫
        (podIntegralAmbientHomShift l E Y P.obj.1.unop.obj P.obj.2.obj a b).hom ≫
        (integralDerivedInternalHom l E Y).map
          (Prod.mkHom (((sfIntegralConstructible l E Y).ι.commShiftIso a).hom.app
            P.obj.1.unop).op
            (((sfIntegralConstructible l E Y).ι.commShiftIso b).inv.app P.obj.2)) := by
  let H (k : ℤ) := (sfIntegralConstructible l E Y).ι.commShiftIso k
  let e : (((constructibleIntegralHom l E Y).obj P)⟦b - a⟧).obj ≅
      ((constructibleIntegralHom l E Y).obj (podIntegralShiftPair l E P a b)).obj :=
    (H (b - a)).app ((constructibleIntegralHom l E Y).obj P) ≪≫
      podIntegralAmbientHomShift l E Y P.obj.1.unop.obj P.obj.2.obj a b ≪≫
      (integralDerivedInternalHom l E Y).mapIso
        (((H a).app P.obj.1.unop).op.prod ((H b).symm.app P.obj.2))
  refine ⟨(sfIntegralConstructible l E Y).isoMk e, rfl, ?_⟩
  intro f hf
  apply Iso.ext
  apply ObjectProperty.hom_ext
  exact hf

/-- The restricted signed Hom shift, with its actual ambient normalization.
Source: Stacks 08JA (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podIntegralHomShift
    (P : (constructibleIntegralHomPairs l E Y).FullSubcategory) (a b : ℤ) :=
  (podIntegralHomShift_existsUnique l E P a b).exists.choose

/-- Pullback's shift comparison is fixed through the canonical complete-input map.
Source: node proof steps 2, 6 and 8.
Proof: conjugate the termwise exact inverse-image shift by the completion-unit
identification, and then by the full-subcategory inclusion's shift comparison.
Naturality and the shift zero/addition equations are inherited from those
comparisons. The displayed equation fixes the isomorphism uniquely.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podIntegralPullbackShift_existsUnique
    (M : sfIntegralConstructibleCategory l E Y) (a : ℤ) :
    ∃! e : (constructibleIntegralPullback l E g).obj (M⟦a⟧) ≅
        ((constructibleIntegralPullback l E g).obj M)⟦a⟧,
      e.hom.hom = (podCompletedToTowerIso l E g (M⟦a⟧)).inv ≫
        (podCompletedDerivedInverseImage l E g).map
          (((sfIntegralConstructible l E Y).ι.commShiftIso a).hom.app M) ≫
        ((podCompletedDerivedInverseImage l E g).commShiftIso a).hom.app M.obj ≫
        ((podCompletedToTowerIso l E g M).hom)⟦a⟧' ≫
        ((sfIntegralConstructible l E X).ι.commShiftIso a).inv.app
          ((constructibleIntegralPullback l E g).obj M) := by
  let e : ((constructibleIntegralPullback l E g).obj (M⟦a⟧)).obj ≅
      (((constructibleIntegralPullback l E g).obj M)⟦a⟧).obj :=
    (podCompletedToTowerIso l E g (M⟦a⟧)).symm ≪≫
      (podCompletedDerivedInverseImage l E g).mapIso
        (((sfIntegralConstructible l E Y).ι.commShiftIso a).app M) ≪≫
      ((podCompletedDerivedInverseImage l E g).commShiftIso a).app M.obj ≪≫
      (shiftFunctor _ a).mapIso (podCompletedToTowerIso l E g M) ≪≫
      (((sfIntegralConstructible l E X).ι.commShiftIso a).symm.app
        ((constructibleIntegralPullback l E g).obj M))
  refine ⟨(sfIntegralConstructible l E X).isoMk e, rfl, ?_⟩
  intro f hf
  apply Iso.ext
  apply ObjectProperty.hom_ext
  exact hf

/-- The canonical shift identification of the tower-defined pullback.
Source: Stacks 08JA (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podIntegralPullbackShift (M : sfIntegralConstructibleCategory l E Y) (a : ℤ) :=
  (podIntegralPullbackShift_existsUnique l E g M a).exists.choose

/-- First route of the signed integral Hom shift square.
Source: node proof step 6 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podIntegralShiftRouteLeft
    (P : (constructibleIntegralHomPairs l E Y).FullSubcategory) (a b : ℤ) :=
  (podIntegralHomComparison l E g P)⟦b - a⟧' ≫
    (podIntegralHomShift l E
      ((podPairPullback (constructibleIntegralPullback l E g) _ _
        (podIntegralPairs_pullback l E g)).obj P) a b).hom

/-- Second route, including pullback shifts in both inputs and contravariance.
Source: node proof step 6 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podIntegralShiftRouteRight
    (P : (constructibleIntegralHomPairs l E Y).FullSubcategory) (a b : ℤ) :=
  (podIntegralPullbackShift l E g ((constructibleIntegralHom l E Y).obj P) (b - a)).inv ≫
    (constructibleIntegralPullback l E g).map (podIntegralHomShift l E P a b).hom ≫
    podIntegralHomComparison l E g (podIntegralShiftPair l E P a b) ≫
    (constructibleIntegralHom l E X).map
      (ObjectProperty.homMk
        (X := (podPairPullback (constructibleIntegralPullback l E g) _ _
          (podIntegralPairs_pullback l E g)).obj (podIntegralShiftPair l E P a b))
        (Y := podIntegralShiftPair l E
          ((podPairPullback (constructibleIntegralPullback l E g) _ _
            (podIntegralPairs_pullback l E g)).obj P) a b)
        (Prod.mkHom (podIntegralPullbackShift l E g P.obj.1.unop a).inv.op
          (podIntegralPullbackShift l E g P.obj.2 b).hom))

/-- The integral square and its actual localized image are equalities of arrows.
The rational equation uses the integral representatives of the cohomological
shifts; the localization CommShift maps identify these with the recorded shifts.
Source: node proof steps 6, 8, 11 and 14.
Proof: apply the fully faithful constructible inclusion to the first equality.
Insert the two normalization equations and cancel the complete-input maps.
The remaining equality is podIntegralReindexedHom_shift. Apply the localization
functor to obtain the second equality. The rational c and its transpose are
exactly these localized maps by podRationalHomComparison_laws, so this is their
shift square, including arbitrary localized arrows by additivity and balancing.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podIntegralRationalHomComparison_shift
    (P : (constructibleIntegralHomPairs l E Y).FullSubcategory) (a b : ℤ) :
    podIntegralShiftRouteLeft l E g P a b = podIntegralShiftRouteRight l E g P a b ∧
    (sfRationalConstructibleLocalization l E X).map (podIntegralShiftRouteLeft l E g P a b) =
      (sfRationalConstructibleLocalization l E X).map
        (podIntegralShiftRouteRight l E g P a b) := by
  sorry
end RestrictedShiftMaps

section CommonShiftImages
open GeneralAlgebraicallyClosedCoefficients AlgebraicallyClosedCoefficients
variable (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
  [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

/-- The common-stage shift square is the class of the rational shift square at
EVERY finite field of definition, followed by the prescribed shift comparisons.
Source: node proof steps 6 and 16.
Proof: represent a permitted pair at its finite coefficient compositum. The
common transpose normalization identifies its c with the rational c there;
common-stage shifts and inclusion CommShift are the prescribed stagewise ones.
Apply the stage inclusion to the rational square. Finite free scalar extension
preserves its evaluation and signed Hom representative formulas, so the same
square results at every larger field. Every common-stage input and arrow has
such a representative, which proves the asserted compatibility on that category.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podCommonHomComparison_shift
    (F : Index l Ω)
    (P : (constructibleIntegralHomPairs l (Coefficient.{u} l Ω F) Y).FullSubcategory)
    (a b : ℤ) :
    (inclusion F : Stage l Ω X F ⥤ generalAlgebraicallyClosedConstructibleCategory l Ω X).map
        ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω F) X).map
          (podIntegralShiftRouteLeft l (Coefficient.{u} l Ω F) g P a b)) =
      (inclusion F : Stage l Ω X F ⥤ generalAlgebraicallyClosedConstructibleCategory l Ω X).map
        ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω F) X).map
          (podIntegralShiftRouteRight l (Coefficient.{u} l Ω F) g P a b)) := by
  exact congrArg
    (fun f ↦ (inclusion F : Stage l Ω X F ⥤
      generalAlgebraicallyClosedConstructibleCategory l Ω X).map f)
    (podIntegralRationalHomComparison_shift l (Coefficient.{u} l Ω F) g P a b).2
end CommonShiftImages

end WeilConjectures
