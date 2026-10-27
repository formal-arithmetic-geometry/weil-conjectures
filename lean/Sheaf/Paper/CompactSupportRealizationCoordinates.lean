/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q66
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.Compactification.RefinementCategory
public import Sheaf.Paper.IntegralUniformCoefficient
public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness
public import Sheaf.Paper.CompactSupportReductionTower
public import Sheaf.Paper.IntegralCompactSupportUniformRestriction
public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.Paper.RingedCoefficientProjectionCocycle
public import Sheaf.SixFunctors.OpenTensorNormalization
public import Sheaf.Paper.CondensedERealization
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
public import Sheaf.Paper.CondensedFlatCoefficientCalculus
public import Sheaf.SixFunctors.IntegralSystemOperations
public import Sheaf.SixFunctors.IntegralSystemCanonicalBridge
public import Sheaf.Paper.CondensedCompactSupportProjection
public import Sheaf.SixFunctors.IntegralCompactificationSystemRealization
public import Sheaf.SixFunctors.IntegralCompactificationComparisonBridge
public import Sheaf.Paper.CompactSupportCondensedRealization
public import Sheaf.Paper.CompletedCoefficientPresentationTransport
public import Sheaf.Paper.SfCbcExtensionZeroCompletion
public import Sheaf.Paper.SfCbcCompactSupportCompositionLimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek
public import Sheaf.SixFunctors.GeneratorReductionStatement
import all Sheaf.SixFunctors.OpenReconstructionEffectivity
import Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus
import Sheaf.Paper.SfDerivedCompleteLegacyComparison
import all Sheaf.Paper.ConstantCoefficientObjectsConstructible
import all Sheaf.AlgebraicGeometry.ProEtaleOperations
import Sheaf.CategoryTheory.ScalarLocalizationSheafExact
import Sheaf.AlgebraicGeometry.ContinuousCoefficientLocalization
import Sheaf.AlgebraicGeometry.ContinuousCoefficientGeneralPullbackIso
import Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction

/-! # Coordinates for compact-support realization factor normalization

The original completed-ring support coordinates, section encodings, restriction
squares and scalar realization comparisons, separated for compilation.
Source: Bhatt--Scholze 6.7.6, 6.7.14 and 6.8.14(2), as interpreted by the original
factor-normalization construction and its unchanged proof docstrings.
(blueprint: lem-zl-compact-support-realization-coordinates-setup). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] HasDerivedCategory.ofHasKInjectiveResolutions
  _root_.instCategoryDerivedCategory
  CategoryTheory.Functor.leftDerivedFunctorIsoMapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctorIsoMapDerivedCategory
  AlgebraicGeometry.ProEtale.upperStarFromPoint
attribute [local irreducible] HasDerivedCategory.standard
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.rightDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Mod.monoidalCategory
  CategoryTheory.Sheaf.monoidalCategory
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open WeilConjectures
open scoped CategoryTheory.Obj
attribute [instance] CondensedERealization.At.encodingAdditive
  CondensedERealization.At.encodingInverseAdditive

namespace WeilConjectures.CompactSupportFactorNormalization
open IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The separately derived proper/open word. Source: node statement, paragraph 2
(blueprint: lem-zl-compact-support-realization-coordinates-setup). -/
def word {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    Integral l E X ⥤ Integral l E Y :=
  ringedOpen l E c.i ⋙ ringedPush l E c.g

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The proper coefficient projection is the transpose of the specified limit comparison.
Source: node proof Step 2
(blueprint: lem-zl-compact-support-realization-coordinates-setup). -/
def properReduction (o : Operations l E) (m : RealizationModel l E o)
    {X Y : Scheme.{u}} (g : X ⟶ Y) (D : Integral l E X) :=
  (calculus l E Y).reduction.map
      ((ringedPush l E g).map
        ((calculus l E X).adjunction.unit.app D) ≫
      (m.push l E g).inv.app ((calculus l E X).reduction.obj D)) ≫
    (calculus l E Y).adjunction.counit.app
      ((Operations.push l E o g).obj ((calculus l E X).reduction.obj D))

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The ordered coefficient comparison in the derived category of strict systems.
Source: node statement, definition of b
(blueprint: lem-zl-compact-support-realization-coordinates-setup). -/
def systemComparison (o : Operations l E) (m : RealizationModel l E o)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (K : Integral l E X) :=
  properReduction l E o m c.g ((ringedOpen l E c.i).obj K) ≫
    (Operations.push l E o c.g).map
      (GeneratorReduction.inverseOrZero ((m.openReduction l E c.i).app K))

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Reduction followed by the actual system proper/open word and total limit.
Source: node statement, definition of P_R
(blueprint: lem-zl-compact-support-realization-coordinates-setup). -/
def support (o : Operations l E) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) :=
  (calculus l E X).reduction ⋙ Operations.shriek l E o c.i ⋙
    Operations.push l E o c.g ⋙ coefficientSequenceLimit l E Y

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The specified comparison q=L(b)u, before finite evaluation.
Source: node statement, definition of q
(blueprint: lem-zl-compact-support-realization-coordinates-setup). -/
def integralComparison (o : Operations l E) (m : RealizationModel l E o)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (K : Integral l E X) :=
  (calculus l E Y).adjunction.unit.app ((word l E c).obj K) ≫
    (coefficientSequenceLimit l E Y).map (systemComparison l E o m c K)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The inverse coordinate map is constructed from the actual proper comparison,
open reduction mate and inverse reconstruction unit. Source: node proof Step 2
(blueprint: lem-zl-compact-support-realization-coordinates-setup). -/
def integralInverse (o : Operations l E) (m : RealizationModel l E o)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (K : Integral l E X) :=
  (m.push l E c.g).hom.app
      ((Operations.shriek l E o c.i).obj ((calculus l E X).reduction.obj K)) ≫
    (ringedPush l E c.g).map
      ((coefficientSequenceLimit l E c.Z).map ((m.openReduction l E c.i).app K) ≫
        GeneratorReduction.inverseOrZero ((calculus l E c.Z).adjunction.unit.app
          ((ringedOpen l E c.i).obj K)))

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The common finite cohomological/Tor window and compatible etale origins for
all input, open and proper/open intermediates. Source: node hypothesis paragraph
(blueprint: lem-zl-compact-support-realization-coordinates-setup). -/
def Domain (o : Operations l E) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (K : Integral l E X) (lo hi a b : ℤ) : Prop :=
  GeneratorReduction.Admissible l E (calculus l E X) K lo hi a b ∧
  GeneratorReduction.Admissible l E (calculus l E c.Z)
    ((ringedOpen l E c.i).obj K) lo hi a b ∧
  GeneratorReduction.Admissible l E (calculus l E Y) ((word l E c).obj K) lo hi a b ∧
  IntegralCompactificationBridge.systemWordDomain l E o c
    ((calculus l E X).reduction.obj K) lo hi a b

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem unit_map_transpose
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    {A : C} {B : D} (h : A ⟶ G.obj B) :
    adj.unit.app A ≫ G.map (F.map h ≫ adj.counit.app B) = h :=
  (adj.homEquiv A B).apply_symm_apply h

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem inverseOrZero_eq_inv
    {C : Type*} [Category C] [HasZeroMorphisms C]
    {A B : C} (h : A ⟶ B) [IsIso h] :
    GeneratorReduction.inverseOrZero h = inv h := by
  simp only [GeneratorReduction.inverseOrZero, dif_pos (inferInstance : IsIso h)]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem comparison_normalization
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [HasZeroMorphisms A] [HasZeroMorphisms B]
    {F : A ⥤ B} {G : B ⥤ A} (adj : F ⊣ G)
    {F' : C ⥤ D} {G' : D ⥤ C} (adj' : F' ⊣ G')
    (T : A ⥤ C) (P : B ⥤ D) (e : P ⋙ G' ≅ G ⋙ T)
    (K : A) (N : B) (r : N ⟶ F.obj K)
    (hu : IsIso (adj.unit.app K)) (hr : IsIso r) :
    let t := T.map (adj.unit.app K) ≫ e.inv.app (F.obj K)
    let b := (F'.map t ≫ adj'.counit.app (P.obj (F.obj K))) ≫
      P.map (GeneratorReduction.inverseOrZero r)
    let q := adj'.unit.app (T.obj K) ≫ G'.map b
    let v := e.hom.app N ≫
      T.map (G.map r ≫ GeneratorReduction.inverseOrZero (adj.unit.app K))
    IsIso q ∧ q ≫ v = 𝟙 _ ∧ v ≫ q = 𝟙 _ ∧
      F'.map q ≫ adj'.counit.app (P.obj N) = b := by
  let t := T.map (adj.unit.app K) ≫ e.inv.app (F.obj K)
  let b := (F'.map t ≫ adj'.counit.app (P.obj (F.obj K))) ≫
    P.map (GeneratorReduction.inverseOrZero r)
  let q := adj'.unit.app (T.obj K) ≫ G'.map b
  let v := e.hom.app N ≫
    T.map (G.map r ≫ GeneratorReduction.inverseOrZero (adj.unit.app K))
  change IsIso q ∧ q ≫ v = 𝟙 _ ∧ v ≫ q = 𝟙 _ ∧
    F'.map q ≫ adj'.counit.app (P.obj N) = b
  let i := T.mapIso (asIso (adj.unit.app K)) ≪≫ e.symm.app (F.obj K) ≪≫
    G'.mapIso (P.mapIso (asIso r).symm)
  have hq : q = i.hom := by
    dsimp only [q, b]
    rw [G'.map_comp, ← Category.assoc, unit_map_transpose]
    simp only [i, t, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom,
      asIso_hom, asIso_inv, inverseOrZero_eq_inv, Category.assoc]
  have hv : v = i.inv := by
    dsimp only [v]
    rw [inverseOrZero_eq_inv, T.map_comp]
    dsimp only [i, Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv, Iso.app_inv,
      asIso_hom, asIso_inv, Functor.comp_obj, Functor.comp_map]
    rw [← Category.assoc]
    exact congrArg (fun h => h ≫ T.map (inv (adj.unit.app K))) (e.hom.naturality r).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hq]
    infer_instance
  · rw [hq, hv]
    exact i.hom_inv_id
  · rw [hq, hv]
    exact i.inv_hom_id
  · exact (adj'.homEquiv _ _).symm_apply_apply b

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The integral inverse and transpose formulas, with naturality on the stated domain.
Source: node proof Steps 1--4
(blueprint: lem-zl-compact-support-realization-coordinates-setup).
Proof: proper reduction is the counit transpose of the fixed pullback/scalar square.
The strict open reduction mate is invertible. Completeness makes the reconstruction
unit invertible, so b and L(b)u are invertible. Naturality and the triangle identity
cancel L(e)u, giving exactly the displayed inverse. Generator reduction squares give
L(tau)q_B=q_C tau_int. For completed composition substitute the comparison bridge;
its inserted system counit cancels the intervening reconstruction unit. All equations
hold in the system adjunction before evaluation. -/
theorem integralComparison_normalization (o : Operations l E)
    (m : RealizationModel l E o) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (K : Integral l E X) (lo hi a b : ℤ)
    (_hK : Domain l E o c K lo hi a b) :
    IsIso (integralComparison l E o m c K) ∧
    integralComparison l E o m c K ≫ integralInverse l E o m c K = 𝟙 _ ∧
    integralInverse l E o m c K ≫ integralComparison l E o m c K = 𝟙 _ ∧
    (calculus l E Y).reduction.map (integralComparison l E o m c K) ≫
        (calculus l E Y).adjunction.counit.app
          ((Operations.push l E o c.g).obj
            ((Operations.shriek l E o c.i).obj ((calculus l E X).reduction.obj K))) =
      systemComparison l E o m c K := by
  have hr : IsIso ((m.openReduction l E c.i).app K) :=
    GeneratorReduction.fixedOpenReduction_isIso l E o m c.i K
  have hc : IntegralOnSlice.IsComplete l E c.Z none ((ringedOpen l E c.i).obj K) := by
    obtain ⟨D, hl⟩ := exists_coefficientTestDatum l
    exact ⟨D, hl, (sfDerivedComplete_iff_legacy l E c.Z D hl _).mp _hK.2.1.1.1.1⟩
  have hu : IsIso ((calculus l E c.Z).adjunction.unit.app
      ((ringedOpen l E c.i).obj K)) :=
    (purNormalizedReconstructionOfScheme l E c.Z (calculus l E c.Z)).2 _ hc
  exact comparison_normalization (calculus l E c.Z).adjunction
    (calculus l E Y).adjunction (ringedPush l E c.g) (Operations.push l E o c.g)
    (m.push l E c.g) ((ringedOpen l E c.i).obj K)
    ((Operations.shriek l E o c.i).obj ((calculus l E X).reduction.obj K))
    ((m.openReduction l E c.i).app K) hu hr

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The finite-field datum gives the characteristic of its algebraic closure.
Source: finite-field convention
(blueprint: lem-zl-compact-support-realization-coordinates-setup).
Proof: the cardinality p^a of k₀ gives characteristic p by the prime-power cardinality
theorem; an algebraic field extension has the same characteristic. -/
theorem geometricCharacteristic (D : FiniteFieldDatum.{u}) : ringChar D.k = D.p := by
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq)
  let : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  exact ringChar.eq D.k D.p

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Prime characteristic inherited from the finite-field datum.
Source: finite-field convention
(blueprint: lem-zl-compact-support-realization-coordinates-setup).
Proof: geometricCharacteristic identifies the characteristic with the recorded prime. -/
theorem geometricCharacteristic_prime (D : FiniteFieldDatum.{u}) :
    Fact (ringChar D.k).Prime := by
  exact ⟨(geometricCharacteristic D).symm ▸ D.prime⟩

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The distinct coefficient prime in the inherited characteristic convention.
Source: finite-field convention
(blueprint: lem-zl-compact-support-realization-coordinates-setup).
Proof: rewrite the characteristic by geometricCharacteristic and use the given inequality. -/
theorem geometricCharacteristic_ne (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p) :
    Fact (ringChar D.k ≠ l) := by
  exact ⟨by rw [geometricCharacteristic D]; exact Ne.symm hl⟩

attribute [instance] geometricCharacteristic_prime

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The characteristic convention as an inference rule from the original distinct-prime fact.
Source: finite-field convention
(blueprint: lem-zl-compact-support-realization-coordinates-setup).
Proof: geometricCharacteristic_ne applied to Fact.out gives the stated fact. -/
theorem geometricCharacteristic_ne_fact (D : FiniteFieldDatum.{u}) [Fact (l ≠ D.p)] :
    Fact (ringChar D.k ≠ l) := by
  exact geometricCharacteristic_ne l D (Fact.out : l ≠ D.p)

attribute [instance] geometricCharacteristic_ne_fact

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The published internal/section encoding at the normalized rational coefficient sheaf.
Source: coefficient-realization scalar-extension normalization, proof Step 5
(blueprint: lem-zl-compact-support-realization-coordinates-setup). -/
def encoding (W : Scheme.{u}) (A : CondensedERealization.At l E W) :=
  (CompactSupportCondensedRealization.encodingDerived l E W A).asEquivalence

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Integral-to-rational scalar realization in the actual internal module category.
Source: coefficient-realization scalar-extension normalization, proof Step 5
(blueprint: lem-zl-compact-support-realization-coordinates-setup). -/
def realize (W : Scheme.{u}) (A : CondensedERealization.At l E W) :=
  (purCoefficientModel l E W).inverse ⋙
    pbcDerivedExtend (A.integralIso.hom ≫ A.inclusion) ⋙ (encoding l E W A).inverse

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The right adjoint retains the actual restriction of the coefficient action.
Source: proof Step 5, canonical scalar adjunction
(blueprint: lem-zl-compact-support-realization-coordinates-setup). -/
def restrict (W : Scheme.{u}) (A : CondensedERealization.At l E W) :=
  (encoding l E W A).functor ⋙
    pbcDerivedRestrict (A.integralIso.hom ≫ A.inclusion) ⋙
      (purCoefficientModel l E W).functor

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The scalar adjunction uses the specified tensor-unit normalized adjunction.
Source: proof Step 5, canonical scalar adjunction
(blueprint: lem-zl-compact-support-realization-coordinates-setup). -/
def scalarAdjunction (W : Scheme.{u}) (A : CondensedERealization.At l E W) :
    realize l E W A ⊣ restrict l E W A :=
  ((purCoefficientModel l E W).symm.toAdjunction.comp
    (pbcDerivedScalarAdjunction (A.integralIso.hom ≫ A.inclusion))).comp
      (encoding l E W A).symm.toAdjunction

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The ordinary restriction functor, before deriving the sectionwise identity square.
Source: proof Step 5, coefficient and section presentations
(blueprint: lem-zl-compact-support-realization-coordinates-setup). -/
def ordinaryRestrict (W : Scheme.{u}) (A : CondensedERealization.At l E W) :=
  (CondensedERealization.moduleEncoding l E W A.sectionIso).functor ⋙
    pbcRestrict (A.integralIso.hom ≫ A.inclusion) ⋙ purOrdinaryCoefficientModel l E W

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Additivity of the explicit ordinary restriction composite.
Source: proof Step 5 (blueprint: lem-zl-compact-support-realization-coordinates-setup)..
Proof: Additivity is preserved by the section equivalence and the two exact scalar restrictions. -/
theorem ordinaryRestrictAdditive (W : Scheme.{u}) (A : CondensedERealization.At l E W) :
    (ordinaryRestrict l E W A).Additive := by
  dsimp only [ordinaryRestrict]
  infer_instance

attribute [instance] ordinaryRestrictAdditive

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Exactness of ordinary coefficient restriction.
Source: proof Step 5 (blueprint: lem-zl-compact-support-realization-coordinates-setup)..
Proof: The section equivalence and restriction functors preserve kernels and finite products. -/
theorem ordinaryRestrictLimits (W : Scheme.{u}) (A : CondensedERealization.At l E W) :
    PreservesFiniteLimits (ordinaryRestrict l E W A) := by
  dsimp only [ordinaryRestrict]
  infer_instance

attribute [instance] ordinaryRestrictLimits

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Exactness of ordinary coefficient restriction.
Source: proof Step 5 (blueprint: lem-zl-compact-support-realization-coordinates-setup)..
Proof: The section equivalence and restriction functors preserve cokernels and finite sums. -/
theorem ordinaryRestrictColimits (W : Scheme.{u}) (A : CondensedERealization.At l E W) :
    PreservesFiniteColimits (ordinaryRestrict l E W A) := by
  dsimp only [ordinaryRestrict]
  infer_instance

attribute [instance] ordinaryRestrictColimits

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Direct image preserves K-injectives since its inverse image is exact.
Source: proof Step 5 (blueprint: lem-zl-compact-support-realization-coordinates-setup).
Proof: the constant condensed coefficient inverse image is exact; its right adjoint
preserves K-injectives by the acyclic-Hom adjunction criterion. -/
theorem fieldPush_kInjective {X Y : Scheme.{u}} (g : X ⟶ Y) :
    Functor.PreservesKInjectiveComplexes
      (CondensedRing.lowerStar (Profinite.continuousCoefficientRingObj E) g) := by
  exact (CondensedRing.upperStarLowerStarAdjunction
    (Profinite.continuousCoefficientRingObj E) g).preservesKInjectiveComplexes

attribute [instance] fieldPush_kInjective

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The ordinary square is uniquely identity on every underlying section.
Source: proof Step 5; Bhatt--Scholze 6.8.14(2)
(blueprint: lem-zl-compact-support-realization-coordinates-setup).
Proof: all coefficient maps are precomposition on continuous functions, with the
specified residue and scalar normalizations. Both restriction/direct-image actions
therefore agree. Identity section maps are linear and natural and give inverse maps;
faithfulness of the underlying sheaf functor proves uniqueness. -/
theorem ordinaryRestrictionSquare_existsUnique {X Y : Scheme.{u}} (g : X ⟶ Y)
    (AX : CondensedERealization.At l E X) (AY : CondensedERealization.At l E Y) :
    ∃! e : CondensedRing.lowerStar (Profinite.continuousCoefficientRingObj E) g ⋙
        ordinaryRestrict l E Y AY ≅
      ordinaryRestrict l E X AX ⋙
        proEtaleRingModuleDirectImage g ((PurCompactSupport.completed l E).ring Y)
          ((PurCompactSupport.completed l E).ring X) ((PurCompactSupport.completed l E).pull g),
      ∀ (M : CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
          (CondensedERealization.Coefficient E X)) (V : Y.ProEtᵒᵖ)
        (x : ((ordinaryRestrict l E X AX ⋙
          proEtaleRingModuleDirectImage g ((PurCompactSupport.completed l E).ring Y)
            ((PurCompactSupport.completed l E).ring X)
            ((PurCompactSupport.completed l E).pull g)).obj M).val.obj V),
        ((e.hom.app M).val.app V).hom x = x := by
  sorry

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The uniquely normalized sectionwise restriction square.
Source: proof Step 5 (blueprint: lem-zl-compact-support-realization-coordinates-setup). -/
def ordinaryRestrictionSquare {X Y : Scheme.{u}} (g : X ⟶ Y)
    (AX : CondensedERealization.At l E X) (AY : CondensedERealization.At l E Y) :=
  (ordinaryRestrictionSquare_existsUnique l E g AX AY).exists.choose

private def uniformizerSection (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : Scheme.{u}) :
    ((AlgebraicGeometry.Scheme.integralCoefficientSheaf l W E).obj ⋙
      forget CommRingCat.{u + 1}).sections := by
  letI := coefficientExtensionNormedField l E
  exact ⟨fun U ↦ ContinuousMap.const U.unop.left
    (ULift.up.{u + 1, u} (Padic.coefficientExtensionUniformizer l E)), fun _ ↦ rfl⟩

private def continuousLocalizationPresheafChart (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : Scheme.{u}) :
    ringedLocalizationRingPresheafOfUniverses
        (AlgebraicGeometry.Scheme.integralCoefficientSheaf l W E)
        (uniformizerSection l E W) ≅
      (letI := coefficientExtensionNormedField l E
       localizedContinuousMapPresheaf W
         (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))
         (ULift.up.{u + 1, u} (Padic.coefficientExtensionUniformizer l E))) := by
  letI := coefficientExtensionNormedField l E
  refine NatIso.ofComponents (fun _ ↦ Iso.refl _) ?_
  intro U V f
  simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  apply CommRingCat.hom_ext
  apply IsLocalization.ringHom_ext
    (S := Localization.Away (ContinuousMap.const U.unop.left
      (ULift.up.{u + 1, u} (Padic.coefficientExtensionUniformizer l E))))
    (Submonoid.powers (ContinuousMap.const U.unop.left
      (ULift.up.{u + 1, u} (Padic.coefficientExtensionUniformizer l E))))
  ext a
  simp only [ringedLocalizationRingPresheafOfUniverses,
    ringedSectionLocalizationMapOfUniverses, localizedContinuousMapPresheaf,
    localizedContinuousMapRestriction, IsLocalization.Away.map, RingHom.comp_apply]
  rfl

private def continuousLocalizationChart (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : Scheme.{u}) :
    ringedLocalizationRingOfUniverses (AlgebraicGeometry.Scheme.integralCoefficientSheaf l W E)
        (uniformizerSection l E W) ≅ integralCoefficientLocalization l W E :=
  (presheafToSheaf (ProEt.topology W) CommRingCat.{u + 1}).mapIso
    (continuousLocalizationPresheafChart l E W)

private theorem continuous_inclusion_factor (W : Scheme.{u})
    (A : CondensedERealization.At l E W) :
    ∃ e : ringedLocalizationRingOfUniverses
        (AlgebraicGeometry.Scheme.integralCoefficientSheaf l W E)
        (uniformizerSection l E W) ≅ rationalCoefficientSheaf l W E,
      ringedLocalizationRingUnitOfUniverses
        (AlgebraicGeometry.Scheme.integralCoefficientSheaf l W E)
        (uniformizerSection l E W) ≫ e.hom = A.inclusion := by
  obtain ⟨b, hb⟩ := continuousCoefficientLocalization l E W
  refine ⟨continuousLocalizationChart l E W ≪≫ b, ?_⟩
  apply Sheaf.hom_ext
  ext U a
  apply rationalCoefficientValue_ext l E W U
  intro x
  refine Eq.trans ?_ (A.inclusion_normalization U.unop a x).symm
  change rationalCoefficientValue l E W U
    (b.hom.hom.app U
      (((ringedLocalizationRingUnitOfUniverses
        (AlgebraicGeometry.Scheme.integralCoefficientSheaf l W E)
        (uniformizerSection l E W) ≫ (continuousLocalizationChart l E W).hom).hom.app U) a)) x = _
  let R := AlgebraicGeometry.Scheme.integralCoefficientSheaf l W E
  let t := uniformizerSection l E W
  let P := ringedLocalizationRingPresheafOfUniverses R t
  let num := ((ringedLocalizationRingPresheafUnitOfUniverses R t).app U).hom a
  have hn := ConcreteCategory.congr_hom
    (congr_app (toSheafify_naturality (ProEt.topology W)
      (continuousLocalizationPresheafChart l E W).hom) U) num
  change rationalCoefficientValue l E W U (b.hom.hom.app U
    (((presheafToSheaf (ProEt.topology W) CommRingCat.{u + 1}).map
      (continuousLocalizationPresheafChart l E W).hom).hom.app U
      ((toSheafify (ProEt.topology W) P).app U num))) x = _
  simp only [NatTrans.comp_app, CommRingCat.comp_apply] at hn
  erw [← hn]
  exact hb U a x

private theorem localization_restrict_kInjective (W : Scheme.{u})
    (R : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (s : (R.obj ⋙ forget CommRingCat.{u + 1}).sections) :
    (pbcRestrict (ringedLocalizationRingUnitOfUniverses R s)).PreservesKInjectiveComplexes := by
  obtain ⟨F, hobj, hmap, hAdd, hLim, hColim, _⟩ :=
    scalarLocalization_sheaf_exact (ProEt.topology W) R s
  have : F.Additive := hAdd
  have : PreservesFiniteLimits F := hLim
  have : PreservesFiniteColimits F := hColim
  obtain ⟨_, _, ha⟩ := SheafOfModules.sheafRingCoefficientOrdinaryAdjunction
    (ringedLocalizationRingUnitOfUniverses R s)
  obtain ⟨adj, _⟩ := ha F hobj hmap
  exact adj.preservesKInjectiveComplexes

private theorem iso_restrict_kInjective (W : Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (e : R ≅ S) :
    (pbcRestrict e.hom).PreservesKInjectiveComplexes := by
  have : (pbcRestrict e.hom).IsEquivalence :=
    inferInstanceAs
      (proEtaleScalarEquivalence W ((adicLisseForget W).mapIso e)).functor.IsEquivalence
  infer_instance

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The ordinary restriction is exact and preserves K-injective complexes because its
left adjoint is localization of coefficients followed by exact equivalences.
Source: proof Steps 5--7 (blueprint: lem-zl-compact-support-realization-coordinates-setup).
Proof: inverting the uniformizer is flat. Its scalar adjunction has exact left adjoint.
The section and completed coefficient equivalences are exact. Their composite left
adjoint is exact, so restriction preserves injectives and K-injective complexes. -/
theorem ordinaryRestrict_kInjective (W : Scheme.{u})
    (A : CondensedERealization.At l E W) :
    (ordinaryRestrict l E W A).PreservesKInjectiveComplexes := by
  obtain ⟨e, he⟩ := continuous_inclusion_factor l E W A
  have : (pbcRestrict (ringedLocalizationRingUnitOfUniverses
      (AlgebraicGeometry.Scheme.integralCoefficientSheaf l W E)
      (uniformizerSection l E W))).PreservesKInjectiveComplexes :=
    localization_restrict_kInjective W _ _
  have : (pbcRestrict e.hom).PreservesKInjectiveComplexes := iso_restrict_kInjective W e
  have : (pbcRestrict A.inclusion).PreservesKInjectiveComplexes :=
    Functor.preservesKInjectiveComplexes_of_iso
      (pbcRestrictComp _ _ _ he)
  have : (pbcRestrict A.integralIso.hom).PreservesKInjectiveComplexes :=
    iso_restrict_kInjective W A.integralIso
  have : (pbcRestrict (A.integralIso.hom ≫ A.inclusion)).PreservesKInjectiveComplexes :=
    Functor.preservesKInjectiveComplexes_of_iso (pbcRestrictComp _ _ _ rfl)
  have : (purOrdinaryCoefficientModel l E W).PreservesKInjectiveComplexes :=
    iso_restrict_kInjective W (purCoefficientIso l E W).symm
  dsimp only [ordinaryRestrict]
  infer_instance

attribute [instance] ordinaryRestrict_kInjective

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The derived restriction model is the standard exact-functor presentation.
Source: proof Step 5 (blueprint: lem-zl-compact-support-realization-coordinates-setup). -/
def restrictionModel (W : Scheme.{u}) (A : CondensedERealization.At l E W) :
    (ordinaryRestrict l E W A).rightDerivedFunctor ≅ restrict l E W A :=
  (ordinaryRestrict l E W A).rightDerivedFunctorIsoMapDerivedCategory ≪≫
    Functor.mapDerivedCategoryCompIso _ _ ≪≫
      Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryCompIso _ _)

/-- The whole-derived restriction square, derived from identity on sections, with the
canonical right-derived composition units. No evaluated-arrow characterization is used.
Source: proof Step 5 (blueprint: lem-zl-compact-support-realization-coordinates-setup). -/
def restrictionSquare {X Y : Scheme.{u}} (g : X ⟶ Y)
    (AX : CondensedERealization.At l E X) (AY : CondensedERealization.At l E Y) :
    (CondensedRing.lowerStar (Profinite.continuousCoefficientRingObj E) g).rightDerivedFunctor ⋙
        restrict l E Y AY ≅
      restrict l E X AX ⋙ ringedPush l E g :=
  Functor.isoWhiskerLeft _ (restrictionModel l E Y AY).symm ≪≫
    (Functor.rightDerivedFunctorCompIso _ _).symm ≪≫
      Functor.rightDerivedFunctorNatIso (ordinaryRestrictionSquare l E g AX AY) ≪≫
        Functor.rightDerivedFunctorCompIso _ _ ≪≫
          Functor.isoWhiskerRight (restrictionModel l E X AX) _

/-- Pullback/scalar balancing is the unique left-adjoint comparison conjugate to the
actual restriction/direct-image square.
Source: proof Step 5 (blueprint: lem-zl-compact-support-realization-coordinates-setup). -/
def realizationPull {X Y : Scheme.{u}} (g : X ⟶ Y)
    (AX : CondensedERealization.At l E X) (AY : CondensedERealization.At l E Y) :
    ringedPull l E g ⋙ realize l E X AX ≅
      realize l E Y AY ⋙
        (CondensedRing.upperStar (Profinite.continuousCoefficientRingObj E) g).leftDerivedFunctor :=
  (((ringedAdj l E g).comp (scalarAdjunction l E X AX)).ofNatIsoRight
    (restrictionSquare l E g AX AY).symm).leftAdjointUniq
      ((scalarAdjunction l E Y AY).comp
        (CondensedRing.derivedUpperStarLowerStarAdjunction
          (Profinite.continuousCoefficientRingObj E) g))

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The proper realization factor is precisely the geometric counit mate of the fixed
pullback/scalar balancing square.
Source: proof Step 5 (blueprint: lem-zl-compact-support-realization-coordinates-setup). -/
def properRealization {X Y : Scheme.{u}} (g : X ⟶ Y)
    (AX : CondensedERealization.At l E X) (AY : CondensedERealization.At l E Y) :=
  (mateEquiv (ringedAdj l E g)
    (CondensedRing.derivedUpperStarLowerStarAdjunction
      (Profinite.continuousCoefficientRingObj E) g)
    (TwoSquare.mk _ _ _ _ (realizationPull l E g AX AY).inv)).natTrans

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The inverse open scalar factor is the adjunct of the actual open unit.
Source: proof Steps 5 and 8
(blueprint: lem-zl-compact-support-realization-coordinates-setup). -/
def openRealizationInverse {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (AX : CondensedERealization.At l E X) (AZ : CondensedERealization.At l E Z) :=
  ((mateEquiv (ringedOpenAdj l E j)
    (CompactSupportCondensedRealization.fieldOpenAdjunction
      (Profinite.continuousCoefficientRingObj E) j)).symm
      (TwoSquare.mk _ _ _ _ (realizationPull l E j AX AZ).hom)).natTrans

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The open factor in the forward scalar direction. Its inverse is uniquely fixed by
the open unit; the normalization theorem proves that it is invertible.
Source: proof Step 5 (blueprint: lem-zl-compact-support-realization-coordinates-setup). -/
def openRealization {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (AX : CondensedERealization.At l E X) (AZ : CondensedERealization.At l E Z)
    (K : Integral l E X) :=
  GeneratorReduction.inverseOrZero ((openRealizationInverse l E j AX AZ).app K)



set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The scalar normalization identifies the real scalar construction with J on lattices.
Source: proof Step 5 (blueprint: lem-zl-compact-support-realization-coordinates-setup). -/
def latticeComparison (W : Scheme.{u}) (A : CondensedERealization.At l E W) :
    ObjectProperty.ι (PbcIsBoundedConstructibleComplete W (pbcIntegralDatum l E)) ⋙
        (purCoefficientModel l E W).functor ⋙ realize l E W A ≅
      pbcRationalization W (pbcIntegralDatum l E) (pbcUniformizer l E) ⋙
        A.realization.functor ⋙ (boundedConstructible (CondensedERealization.Coefficient E W)).ι :=
  Functor.isoWhiskerLeft _
      (Functor.isoWhiskerRight (purCoefficientModel l E W).unitIso.symm
        (pbcDerivedExtend (A.integralIso.hom ≫ A.inclusion) ⋙ (encoding l E W A).inverse)) ≪≫
    Functor.isoWhiskerLeft _ (Functor.leftUnitor _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Iso.compInverseIso (H := encoding l E W A)
      (A.scalarExtension.symm ≪≫
        (Functor.associator _ _ _).symm ≪≫
        (Functor.associator _ _ _).symm)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The fixed support-system presentation is the canonical bridge's proper/open paste.
Source: proof Steps 2 and 5
(blueprint: lem-zl-compact-support-realization-coordinates-setup). -/
def systemPresentation (o : Operations l E) (b : CanonicalBridge l E o)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    Operations.shriek l E o c.i ⋙ Operations.push l E o c.g ≅
      CompactSupportCondensedRealization.systemSupport l E c :=
  Functor.isoWhiskerRight (b.shriek l E c.i) _ ≪≫
    Functor.isoWhiskerLeft _ (b.push l E c.g)

end WeilConjectures.CompactSupportFactorNormalization
