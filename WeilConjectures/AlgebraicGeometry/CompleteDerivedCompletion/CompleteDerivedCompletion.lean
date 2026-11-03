/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.CategoryTheory.SmoothBaseChange.TowerDerivedEvaluationNormalization
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.CategoryTheory.ExactProductsRoos.ExactProductsRoosComparisonSupplement

public import Mathlib.CategoryTheory.Monoidal.Mon
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
public import Mathlib.Topology.Bases
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone
public import WeilConjectures.CategoryTheory.Monoidal.Closed.UnitEnd
public import Mathlib.CategoryTheory.Center.Linear
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
public import WeilConjectures.NumberTheory.Padics.ContinuousUniformizerDivision
public import Mathlib.Topology.Algebra.Order.Field
public import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
public import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.BifunctorShift
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Conj
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Complete
public import WeilConjectures.Algebra.Homology.ScalarTowerProductFibre
public import WeilConjectures.Algebra.Homology.SixFunctors.TermwiseConeHomotopyExact
public import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.InternalQuotientPrincipalConeComparison
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.InternalRoosOutputComplete
public import WeilConjectures.AlgebraicGeometry.ProEtale.RepleteAddCommGrp
public import WeilConjectures.CategoryTheory.AdditiveConeFamilyComparison
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapDualizable
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryMonoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.AssociatorShift
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Dualizable
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableProjectiveUnit
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import WeilConjectures.CategoryTheory.Flat.FlatConstantTensorProZeroConesSupplement
public import WeilConjectures.CategoryTheory.ModuleObjects.KFlatScalarTower.InternalKFlatScalarTowerRealizationSupplement
public import WeilConjectures.CategoryTheory.ModuleObjects.SequentialLimitEpi
public import WeilConjectures.CategoryTheory.UnboundedExactTower.UnboundedExactAdjunctionSquare
public import WeilConjectures.ProEtaleCoefficients.DerivedNakayamaResolution
public import WeilConjectures.ProperBaseChange.RingedStrictTowerHomotopyLimitIndependentCoefficients

/-!
# Towers and the derived completion

Source: literature/blueprint/latest/blueprint/sec-proper-base-change/
sk-prop-pbc-complete/det-pbc-complete-derived-completion.md
(blueprint: det-pbc-complete-derived-completion).

The natural index `n` denotes the positive exponent `n + 1`. The reduction tower is
constructed as a cone in complexes of towers. Its source has transition multiplication
by the uniformizer and its target is constant. Thus its transition is precisely
`(π, 1)`, including on complexes with torsion. Localization defines the derived
reduction functor; no choice of unrelated levelwise derived arrows is made.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.modulesMonoidal AdicCompletion.modulesSymmetric AdicCompletion.modulesClosed
  AdicCompletion.modulesMonoidalPreadditive AdicCompletion.modulesDerived
  AdicCompletion.finiteRingMonoidalObject AdicCompletion.finiteRingCommutative
  AdicCompletion.finiteModulesDerived
  AdicCompletion.modulesProducts AdicCompletion.complexProducts

namespace CompleteDerivedCompletion

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The category of inverse towers of integral modules; level `n` means exponent `n+1`.
Source: blueprint Notation 1 (blueprint: det-pbc-complete-derived-completion). -/
abbrev Tow (T : Scheme.{u}) := ℕᵒᵖ ⥤ AdicCompletion.Modules l E T

/-- Grothendieckness of the actual tower category, with its inherited abelian structure.
Source: blueprint Assertion 1 (blueprint: det-pbc-complete-derived-completion).
Proof: identify internal modules with sheaves of modules, then use the small-diagram
Grothendieck theorem. Kernels, cokernels and filtered colimits are computed levelwise;
the coproduct of the free diagrams on a generator is a generator. -/
@[instance] theorem towerGrothendieck (T : Scheme.{u}) :
    IsGrothendieckAbelian.{u+1} (Tow l E T) := by
  let A := AdicCompletion.Modules l E T
  let : IsGrothendieckAbelian.{u+1} A := inferInstance
  let : HasColimitsOfSize.{u+1, u+1} A := inferInstance
  let : HasColimitsOfSize.{0, u+1} A := hasColimitsOfSizeShrink.{0, u+1, u+1, u+1} A
  change IsGrothendieckAbelian.{u+1} (ℕᵒᵖ ⥤ A)
  have ht (K : Type (u+1)) [SmallCategory K] : IsGrothendieckAbelian.{u+1} (K ⥤ A) := by
    let (_a _b : K) : HasColimitsOfShape (Discrete (_a ⟶ _b)) A :=
      HasColimitsOfShape.of_small.{u+1, u+1} A _
    let : HasColimitsOfSize.{0, u+1} (K ⥤ A) := inferInstance
    let : HasColimitsOfShape (Discrete K) (K ⥤ A) :=
      HasColimitsOfShape.of_small.{u+1, u+1} (K ⥤ A) _
    let G := separator A
    have hG := isSeparator_separator A
    have hS : ObjectProperty.IsSeparating
        (.ofObj fun j : K ↦ (evaluationLeftAdjoint A j).obj G) := by
      intro F F' f g hfg
      apply NatTrans.ext
      funext j
      apply hG.def
      intro a
      let adj := evaluationAdjunctionRight A j
      apply (adj.homEquiv G F').symm.injective
      have h := hfg _ (ObjectProperty.ofObj_apply _ j) ((adj.homEquiv G F).symm a)
      exact (adj.homEquiv_naturality_right_symm a f).trans
        (h.trans (adj.homEquiv_naturality_right_symm a g).symm)
    let : HasCoproduct (fun j : K ↦ (evaluationLeftAdjoint A j).obj G) :=
      HasColimitsOfShape.has_colimit _
    let : HasSeparator (K ⥤ A) :=
      ⟨∐ (fun j : K ↦ (evaluationLeftAdjoint A j).obj G), hS.isSeparator_coproduct⟩
    let : HasFilteredColimitsOfSize.{u+1, u+1} (K ⥤ A) := ⟨fun _ _ _ ↦ inferInstance⟩
    let : AB5OfSize.{u+1, u+1} (K ⥤ A) := ⟨fun _ _ _ ↦ inferInstance⟩
    exact {}
  let : IsGrothendieckAbelian.{u+1} (AsSmall.{u+1} ℕᵒᵖ ⥤ A) := ht (AsSmall.{u+1} ℕᵒᵖ)
  exact IsGrothendieckAbelian.of_equivalence
    (Equivalence.congrLeft (AsSmall.equiv : ℕᵒᵖ ≌ AsSmall.{u+1} ℕᵒᵖ).symm)

/-- The unbounded derived category of towers, with small Hom universe `u+1`.
Source: blueprint Notation 1 (blueprint: det-pbc-complete-derived-completion). -/
abbrev DTow (T : Scheme.{u}) := DerivedCategory.{u+1} (Tow l E T)

/-- Exact evaluation of module towers.
Source: blueprint Notation 1 (blueprint: det-pbc-complete-derived-completion). -/
abbrev ev (T : Scheme.{u}) (n : ℕ) :=
  (evaluation ℕᵒᵖ (AdicCompletion.Modules l E T)).obj (op n)

/-- Evaluation on the derived category of towers, induced by exact evaluation.
Source: blueprint Assertion 2 (blueprint: det-pbc-complete-derived-completion). -/
abbrev dev (T : Scheme.{u}) (n : ℕ) := (ev l E T n).mapDerivedCategory

/-- The constant tower functor.
Source: blueprint Notation 1 (blueprint: det-pbc-complete-derived-completion). -/
abbrev constant (T : Scheme.{u}) := Functor.const ℕᵒᵖ (C := AdicCompletion.Modules l E T)

/-- The constant functor on unbounded derived categories.
Source: blueprint Notation 1 (blueprint: det-pbc-complete-derived-completion). -/
abbrev dconstant (T : Scheme.{u}) := (constant l E T).mapDerivedCategory

/-- The ordinary inverse limit of module towers, right adjoint to the constant functor.
Source: blueprint Notation 1 (blueprint: det-pbc-complete-derived-completion). -/
abbrev inverseLimit (T : Scheme.{u}) : Tow l E T ⥤ AdicCompletion.Modules l E T := lim

/-- Additivity of ordinary inverse limit from the additive constant-limit adjunction.
Source: blueprint Notation 1 (blueprint: det-pbc-complete-derived-completion).
Proof: the constant functor is additive, and an additive left adjoint has an additive
right adjoint. Apply this to Mathlib's constant-limit adjunction. -/
@[instance] theorem inverseLimit_additive (T : Scheme.{u}) :
    (inverseLimit l E T).Additive := by
  exact (constLimAdj : constant l E T ⊣ inverseLimit l E T).right_adjoint_additive

/-- The total right derived inverse-limit functor, constructed by K-injective resolutions.
Source: blueprint Notation 1 (blueprint: det-pbc-complete-derived-completion). -/
abbrev rlim (T : Scheme.{u}) := (inverseLimit l E T).rightDerivedFunctor

/-- The canonical derived constant-limit adjunction.
Source: blueprint Notation 4 (blueprint: det-pbc-complete-derived-completion). -/
def constantLimitAdjunction (T : Scheme.{u}) : dconstant l E T ⊣ rlim l E T :=
  (constLimAdj : constant l E T ⊣ inverseLimit l E T).mapDerivedCategoryRightDerivedAdjunction

/-- Levelwise ordinary pullback of module towers.
Source: blueprint Notation 2 (blueprint: det-pbc-complete-derived-completion). -/
abbrev pull {T T' : Scheme.{u}} (f : T' ⟶ T) : Tow l E T ⥤ Tow l E T' :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj
    (CondensedRing.upperStar (DerivedNakayama.integerRing l E) f)

/-- Levelwise ordinary pushforward of module towers.
Source: blueprint Notation 2 (blueprint: det-pbc-complete-derived-completion). -/
abbrev push {T T' : Scheme.{u}} (f : T' ⟶ T) : Tow l E T' ⥤ Tow l E T :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj
    (CondensedRing.lowerStar (DerivedNakayama.integerRing l E) f)

/-- Exact module pullback on the derived category; no resolution is needed.
Source: blueprint Notation 2 (blueprint: det-pbc-complete-derived-completion). -/
abbrev dpullModule {T T' : Scheme.{u}} (f : T' ⟶ T) :=
  (CondensedRing.upperStar (DerivedNakayama.integerRing l E) f).mapDerivedCategory

/-- The existing total right derived module direct image.
Source: blueprint Assertion 3 (blueprint: det-pbc-complete-derived-completion). -/
abbrev rpushModule {T T' : Scheme.{u}} (f : T' ⟶ T) :=
  (CondensedRing.lowerStar (DerivedNakayama.integerRing l E) f).rightDerivedFunctor

/-- Exact pullback on derived towers.
Source: blueprint Notation 2 (blueprint: det-pbc-complete-derived-completion). -/
abbrev dpull {T T' : Scheme.{u}} (f : T' ⟶ T) := (pull l E f).mapDerivedCategory

/-- Total right derived pushforward on the derived category of towers.
Source: blueprint Notation 2 (blueprint: det-pbc-complete-derived-completion). -/
abbrev rpush {T T' : Scheme.{u}} (f : T' ⟶ T) := (push l E f).rightDerivedFunctor

/-- The canonical exact-pullback/derived-pushforward module adjunction.
Source: blueprint Assertion 3 (blueprint: det-pbc-complete-derived-completion). -/
def moduleAdjunction {T T' : Scheme.{u}} (f : T' ⟶ T) :
    dpullModule l E f ⊣ rpushModule l E f :=
  (CondensedRing.upperStarLowerStarAdjunction (DerivedNakayama.integerRing l E) f)
    |>.mapDerivedCategoryRightDerivedAdjunction

/-- The canonical exact-pullback/derived-pushforward tower adjunction.
Source: blueprint Assertion 3 (blueprint: det-pbc-complete-derived-completion). -/
def towerAdjunction {T T' : Scheme.{u}} (f : T' ⟶ T) : dpull l E f ⊣ rpush l E f :=
  ((CondensedRing.upperStarLowerStarAdjunction (DerivedNakayama.integerRing l E) f)
    |>.whiskerRight ℕᵒᵖ).mapDerivedCategoryRightDerivedAdjunction

/-- The canonical pullback-evaluation comparison from exact localization.
Source: blueprint Assertion 3 (blueprint: det-pbc-complete-derived-completion). -/
def pullEvaluation {T T' : Scheme.{u}} (f : T' ⟶ T) (n : ℕ) :
    dpull l E f ⋙ dev l E T' n ≅ dev l E T n ⋙ dpullModule l E f :=
  towerDerivedEvaluationInterchange
    (CondensedRing.upperStar (DerivedNakayama.integerRing l E) f) (op n)

/-- Multiplication by the specified coefficient uniformizer on the regular module.
This choice is determined uniquely: the first property of the cited resolution theorem
specifies its value on every section and every point, so it is not a choice from a bare
existence assertion. Source: blueprint Notation 3 and derived Nakayama resolution
(blueprint: det-pbc-complete-derived-completion). -/
def uniformizer : End (Mod.regular (DerivedNakayama.integerRing l E)) :=
  (DerivedNakayama.derived_nakayama_resolution l E).choose

/-- Scalar multiplication by the uniformizer on integral module sheaves.
Source: blueprint Notation 3 (blueprint: det-pbc-complete-derived-completion). -/
abbrev scalar (T : Scheme.{u}) :=
  DerivedNakayama.scalarOnModules l E T (uniformizer l E)

/-- The source of the reduction power map: the same module at every level with
uniformizer transitions. Source: blueprint Notation 3
(blueprint: det-pbc-complete-derived-completion). -/
def scalarTower (T : Scheme.{u}) : AdicCompletion.Modules l E T ⥤ Tow l E T :=
  (Functor.ofOpSequence (X := fun _ : ℕ ↦ 𝟭 (AdicCompletion.Modules l E T))
    (fun _ ↦ scalar l E T)).flip

/-- The scalar tower functor is additive.
Source: blueprint Notation 3 (blueprint: det-pbc-complete-derived-completion).
Proof: every component of its map is the original module morphism; addition is
levelwise in a functor category. -/
@[instance] theorem scalarTower_additive (T : Scheme.{u}) : (scalarTower l E T).Additive := by
  refine ⟨?_⟩
  intro M N f g
  apply NatTrans.ext
  funext n
  rfl

/-- The power components commute with the scalar-tower transition.
Source: blueprint Notation 3 (blueprint: det-pbc-complete-derived-completion).
Proof: at level n the equation is π^(n+2) = π · π^(n+1), the power identity. -/
theorem powerMap_condition (T : Scheme.{u}) (M : AdicCompletion.Modules l E T) (n : ℕ) :
    ((scalarTower l E T).obj M).map (homOfLE (Nat.le_succ n)).op ≫
        End.asHom ((End.of ((scalar l E T).app M)) ^ (n+1)) =
      End.asHom ((End.of ((scalar l E T).app M)) ^ (n+1+1)) ≫
        ((constant l E T).obj M).map (homOfLE (Nat.le_succ n)).op := by
  change ((Functor.ofOpSequence (X := fun _ : ℕ ↦ 𝟭 (AdicCompletion.Modules l E T))
    (fun _ ↦ scalar l E T)).map (homOfLE (Nat.le_succ n)).op).app M ≫
      End.asHom ((End.of ((scalar l E T).app M)) ^ (n+1)) = _
  rw [Functor.ofOpSequence_map_homOfLE_succ]
  change End.asHom ((End.of ((scalar l E T).app M)) ^ (n+1) *
    End.of ((scalar l E T).app M)) = _
  rw [← pow_succ]
  rfl

/-- The power map on one module, as an actual morphism of towers.
Source: blueprint Notation 3 (blueprint: det-pbc-complete-derived-completion). -/
def powerMapApp (T : Scheme.{u}) (M : AdicCompletion.Modules l E T) :
    (scalarTower l E T).obj M ⟶ (constant l E T).obj M :=
  NatTrans.ofOpSequence
    (fun n ↦ End.asHom ((End.of ((scalar l E T).app M)) ^ (n+1)))
    (powerMap_condition l E T M)

/-- Naturality of the power map in the module.
Source: blueprint Notation 3 (blueprint: det-pbc-complete-derived-completion).
Proof: naturality of the scalar action implies naturality of all its powers. -/
theorem powerMap_naturality (T : Scheme.{u})
    {M N : AdicCompletion.Modules l E T} (f : M ⟶ N) :
    (scalarTower l E T).map f ≫ powerMapApp l E T N =
      powerMapApp l E T M ≫ (constant l E T).map f := by
  apply NatTrans.ext
  funext n
  change f ≫ End.asHom ((End.of ((scalar l E T).app N)) ^ (n.unop+1)) =
    End.asHom ((End.of ((scalar l E T).app M)) ^ (n.unop+1)) ≫ f
  have h (k : ℕ) :
      f ≫ End.asHom ((End.of ((scalar l E T).app N)) ^ k) =
        End.asHom ((End.of ((scalar l E T).app M)) ^ k) ≫ f := by
    induction k with
    | zero => simp
    | succ k ih =>
      change f ≫ ((scalar l E T).app N ≫
        End.asHom ((End.of ((scalar l E T).app N)) ^ k)) =
          ((scalar l E T).app M ≫
            End.asHom ((End.of ((scalar l E T).app M)) ^ k)) ≫ f
      have hs : f ≫ (scalar l E T).app N = (scalar l E T).app M ≫ f :=
        (scalar l E T).naturality f
      rw [← Category.assoc, hs, Category.assoc, ih, Category.assoc]
  exact h _

/-- The power map from the scalar tower to the constant tower.
Source: blueprint Notation 3 (blueprint: det-pbc-complete-derived-completion). -/
def powerMap (T : Scheme.{u}) : scalarTower l E T ⟶ constant l E T where
  app M := powerMapApp l E T M
  naturality _ _ f := powerMap_naturality l E T f

/-- The strict reduction power map on complexes of towers.
Source: blueprint Notation 3 (blueprint: det-pbc-complete-derived-completion). -/
abbrev complexPowerMap (T : Scheme.{u}) :=
  NatTrans.mapHomologicalComplex (powerMap l E T) (.up ℤ)

/-- Identity maps induce the identity on the strict cone tower.
Source: blueprint Notation 3 (blueprint: det-pbc-complete-derived-completion).
Proof: both functors in the defining square send the identity to the identity;
apply the standard mapping-cone identity formula. -/
theorem strictRed_map_id (T : Scheme.{u})
    (M : CochainComplex (AdicCompletion.Modules l E T) ℤ) :
    CochainComplex.mappingCone.map ((complexPowerMap l E T).app M)
      ((complexPowerMap l E T).app M)
      (((scalarTower l E T).mapHomologicalComplex (.up ℤ)).map (𝟙 M))
      (((constant l E T).mapHomologicalComplex (.up ℤ)).map (𝟙 M))
      ((complexPowerMap l E T).naturality (𝟙 M)).symm = 𝟙 _ := by
  exact CochainComplex.mappingCone.map_id _

/-- The strict reduction functor, with cone transitions (π,1), on arbitrary complexes.
The cone is taken in complexes of towers, so it includes all coherence automatically.
Source: blueprint Notation 3 (blueprint: det-pbc-complete-derived-completion). -/
def strictRed (T : Scheme.{u}) :
    CochainComplex (AdicCompletion.Modules l E T) ℤ ⥤ CochainComplex (Tow l E T) ℤ where
  obj M := CochainComplex.mappingCone ((complexPowerMap l E T).app M)
  map {M N} f := CochainComplex.mappingCone.map _ _
    (((scalarTower l E T).mapHomologicalComplex (.up ℤ)).map f)
    (((constant l E T).mapHomologicalComplex (.up ℤ)).map f)
    ((complexPowerMap l E T).naturality f).symm
  map_id M := strictRed_map_id l E T M
  map_comp f g := by
    simp only [Functor.map_comp]
    exact CochainComplex.mappingCone.map_comp _ _ _ _ _
      ((complexPowerMap l E T).naturality f).symm _ _
      ((complexPowerMap l E T).naturality g).symm

/-- Reduction inverts quasi-isomorphisms before passage to derived towers.
Source: blueprint Notation 3 (blueprint: det-pbc-complete-derived-completion).
Proof: exact evaluation identifies the cone at n with Cone(π^(n+1)); a quasi-isomorphism
on both sides of its defining square induces a quasi-isomorphism of cones. Detect
quasi-isomorphisms in the tower category levelwise. -/
theorem strictRed_inverts (T : Scheme.{u}) :
    (HomologicalComplex.quasiIso (AdicCompletion.Modules l E T) (.up ℤ)).IsInvertedBy
      (strictRed l E T ⋙ DerivedCategory.Q) := by
  have : PreservesFiniteLimits (scalarTower l E T) :=
    preservesFiniteLimits_of_evaluation _ (fun n ↦ by
      change PreservesFiniteLimits (𝟭 (AdicCompletion.Modules l E T))
      infer_instance)
  have : PreservesFiniteColimits (scalarTower l E T) :=
    preservesFiniteColimits_of_evaluation _ (fun n ↦ by
      change PreservesFiniteColimits (𝟭 (AdicCompletion.Modules l E T))
      infer_instance)
  intro M N f hf
  let : QuasiIso f := hf
  let a := ((scalarTower l E T).mapHomologicalComplex (.up ℤ)).map f
  let b := ((constant l E T).mapHomologicalComplex (.up ℤ)).map f
  have : QuasiIso a := inferInstance
  have : QuasiIso b := inferInstance
  let t := DerivedCategory.Q.mapTriangle.map
    (CochainComplex.mappingCone.triangleMap
      ((complexPowerMap l E T).app M) ((complexPowerMap l E T).app N)
      a b ((complexPowerMap l E T).naturality f).symm)
  exact Pretriangulated.isIso₃_of_isIso₁₂ t
    (DerivedCategory.mappingCone_triangle_distinguished _)
    (DerivedCategory.mappingCone_triangle_distinguished _)
    (by change IsIso (DerivedCategory.Q.map a); infer_instance)
    (by change IsIso (DerivedCategory.Q.map b); infer_instance)

/-- The reduction functor on the unbounded derived category of integral modules.
It is the actual localization of the cone tower, rather than a family of derived cones.
Source: blueprint Notation 3 (blueprint: det-pbc-complete-derived-completion). -/
def red (T : Scheme.{u}) : DerivedCategory (AdicCompletion.Modules l E T) ⥤ DTow l E T :=
  Localization.lift (strictRed l E T ⋙ DerivedCategory.Q) (strictRed_inverts l E T)
    DerivedCategory.Q

/-- The canonical factorization of the strict cone tower through its localization.
Source: blueprint Notation 3 (blueprint: det-pbc-complete-derived-completion). -/
def redFactors (T : Scheme.{u}) :
    DerivedCategory.Q ⋙ red l E T ≅ strictRed l E T ⋙ DerivedCategory.Q :=
  Localization.fac _ (strictRed_inverts l E T) DerivedCategory.Q

/-- Register the explicit localization comparison for the reduction tower.
Source: blueprint Notation 3 (blueprint: det-pbc-complete-derived-completion). -/
instance red_lifting (T : Scheme.{u}) :
    Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso (AdicCompletion.Modules l E T) (.up ℤ))
      (strictRed l E T ⋙ DerivedCategory.Q) (red l E T) :=
  ⟨redFactors l E T⟩

/-- The strict degree-zero cone inclusion is natural.
Source: blueprint Notation 4 (blueprint: det-pbc-complete-derived-completion).
Proof: the second square map in the definition of strictRed is the constant functor's
map. Naturality is the inr equation for the induced cone map. -/
theorem strictAugmentation_naturality (T : Scheme.{u})
    {M N : CochainComplex (AdicCompletion.Modules l E T) ℤ} (f : M ⟶ N) :
    ((constant l E T).mapHomologicalComplex (.up ℤ)).map f ≫
        CochainComplex.mappingCone.inr ((complexPowerMap l E T).app N) =
      CochainComplex.mappingCone.inr ((complexPowerMap l E T).app M) ≫
        (strictRed l E T).map f := by
  exact (CochainComplex.mappingCone.triangleMap
    ((complexPowerMap l E T).app M) ((complexPowerMap l E T).app N)
    (((scalarTower l E T).mapHomologicalComplex (.up ℤ)).map f)
    (((constant l E T).mapHomologicalComplex (.up ℤ)).map f)
    ((complexPowerMap l E T).naturality f).symm).comm₂.symm

/-- The degree-zero inclusions give a morphism of strict towers of complexes.
Source: blueprint Notation 4 (blueprint: det-pbc-complete-derived-completion). -/
def strictAugmentation (T : Scheme.{u}) :
    (constant l E T).mapHomologicalComplex (.up ℤ) ⟶ strictRed l E T where
  app M := CochainComplex.mappingCone.inr ((complexPowerMap l E T).app M)
  naturality _ _ f := strictAugmentation_naturality l E T f

/-- The canonical degree-zero inclusion on derived towers.
Source: blueprint Notation 4 (blueprint: det-pbc-complete-derived-completion). -/
def augmentation (T : Scheme.{u}) : dconstant l E T ⟶ red l E T :=
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso (AdicCompletion.Modules l E T) (.up ℤ)) _ _
    (dconstant l E T) (red l E T)
    (Functor.whiskerRight (strictAugmentation l E T) DerivedCategory.Q)

/-- Derived completion as Rlim of the strict, localized reduction tower.
Source: blueprint Notation 4 (blueprint: det-pbc-complete-derived-completion). -/
def completion (T : Scheme.{u}) := red l E T ⋙ rlim l E T

/-- The canonical completion unit: the constant-limit adjunction unit followed by
Rlim of the degree-zero inclusions. Source: blueprint Notation 4
(blueprint: det-pbc-complete-derived-completion). -/
def kappa (T : Scheme.{u}) : 𝟭 (DerivedCategory (AdicCompletion.Modules l E T)) ⟶
    completion l E T :=
  (constantLimitAdjunction l E T).unit ≫
    Functor.whiskerRight (augmentation l E T) (rlim l E T)

/-- The canonical mate of the exact pullback/evaluation comparison.
Source: blueprint Assertion 3 (blueprint: det-pbc-complete-derived-completion). -/
def pushEvaluationMap {T T' : Scheme.{u}} (f : T' ⟶ T) (n : ℕ) :
    rpush l E f ⋙ dev l E T n ⟶ dev l E T' n ⋙ rpushModule l E f :=
  (mateEquiv (towerAdjunction l E f) (moduleAdjunction l E f)
    (.mk _ _ _ _ (pullEvaluation l E f n).inv)).natTrans

/-- The exact-localization comparison between an exact functor and constant towers.
Source: blueprint Assertions 4--5 (blueprint: det-pbc-complete-derived-completion). -/
def constantInterchange {T T' : Scheme.{u}}
    (F : AdicCompletion.Modules l E T ⥤ AdicCompletion.Modules l E T')
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    F.mapDerivedCategory ⋙ dconstant l E T' ≅
      dconstant l E T ⋙ ((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso F (constant l E T')).symm ≪≫
    Functor.mapDerivedCategoryNatIso (Functor.compConstIso ℕᵒᵖ F) ≪≫
    Functor.mapDerivedCategoryCompIso (constant l E T)
      ((Functor.whiskeringRight ℕᵒᵖ _ _).obj F)

/-- The canonical derived pushforward/limit isomorphism. It is the conjugate of the
constant/pullback comparison under the two composite derived adjunctions, and therefore
has the ordinary limit comparison as its K-injective normalization.
Source: blueprint Assertion 4 (blueprint: det-pbc-complete-derived-completion). -/
def pushLimitIso {T T' : Scheme.{u}} (f : T' ⟶ T) :
    rlim l E T' ⋙ rpushModule l E f ≅ rpush l E f ⋙ rlim l E T :=
  conjugateIsoEquiv
    ((moduleAdjunction l E f).comp (constantLimitAdjunction l E T'))
    ((constantLimitAdjunction l E T).comp (towerAdjunction l E f))
    (constantInterchange l E
      (CondensedRing.upperStar (DerivedNakayama.integerRing l E) f)).symm

/-- An exact equivalence commutes with derived limits, canonically by conjugating the
constant comparison for its inverse equivalence. Source: blueprint Assertion 5
(blueprint: det-pbc-complete-derived-completion). -/
def equivalenceLimitIso {T T' : Scheme.{u}}
    (e : AdicCompletion.Modules l E T ≌ AdicCompletion.Modules l E T')
    [e.functor.Additive] :
    rlim l E T ⋙ e.functor.mapDerivedCategory ≅
      ((Functor.whiskeringRight ℕᵒᵖ _ _).obj e.functor).mapDerivedCategory ⋙ rlim l E T' := by
  letI := e.inverse_additive
  let adj : e.inverse ⊣ e.functor := e.symm.toAdjunction
  let a := adj.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight
    e.functor.rightDerivedFunctorIsoMapDerivedCategory
  let b := (adj.whiskerRight ℕᵒᵖ)
    |>.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight
      (Functor.rightDerivedFunctorIsoMapDerivedCategory
        ((Functor.whiskeringRight ℕᵒᵖ _ _).obj e.functor))
  exact conjugateIsoEquiv (a.comp (constantLimitAdjunction l E T))
    ((constantLimitAdjunction l E T').comp b)
    (constantInterchange l E e.inverse).symm

/-- Total tensor with a constant complex on strict towers, using the pointwise tensor
of module towers and the usual direct-sum total complex.
Source: blueprint Assertion 5 (blueprint: det-pbc-complete-derived-completion). -/
def strictTensor (T : Scheme.{u}) (P : CochainComplex (AdicCompletion.Modules l E T) ℤ) :
    CochainComplex (Tow l E T) ℤ ⥤ CochainComplex (Tow l E T) ℤ :=
  ((curriedTensor (Tow l E T)).map₂CochainComplex).flip.obj
    (((constant l E T).mapHomologicalComplex (.up ℤ)).obj P)

/-- Tensoring strict towers with a bounded finite-free complex inverts quasi-isomorphisms.
Source: blueprint Assertion 5 (blueprint: det-pbc-complete-derived-completion).
Proof: finite-free terms are flat, and bounded flat complexes are K-flat. Evaluation
computes this tensor levelwise, so its preservation of quasi-isomorphisms follows from
K-flatness at every level and levelwise detection in the tower category. -/
theorem strictTensor_inverts (T : Scheme.{u})
    (P : CochainComplex (AdicCompletion.Modules l E T) ℤ)
    (_hb : ∃ a b : ℤ, P.IsStrictlyGE a ∧ P.IsStrictlyLE b)
    (_hf : ∀ j : ℤ, Mod.IsFree (AdicCompletion.ring l E T) (P.X j)) :
    (HomologicalComplex.quasiIso (Tow l E T) (.up ℤ)).IsInvertedBy
      (strictTensor l E T P ⋙ DerivedCategory.Q) := by
  let C : CochainComplex (Tow l E T) ℤ :=
    ((constant l E T).mapHomologicalComplex (.up ℤ)).obj P
  have (N : Tow l E T) : PreservesColimitsOfSize.{0, 0} (tensorRight N) := by
    constructor
    intro J _
    apply preservesColimitsOfShape_of_evaluation
    intro n
    change PreservesColimitsOfShape J
      ((ev l E T n.unop) ⋙ tensorRight (N.obj n))
    infer_instance
  have (N : Tow l E T) : PreservesColimitsOfSize.{0, 0} (tensorLeft N) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight N).symm
  have (X₁ X₂ : GradedObject ℤ (Tow l E T)) : GradedObject.HasTensor X₁ X₂ :=
    inferInstance
  have (X₁ X₂ X₃ : GradedObject ℤ (Tow l E T)) :
      GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := inferInstance
  have (X₁ X₂ X₃ : GradedObject ℤ (Tow l E T)) :
      GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := inferInstance
  have (X₁ X₂ X₃ X₄ : GradedObject ℤ (Tow l E T)) :
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := inferInstance
  obtain ⟨a, b, ha, hb⟩ := _hb
  let : P.IsStrictlyGE a := ha
  let : P.IsStrictlyLE b := hb
  have : C.IsStrictlyGE a := inferInstance
  have : C.IsStrictlyLE b := inferInstance
  have hflat (j : ℤ) : ObjectProperty.flat (C.X j) := by
    obtain ⟨n, ⟨e⟩⟩ := _hf j
    let e' : C.X j ≅ ⨁ (fun _ : Fin n ↦ (𝟙_ (Tow l E T))) :=
      (constant l E T).mapIso e ≪≫
        (constant l E T).mapBiproduct (fun _ : Fin n ↦ Mod.regular (AdicCompletion.ring l E T))
    apply ObjectProperty.prop_of_iso _ e'.symm
    exact ObjectProperty.prop_of_isLimit _ (biproduct.isLimit _)
      (fun _ ↦ ObjectProperty.prop_unit _)
  have hk := CochainComplex.kFlat_of_bounded_of_flat C a b hflat
  intro X Y f hf
  have : QuasiIso ((strictTensor l E T P).map f) := hk.2 f hf
  change IsIso (DerivedCategory.Q.map ((strictTensor l E T P).map f))
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance

/-- The derived tower tensor with a bounded finite-free complex, defined by localization
of the actual total tensor on strict towers.
Source: blueprint Assertion 5 (blueprint: det-pbc-complete-derived-completion). -/
def tensorTower (T : Scheme.{u}) (P : CochainComplex (AdicCompletion.Modules l E T) ℤ)
    (hb : ∃ a b : ℤ, P.IsStrictlyGE a ∧ P.IsStrictlyLE b)
    (hf : ∀ j : ℤ, Mod.IsFree (AdicCompletion.ring l E T) (P.X j)) :
    DTow l E T ⥤ DTow l E T :=
  Localization.lift (strictTensor l E T P ⋙ DerivedCategory.Q)
    (strictTensor_inverts l E T P hb hf) DerivedCategory.Q

/-- The derived evaluation transition, including the successor transition and identities.
Source: blueprint Notation 1 (blueprint: det-pbc-complete-derived-completion). -/
def transition (T : Scheme.{u}) (n : ℕ) : dev l E T (n+1) ⟶ dev l E T n :=
  towerDerivedEvaluationTransition (AdicCompletion.Modules l E T)
    (homOfLE (Nat.le_succ n)).op

/-- The canonical free diagram left adjoint to evaluation; on level m it is a coproduct
of copies of N indexed by arrows n→m, hence N for m≤n and zero otherwise.
Source: blueprint Assertion 1 (blueprint: det-pbc-complete-derived-completion). -/
abbrev freeDiagram (T : Scheme.{u}) (n : ℕ) :=
  evaluationLeftAdjoint (AdicCompletion.Modules l E T) (op n)

/-- The actual evaluation adjunction, rather than just the assertion of a right adjoint.
Source: blueprint Assertion 1 (blueprint: det-pbc-complete-derived-completion). -/
def evaluationAdjunction (T : Scheme.{u}) (n : ℕ) : freeDiagram l E T n ⊣ ev l E T n :=
  evaluationAdjunctionRight (AdicCompletion.Modules l E T) (op n)

/-- Evaluation has an exact free-diagram left adjoint and preserves K-injective complexes.
Source: blueprint Assertion 1, Stacks Tag 08BJ
(blueprint: det-pbc-complete-derived-completion).
Proof: the free diagram evaluated at m is the coproduct indexed by n→m. This index
is subsingleton, so its coproduct is finite and exact in an abelian category. Limits
are detected by evaluation, and the adjunction supplies preservation of colimits.
The existing exact-adjoint theorem then gives preservation of K-injective complexes. -/
theorem evaluationProperties (T : Scheme.{u}) (n : ℕ) :
    PreservesFiniteLimits (ev l E T n) ∧
      PreservesFiniteColimits (ev l E T n) ∧
      PreservesFiniteLimits (freeDiagram l E T n) ∧
      PreservesFiniteColimits (freeDiagram l E T n) ∧
      (∀ I : CochainComplex (Tow l E T) ℤ, I.IsKInjective →
        CochainComplex.IsKInjective (((ev l E T n).mapHomologicalComplex (.up ℤ)).obj I)) := by
  classical
  have (m : ℕᵒᵖ) : PreservesFiniteLimits
      (freeDiagram l E T n ⋙ (evaluation ℕᵒᵖ (AdicCompletion.Modules l E T)).obj m) := by
    let e : freeDiagram l E T n ⋙
        (evaluation ℕᵒᵖ (AdicCompletion.Modules l E T)).obj m ≅
        Functor.const (Discrete (op n ⟶ m)) ⋙ colim :=
      NatIso.ofComponents (fun X ↦ Iso.refl _) (by
        intro X Y f
        apply Sigma.hom_ext
        intro i
        simp [freeDiagram, evaluationLeftAdjoint]
        rfl)
    exact preservesFiniteLimits_of_natIso e.symm
  have : PreservesFiniteLimits (freeDiagram l E T n) := ⟨fun J _ _ ↦
    preservesLimitsOfShape_of_evaluation _ J (fun m ↦ inferInstance)⟩
  have : (freeDiagram l E T n).IsLeftAdjoint := (evaluationAdjunction l E T n).isLeftAdjoint
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  intro I hI
  let := hI
  exact tower_evaluation_isKInjective (AdicCompletion.Modules l E T) I (op n)

/-- Derived evaluations jointly reflect isomorphisms.
Source: blueprint Assertion 2 (blueprint: det-pbc-complete-derived-completion).
Proof: exact evaluation commutes with derived cohomology. If every evaluation of an
arrow is invertible, all components of every cohomology arrow are invertible, hence
that cohomology arrow is invertible. Cohomology detects isomorphisms in D(Tow). -/
theorem evaluation_isIso_iff (T : Scheme.{u}) {M N : DTow l E T} (a : M ⟶ N) :
    IsIso a ↔ ∀ n : ℕ, IsIso ((dev l E T n).map a) := by
  refine ⟨fun _ n ↦ inferInstance, fun h ↦ ?_⟩
  apply (DerivedCategory.isIso_iff _ a).2
  intro q
  have (n : ℕᵒᵖ) : IsIso (((DerivedCategory.homologyFunctor (Tow l E T) q).map a).app n) := by
    let := h n.unop
    exact (NatIso.isIso_map_iff
      ((ev l E T n.unop).mapDerivedCategoryHomologyFunctorIso q) a).2
        (inferInstance : IsIso ((DerivedCategory.homologyFunctor _ q).map
          ((dev l E T n.unop).map a)))
  exact NatIso.isIso_of_isIso_app _

/-- The specified right derived inverse limit has the normalized strict Roos model.
Source: blueprint Notation 1, Stacks Tag 0941
(blueprint: det-pbc-complete-derived-completion).
Proof: use the exact-products comparison for the integral module category. Its
comparison with ordinary inverse limit is invertible on K-injective towers by the
construction of the total right derived functor. Reverse the resulting comparison. -/
theorem roosComparison (T : Scheme.{u}) :
    Nonempty (DerivedCategory.Q ⋙ rlim l E T ≅ ExactProductsRoos.fibre ⋙ DerivedCategory.Q) := by
  let : CountableAB4Star (AdicCompletion.Modules l E T) :=
    .of_epi_π_app_zero (Mod.epiπAppZeroOfEpi
      Scheme.ProEt.epi_π_app_zero_of_epi_addCommGrpCat)
  obtain ⟨e, _⟩ := ExactProductsRoos.comparisonIso (rlim l E T)
    (show (inverseLimit l E T).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ rlim l E T from
      { app := (inverseLimit l E T).rightDerivedFunctorUnitQ
        naturality _ _ a := (inverseLimit l E T).rightDerivedFunctorUnitQ_naturality a })
    (fun I hI ↦ by
      let := hI
      change IsIso ((inverseLimit l E T).rightDerivedFunctorUnitQ I)
      rw [Functor.rightDerivedFunctorUnitQ_eq]
      infer_instance)
  exact ⟨e.symm⟩

/-- The constant-tower functor on derived categories is fully faithful, so the
canonical constant-limit unit is invertible.
Source: blueprint Notation 4 (blueprint: det-pbc-complete-derived-completion).
Proof: evaluation at the terminal level is exact and left adjoint to the constant
functor. Derive this adjunction. The composite constant then evaluation is the identity,
so the derived constant functor is fully faithful. The unit of any adjunction with
fully faithful left adjoint is invertible, in particular the specified limit adjunction. -/
theorem constantLimitUnit_isIso (T : Scheme.{u})
    (M : DerivedCategory (AdicCompletion.Modules l E T)) :
    IsIso ((constantLimitAdjunction l E T).unit.app M) := by
  let a := (UnboundedExactTower.evaluationZeroConstAdjunction
    (AdicCompletion.Modules l E T)).mapDerivedCategoryRightDerivedAdjunction
    |>.ofNatIsoRight (constant l E T).rightDerivedFunctorIsoMapDerivedCategory
  let e : dconstant l E T ⋙ dev l E T 0 ≅ 𝟭 _ :=
    (Functor.mapDerivedCategoryCompIso (constant l E T) (ev l E T 0)).symm ≪≫
      Functor.mapDerivedCategoryNatIso
        (Functor.constCompEvaluationObj (C := ℕᵒᵖ)
          (D := AdicCompletion.Modules l E T) (op 0)) ≪≫
      Functor.mapDerivedCategoryIdIso _
  let h := a.fullyFaithfulROfCompIsoId e
  let := h.full
  let := h.faithful
  infer_instance

/-- The pushforward/evaluation mate respects the specified adjunction units.
Source: blueprint Assertion 3 (blueprint: det-pbc-complete-derived-completion).
Proof: this is the unit identity for the mates correspondence applied to the inverse
of the pullback/evaluation comparison. -/
theorem pushEvaluation_unit {T T' : Scheme.{u}} (f : T' ⟶ T) (n : ℕ)
    (M : DTow l E T) :
    (dev l E T n).map ((towerAdjunction l E f).unit.app M) ≫
        (pushEvaluationMap l E f n).app ((dpull l E f).obj M) =
      (moduleAdjunction l E f).unit.app ((dev l E T n).obj M) ≫
        (rpushModule l E f).map ((pullEvaluation l E f n).inv.app M) := by
  exact unit_mateEquiv (towerAdjunction l E f) (moduleAdjunction l E f)
    (.mk _ _ _ _ (pullEvaluation l E f n).inv) M

/-- The pushforward/evaluation mate respects the specified adjunction counits.
Source: blueprint Assertion 3 (blueprint: det-pbc-complete-derived-completion).
Proof: the mate/counit identity gives the formula after composition with the inverse
pullback/evaluation comparison; cancel that isomorphism. -/
theorem pushEvaluation_counit {T T' : Scheme.{u}} (f : T' ⟶ T) (n : ℕ)
    (N : DTow l E T') :
    (dev l E T' n).map ((towerAdjunction l E f).counit.app N) =
      (pullEvaluation l E f n).hom.app ((rpush l E f).obj N) ≫
        (dpullModule l E f).map ((pushEvaluationMap l E f n).app N) ≫
        (moduleAdjunction l E f).counit.app ((dev l E T' n).obj N) := by
  apply (cancel_epi ((pullEvaluation l E f n).inv.app _)).1
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  exact (mateEquiv_counit (towerAdjunction l E f) (moduleAdjunction l E f)
    (.mk _ _ _ _ (pullEvaluation l E f n).inv) N).symm

/-- Scalar powers are respected by the induced action on every integral module.
Source: blueprint Notation 3 (blueprint: det-pbc-complete-derived-completion).
Proof: the scalar action is the composite of pullback, conjugation by the regular-module
comparison, tensoring on the left, and conjugation by the left unitor. Each is a monoid
homomorphism on endomorphisms, so their composite preserves powers. -/
theorem scalarOnModules_pow (T : Scheme.{u})
    (d : End (Mod.regular (DerivedNakayama.integerRing l E))) (k : ℕ) :
    DerivedNakayama.scalarOnModules l E T (d ^ k) =
      (End.of (DerivedNakayama.scalarOnModules l E T d)) ^ k := by
  let A := AdicCompletion.Modules l E T
  let F₁ := (DerivedNakayama.pullback l E T).mapEnd
    (Mod.regular (DerivedNakayama.integerRing l E))
  let F₂ := (DerivedNakayama.regularPullbackIso l E T).conj.toMonoidHom
  let F₃ := (tensoringLeft A).mapEnd (𝟙_ A)
  let F₄ := (leftUnitorNatIso A).conj.toMonoidHom
  exact (F₄.comp (F₃.comp (F₂.comp F₁))).map_pow d k

/-- The derived reduction tower is triangulated with its totalization shift.
Source: blueprint Notation 3 and Assertion 6
(blueprint: det-pbc-complete-derived-completion).
Proof: the strict functor is the cone of a termwise natural transformation between
additive functors. Its two-column totalization is exact on homotopy categories.
The factorization through complexes agrees with the specified localized functor.
Fully faithful precomposition with the homotopy quotient gives the comparison on
homotopy categories. Transport its shift through localization and descend exactness
using the essential surjectivity of localization on arrows. -/
theorem red_triangulated (T : Scheme.{u}) :
    ∃ (_shift : (red l E T).CommShift ℤ), (red l E T).IsTriangulated := by
  let A := AdicCompletion.Modules l E T
  let B := Tow l E T
  let qA := HomotopyCategory.quotient A (.up ℤ)
  let qB := HomotopyCategory.quotient B (.up ℤ)
  obtain ⟨H, eH, cH, hH⟩ := CochainComplex.termwiseCone_homotopy_exact
    (scalarTower l E T) (constant l E T) (powerMap l E T)
  let := cH
  let := hH
  let eC : qA ⋙ (DerivedCategory.Qh ⋙ red l E T) ≅
      qA ⋙ (H ⋙ DerivedCategory.Qh) :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso A) (red l E T) ≪≫
      redFactors l E T ≪≫
      Functor.isoWhiskerRight (eqToIso (show strictRed l E T =
        CochainComplex.termwiseCone (scalarTower l E T) (constant l E T)
          (powerMap l E T) from rfl)) DerivedCategory.Q ≪≫
      Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso B).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight eH.symm DerivedCategory.Qh ≪≫
      Functor.associator _ _ _
  let e : DerivedCategory.Qh ⋙ red l E T ≅ H ⋙ DerivedCategory.Qh :=
    (Functor.FullyFaithful.ofFullyFaithful
      ((Functor.whiskeringLeft _ _ (DerivedCategory B)).obj qA)).preimageIso eC
  let : Localization.Lifting (DerivedCategory.Qh (C := A))
      (HomotopyCategory.quasiIso A (.up ℤ)) (H ⋙ DerivedCategory.Qh) (red l E T) := ⟨e⟩
  let c := Functor.commShiftOfLocalization DerivedCategory.Qh
    (HomotopyCategory.quasiIso A (.up ℤ)) ℤ (H ⋙ DerivedCategory.Qh) (red l E T)
  let := c
  have := Localization.essSurj_mapArrow (DerivedCategory.Qh (C := A))
    (HomotopyCategory.quasiIso A (.up ℤ))
  have : NatTrans.CommShift e.hom ℤ := by
    change NatTrans.CommShift (Localization.Lifting.iso DerivedCategory.Qh
      (HomotopyCategory.quasiIso A (.up ℤ)) (H ⋙ DerivedCategory.Qh) (red l E T)).hom ℤ
    infer_instance
  exact ⟨c, Functor.isTriangulated_of_precomp_iso e⟩

private theorem tower_flat_of_levelwise (T : Scheme.{u}) (X : Tow l E T)
    (hX : ∀ n : ℕᵒᵖ, ObjectProperty.flat (X.obj n)) : ObjectProperty.flat X := by
  constructor <;> constructor
  · apply preservesFiniteLimits_of_evaluation
    intro n
    let := (hX n).tensorLeft.preservesFiniteLimits
    exact inferInstanceAs (PreservesFiniteLimits
      ((evaluation ℕᵒᵖ (AdicCompletion.Modules l E T)).obj n ⋙ tensorLeft (X.obj n)))
  · apply preservesFiniteColimits_of_evaluation
    intro n
    let := (hX n).tensorLeft.preservesFiniteColimits
    exact inferInstanceAs (PreservesFiniteColimits
      ((evaluation ℕᵒᵖ (AdicCompletion.Modules l E T)).obj n ⋙ tensorLeft (X.obj n)))
  · apply preservesFiniteLimits_of_evaluation
    intro n
    let := (hX n).tensorRight.preservesFiniteLimits
    exact inferInstanceAs (PreservesFiniteLimits
      ((evaluation ℕᵒᵖ (AdicCompletion.Modules l E T)).obj n ⋙ tensorRight (X.obj n)))
  · apply preservesFiniteColimits_of_evaluation
    intro n
    let := (hX n).tensorRight.preservesFiniteColimits
    exact inferInstanceAs (PreservesFiniteColimits
      ((evaluation ℕᵒᵖ (AdicCompletion.Modules l E T)).obj n ⋙ tensorRight (X.obj n)))

private theorem tower_functorialFlatResolution (T : Scheme.{u}) :
    Abelian.HasFunctorialFlatResolution (Tow l E T) := by
  let A := AdicCompletion.Modules l E T
  let Λ := (inferInstance : Abelian.HasFunctorialFlatResolution A).some
  let F₀ := (Functor.whiskeringRight ℕᵒᵖ A A).obj (Λ.F ⋙ ObjectProperty.flat.ι)
  let F := ObjectProperty.lift ObjectProperty.flat F₀
    (fun X ↦ tower_flat_of_levelwise l E T (F₀.obj X)
      (fun n ↦ (Λ.F.obj (X.obj n)).property))
  let π : F ⋙ ObjectProperty.flat.ι ⟶ 𝟭 (Tow l E T) :=
    { app X :=
        { app n := Λ.π.app (X.obj n)
          naturality _ _ t := Λ.π.naturality (X.map t) }
      naturality _ _ f := by
        apply NatTrans.ext
        funext n
        exact Λ.π.naturality (f.app n) }
  refine ⟨{ F := F, π := π, epi_π_app := ?_ }⟩
  intro X
  have (n : ℕᵒᵖ) : Epi ((π.app X).app n) := Λ.epi_π_app (X.obj n)
  exact NatTrans.epi_of_epi_app _

private noncomputable instance towerClosed (T : Scheme.{u}) :
    MonoidalClosed (Tow l E T) :=
  Functor.functorCategoryMonoidalClosed ℕᵒᵖ (AdicCompletion.Modules l E T)

private instance towerFunctorialFlat (T : Scheme.{u}) :
    Abelian.HasFunctorialFlatResolution (Tow l E T) := tower_functorialFlatResolution l E T

private noncomputable instance constantMonoidal (T : Scheme.{u}) :
    (constant l E T).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ ↦ NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; simp)
      μIso_hom_natural_left := by intros; ext n; simp
      μIso_hom_natural_right := by intros; ext n; simp
      associativity := by intros; ext n; simp
      left_unitality := by
        intro X
        apply NatTrans.ext
        funext n
        change (λ_ X).hom = (𝟙 _ ▷ X) ≫ 𝟙 _ ≫ (λ_ X).hom
        simp only [MonoidalCategory.id_whiskerRight, Category.id_comp]
      right_unitality := by
        intro X
        apply NatTrans.ext
        funext n
        change (ρ_ X).hom = (X ◁ 𝟙 _) ≫ 𝟙 _ ≫ (ρ_ X).hom
        simp only [MonoidalCategory.whiskerLeft_id, Category.id_comp] }

private instance constantPreservesFlat (T : Scheme.{u}) :
    (constant l E T).PreservesFlat where
  flat_obj hX := tower_flat_of_levelwise l E T _ (fun _ ↦ hX)

private theorem finiteFree_dualizable (T : Scheme.{u})
    (M : AdicCompletion.Modules l E T) (hM : Mod.IsFree (AdicCompletion.ring l E T) M) :
    IsDualizable M := by
  obtain ⟨r, ⟨e⟩⟩ := hM
  exact IsDualizable.of_iso e.symm (isDualizable_biproduct_unit r)

private theorem constantComplex_kFlat (T : Scheme.{u})
    (P : CochainComplex (AdicCompletion.Modules l E T) ℤ)
    (hb : ∃ a b : ℤ, P.IsStrictlyGE a ∧ P.IsStrictlyLE b)
    (hf : ∀ j : ℤ, Mod.IsFree (AdicCompletion.ring l E T) (P.X j)) :
    (HomologicalComplex.quasiIso (Tow l E T) (.up ℤ)).kFlat
      (((constant l E T).mapHomologicalComplex (.up ℤ)).obj P) := by
  obtain ⟨a, b, ha, hb⟩ := hb
  let := ha
  let := hb
  apply CochainComplex.kFlat_of_bounded_of_flat _ a b
  intro j
  exact tower_flat_of_levelwise l E T _ (fun _ ↦ (finiteFree_dualizable l E T _ (hf j)).flat)

private theorem tensorTower_realization (T : Scheme.{u})
    (P : CochainComplex (AdicCompletion.Modules l E T) ℤ)
    (hb : ∃ a b : ℤ, P.IsStrictlyGE a ∧ P.IsStrictlyLE b)
    (hf : ∀ j : ℤ, Mod.IsFree (AdicCompletion.ring l E T) (P.X j)) :
    Nonempty (tensorTower l E T P hb hf ≅
      tensorRight ((dconstant l E T).obj (DerivedCategory.Q.obj P))) := by
  let B := Tow l E T
  let C := ((constant l E T).mapHomologicalComplex (.up ℤ)).obj P
  let Ck : CochainComplex.KFlat B := ⟨C, constantComplex_kFlat l E T P hb hf⟩
  let L := DerivedCategory.TensorCommShift₂.L B
  let eL := DerivedCategory.quotientCompQhIso B
  let e : DerivedCategory.Q ⋙ tensorRight (DerivedCategory.Q.obj C) ≅
      strictTensor l E T P ⋙ DerivedCategory.Q :=
    Functor.isoWhiskerLeft DerivedCategory.Q
      ((curriedTensor (DerivedCategory B)).flip.mapIso (eL.app C).symm) ≪≫
      Functor.isoWhiskerRight eL.symm (tensorRight (L.obj C)) ≪≫
      asIso (DerivedCategory.TensorCommShift₂.tensorRightLift Ck) ≪≫
      Functor.isoWhiskerLeft (strictTensor l E T P) eL
  let r : tensorTower l E T P hb hf ≅ tensorRight (DerivedCategory.Q.obj C) :=
    (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
      (HomologicalComplex.quasiIso B (.up ℤ)) (DerivedCategory B)).preimageIso
        (Localization.fac (strictTensor l E T P ⋙ DerivedCategory.Q)
          (strictTensor_inverts l E T P hb hf) DerivedCategory.Q ≪≫ e.symm)
  exact ⟨r ≪≫ (curriedTensor (DerivedCategory B)).flip.mapIso
    ((constant l E T).mapDerivedCategoryFactors.app P).symm⟩

/-- Bounded finite-free tensor commutes naturally with derived inverse limit.
Source: blueprint Assertion 5 (blueprint: det-pbc-complete-derived-completion).
Proof: form functorial flat covers of towers levelwise, so the pointwise monoidal
structure has its derived tensor. The exact constant tower functor is strong monoidal
on derived categories. A bounded finite-free complex is dualizable. The projection
formula for its constant/limit adjunction is therefore an isomorphism. The K-flat
comparison identifies derived tensor by its constant tower with the specified
localized strict total tensor, giving the asserted natural comparison. -/
theorem tensorLimitIso (T : Scheme.{u})
    (P : CochainComplex (AdicCompletion.Modules l E T) ℤ)
    (hb : ∃ a b : ℤ, P.IsStrictlyGE a ∧ P.IsStrictlyLE b)
    (hf : ∀ j : ℤ, Mod.IsFree (AdicCompletion.ring l E T) (P.X j)) :
    Nonempty (rlim l E T ⋙
        (CondensedRing.derivedTensor (DerivedNakayama.integerRing l E) T).flip.obj
          (DerivedCategory.Q.obj P) ≅
      tensorTower l E T P hb hf ⋙ rlim l E T) := by
  let F := constant l E T
  let : F.IsLeftAdjoint := (constLimAdj : F ⊣ inverseLimit l E T).isLeftAdjoint
  let : F.mapDerivedCategory.OplaxMonoidal := F.mapDerivedCategoryOplaxMonoidal
  have : IsIso (Functor.OplaxMonoidal.η F.mapDerivedCategory) :=
    F.isIso_mapDerivedCategoryOplaxMonoidal_η
  have (X Y : DerivedCategory (AdicCompletion.Modules l E T)) :
      IsIso (Functor.OplaxMonoidal.δ F.mapDerivedCategory X Y) := by
    rw [F.mapDerivedCategoryOplaxMonoidal_δ]
    infer_instance
  let := Functor.Monoidal.ofOplaxMonoidal F.mapDerivedCategory
  let : SymmetricCategory (DerivedCategory (AdicCompletion.Modules l E T)) :=
    DerivedCategory.symmetricCategory _
  have hbounded := hb
  obtain ⟨a, b, ha, hb'⟩ := hbounded
  let := ha
  let := hb'
  have hP := DerivedCategory.isDualizable_Q_obj P a b
    (fun j ↦ finiteFree_dualizable l E T _ (hf j))
  let φ := F.mapDerivedCategoryTensorComparison
  let π := (constantLimitAdjunction l E T).rightAdjointProjectionMap φ
  let p : rlim l E T ⋙ tensorRight (DerivedCategory.Q.obj P) ⟶
      tensorRight ((dconstant l E T).obj (DerivedCategory.Q.obj P)) ⋙ rlim l E T :=
    { app X := (π.app X).app (DerivedCategory.Q.obj P)
      naturality _ _ f := NatTrans.congr_app (π.naturality f) (DerivedCategory.Q.obj P) }
  have (X : DTow l E T) : IsIso (p.app X) :=
    (constantLimitAdjunction l E T).isIso_rightAdjointProjectionMap_app_app_of_isDualizable
      φ (fun _ _ ↦ rfl) X hP
  have : IsIso p := NatIso.isIso_of_isIso_app p
  obtain ⟨r⟩ := tensorTower_realization l E T P hb hf
  exact ⟨asIso p ≪≫ Functor.isoWhiskerRight r.symm (rlim l E T)⟩

/-- The finite scalar tensor functor is the restricted derived reduction.
Source: blueprint Assertion 5 and the normalized internal K-flat scalar comparison
(blueprint: det-pbc-complete-derived-completion).
Proof: the pulled-back finite coefficient module is the regular quotient module with
scalars restricted. Apply the natural K-flat scalar-tower realization; its canonical
unit and transition equations imply, in particular, the asserted natural isomorphism. -/
theorem finiteScalarComparison (T : Scheme.{u}) (n : ℕ) :
    Nonempty (DerivedNakayama.reductionFunctor l E T (n + 1) ≅
      AdicCompletion.derivedReduction l E T n ⋙ AdicCompletion.restrict l E T n) := by
  obtain ⟨e, _, _⟩ := Mod.KFlatScalarTower.derived_realization
    (AdicCompletion.ring l E T) (AdicCompletion.finiteRing l E T)
    (AdicCompletion.quotient l E T) (AdicCompletion.transition l E T)
    (AdicCompletion.quotient_transition l E T) (AdicCompletion.finiteModule l E T)
    (AdicCompletion.finiteUnit l E T)
    (fun n ↦ (DerivedNakayama.pullback l E T).map (AdicCompletion.quotientStep l E n))
    (AdicCompletion.finiteModuleIso l E T)
    (by
      intro n
      change (𝟙 _ ≫ (upperStarFromPoint T).map
        (DerivedNakayama.reductionRing l E (n + 1))) ≫ 𝟙 _ = _
      simp only [Category.id_comp, Category.comp_id])
    (by
      intro n
      change (upperStarFromPoint T).map (AdicCompletion.transitionRing l E n) ≫ 𝟙 _ =
        𝟙 _ ≫ (upperStarFromPoint T).map (AdicCompletion.transitionRing l E n)
      simp only [Category.id_comp, Category.comp_id])
  exact ⟨e n⟩

private theorem evaluatedPowerMap (T : Scheme.{u}) (n : ℕ) :
    Functor.whiskerRight (complexPowerMap l E T) ((ev l E T n).mapHomologicalComplex (.up ℤ)) =
      NatTrans.mapHomologicalComplex
        (DerivedNakayama.scalarOnModules l E T (uniformizer l E ^ (n + 1))) (.up ℤ) := by
  rw [scalarOnModules_pow]
  apply NatTrans.ext
  funext P
  apply HomologicalComplex.Hom.ext
  funext j
  exact (((evaluation _ _).obj (P.X j)).mapEnd (𝟭 (AdicCompletion.Modules l E T))).map_pow
    (End.of (scalar l E T)) (n + 1) |>.symm

private abbrev principalScalar (T : Scheme.{u})
    (P : CochainComplex (AdicCompletion.Modules l E T) ℤ) : End P :=
  End.of (DerivedNakayama.scalarOnComplex l E T (uniformizer l E) P)

private theorem scalarOnComplex_pow (T : Scheme.{u})
    (P : CochainComplex (AdicCompletion.Modules l E T) ℤ) (k : ℕ) :
    DerivedNakayama.scalarOnComplex l E T (uniformizer l E ^ k) P =
      principalScalar l E T P ^ k := by
  apply HomologicalComplex.Hom.ext
  funext j
  change (DerivedNakayama.scalarOnModules l E T (uniformizer l E ^ k)).app (P.X j) = _
  rw [scalarOnModules_pow]
  have h₁ := (((evaluation (AdicCompletion.Modules l E T)
    (AdicCompletion.Modules l E T)).obj (P.X j)).mapEnd
      (𝟭 (AdicCompletion.Modules l E T))).map_pow (End.of (scalar l E T)) k
  have h₂ := ((HomologicalComplex.eval (AdicCompletion.Modules l E T) (.up ℤ) j).mapEnd P).map_pow
    (principalScalar l E T P) k
  exact h₁.trans h₂.symm

private theorem power_on_complex (T : Scheme.{u})
    (P : CochainComplex (AdicCompletion.Modules l E T) ℤ) (n : ℕ) :
    ((ev l E T n).mapHomologicalComplex (.up ℤ)).map ((complexPowerMap l E T).app P) =
      principalScalar l E T P ^ (n + 1) := by
  apply HomologicalComplex.Hom.ext
  funext j
  exact ((HomologicalComplex.eval (AdicCompletion.Modules l E T) (.up ℤ) j).mapEnd P).map_pow
    (principalScalar l E T P) (n + 1) |>.symm

private theorem strictPrincipalLevels (T : Scheme.{u})
    (P : CochainComplex (AdicCompletion.Modules l E T) ℤ) :
    ∃ b : ∀ n : ℕ, ((strictRed l E T).obj P).asFunctor.obj (op n) ≅
        CochainComplex.PrincipalCone.level
          (principalScalar l E T P) n,
      (∀ n : ℕ, ((strictRed l E T).obj P).asFunctor.map
          (homOfLE (Nat.le_succ n)).op ≫ (b n).hom =
        (b (n + 1)).hom ≫ CochainComplex.PrincipalCone.step
          (principalScalar l E T P) n) ∧
      (∀ n : ℕ, ((ev l E T n).mapHomologicalComplex (.up ℤ)).map
          ((strictAugmentation l E T).app P) ≫ (b n).hom =
        CochainComplex.mappingCone.inr
          (principalScalar l E T P ^ (n + 1))) := by
  let μ := principalScalar l E T P
  let X := (((scalarTower l E T).mapHomologicalComplex (.up ℤ)).obj P).asFunctor
  let Y := (((constant l E T).mapHomologicalComplex (.up ℤ)).obj P).asFunctor
  let f : X ⟶ Y := HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
    ((complexPowerMap l E T).app P)
  let e : ((strictRed l E T).obj P).asFunctor ≅ levelConeTower f := levelConeTowerIso f
  have hf (n : ℕ) : f.app (op n) = μ ^ (n + 1) := power_on_complex l E T P n
  let c (n : ℕ) := coneIso (f.app (op n)) (μ ^ (n + 1))
    (Iso.refl P) (Iso.refl P) (by
      simp only [Iso.refl_hom]
      exact hf n)
  let b (n : ℕ) := e.app (op n) ≪≫ c n
  refine ⟨b, ?_, ?_⟩
  · intro n
    have hX : X.map (homOfLE (Nat.le_succ n)).op = μ := by
      apply HomologicalComplex.Hom.ext
      funext j
      change ((Functor.ofOpSequence
        (X := fun _ : ℕ ↦ 𝟭 (AdicCompletion.Modules l E T))
        (fun _ ↦ scalar l E T)).map (homOfLE (Nat.le_succ n)).op).app (P.X j) = _
      rw [Functor.ofOpSequence_map_homOfLE_succ]
      rfl
    have hY : Y.map (homOfLE (Nat.le_succ n)).op = 𝟙 P := rfl
    have hn := e.hom.naturality (homOfLE (Nat.le_succ n)).op
    have hc : (levelConeTower f).map (homOfLE (Nat.le_succ n)).op ≫ (c n).hom =
        (c (n + 1)).hom ≫ CochainComplex.PrincipalCone.step μ n := by
      change CochainComplex.mappingCone.map _ _ (X.map _) (Y.map _)
          (f.naturality (homOfLE (Nat.le_succ n)).op).symm ≫ (c n).hom =
        (c (n + 1)).hom ≫ CochainComplex.PrincipalCone.step μ n
      dsimp only [c, coneIso, CochainComplex.PrincipalCone.step]
      rw [← CochainComplex.mappingCone.map_comp, ← CochainComplex.mappingCone.map_comp]
      simp only [Iso.refl_hom, Category.comp_id, hX, hY]
      congr 1
    change _ ≫ (e.hom.app (op n) ≫ (c n).hom) =
      (e.hom.app (op (n + 1)) ≫ (c (n + 1)).hom) ≫ _
    calc
      _ = (_ ≫ e.hom.app (op n)) ≫ (c n).hom := (Category.assoc _ _ _).symm
      _ = (e.hom.app (op (n + 1)) ≫
          (levelConeTower f).map (homOfLE (Nat.le_succ n)).op) ≫ (c n).hom :=
        congrArg (fun g ↦ g ≫ (c n).hom) hn
      _ = e.hom.app (op (n + 1)) ≫ ((levelConeTower f).map
          (homOfLE (Nat.le_succ n)).op ≫ (c n).hom) := Category.assoc _ _ _
      _ = e.hom.app (op (n + 1)) ≫ ((c (n + 1)).hom ≫ _) :=
        congrArg (fun g ↦ e.hom.app (op (n + 1)) ≫ g) hc
      _ = _ := (Category.assoc _ _ _).symm
  · intro n
    change ((ev l E T n).mapHomologicalComplex (.up ℤ)).map
      (CochainComplex.mappingCone.inr ((complexPowerMap l E T).app P)) ≫
        (CochainComplex.mappingCone.mapHomologicalComplexIso
          ((complexPowerMap l E T).app P) (ev l E T n)).hom ≫ (c n).hom = _
    rw [← Category.assoc, CochainComplex.mappingCone.map_inr]
    change CochainComplex.mappingCone.inr (f.app (op n)) ≫ (c n).hom = _
    dsimp only [c, coneIso]
    simp only [CochainComplex.mappingCone.map, CochainComplex.mappingCone.inr_desc,
      Iso.refl_hom]
    exact Category.id_comp _

private abbrev strictProductUnit (T : Scheme.{u})
    (P : CochainComplex (AdicCompletion.Modules l E T) ℤ) :
    P ⟶ ∏ᶜ (fun n : ℕ ↦ ((strictRed l E T).obj P).asFunctor.obj (op n)) :=
  Pi.lift (fun n : ℕ ↦ ((ev l E T n).mapHomologicalComplex (.up ℤ)).map
    ((strictAugmentation l E T).app P))

private theorem strictProductUnit_difference (T : Scheme.{u})
    (P : CochainComplex (AdicCompletion.Modules l E T) ℤ) :
    strictProductUnit l E T P ≫
      ExactProductsRoos.difference.app ((strictRed l E T).obj P) = 0 := by
  apply Pi.hom_ext
  intro n
  simp only [strictProductUnit, towerTransitionEndomorphism,
    towerProductShift, Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id,
    Category.assoc,
    Pi.lift_π, Pi.lift_π_assoc, sub_eq_zero, zero_comp]
  apply HomologicalComplex.Hom.ext
  funext j
  have h := (((strictAugmentation l E T).app P).f j).naturality
    (homOfLE (Nat.le_succ n)).op
  change 𝟙 (P.X j) ≫ (((strictAugmentation l E T).app P).f j).app (op n) = _ at h
  change (((strictAugmentation l E T).app P).f j).app (op n) = _
  exact (Category.id_comp _).symm.trans h

private def strictRoosAugmentation (T : Scheme.{u})
    (P : CochainComplex (AdicCompletion.Modules l E T) ℤ) :
    P ⟶ CochainComplex.mappingCocone
      (ExactProductsRoos.difference.app ((strictRed l E T).obj P)) :=
  CochainComplex.mappingCocone.lift _ (strictProductUnit l E T P) 0
    (by
      have h := congrArg CochainComplex.HomComplex.Cochain.ofHom
        (strictProductUnit_difference l E T P)
      simpa only [CochainComplex.HomComplex.Cochain.ofHom_zero,
        CochainComplex.HomComplex.δ_zero, zero_add] using h)

private theorem principalPositiveRoos (T : Scheme.{u})
    (P : CochainComplex (AdicCompletion.Modules l E T) ℤ) :
    ∃ c : DerivedCategory.Q.obj (CochainComplex.PrincipalCone.completion
        (principalScalar l E T P)) ≅
      DerivedCategory.Q.obj (CochainComplex.mappingCocone
        (ExactProductsRoos.difference.app ((strictRed l E T).obj P))),
      DerivedCategory.Q.map (CochainComplex.PrincipalCone.unit
          (principalScalar l E T P)) ≫ c.hom =
        DerivedCategory.Q.map (strictRoosAugmentation l E T P) := by
  let : CountableAB4Star (AdicCompletion.Modules l E T) :=
    .of_epi_π_app_zero (Mod.epiπAppZeroOfEpi
      Scheme.ProEt.epi_π_app_zero_of_epi_addCommGrpCat)
  let μ := principalScalar l E T P
  let X := ((strictRed l E T).obj P).asFunctor
  let t (n : ℕ) := X.map (homOfLE (Nat.le_succ n)).op
  let u (n : ℕ) : P ⟶ X.obj (op n) :=
    ((ev l E T n).mapHomologicalComplex (.up ℤ)).map
    ((strictAugmentation l E T).app P)
  have hs (n : ℕ) : u (n + 1) ≫ t n = u n := by
    have h := (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
      ((strictAugmentation l E T).app P)).naturality (homOfLE (Nat.le_succ n)).op
    change 𝟙 P ≫ u n = u (n + 1) ≫ t n at h
    simpa only [Category.id_comp] using h.symm
  have hz : Pi.lift u ≫ towerTransitionEndomorphism (K := fun n ↦ X.obj (op n)) t = 0 := by
    apply Pi.hom_ext
    intro n
    simp only [towerTransitionEndomorphism, towerProductShift, Preadditive.comp_sub,
      Preadditive.sub_comp,
      Category.comp_id, Category.assoc, Pi.lift_π, Pi.lift_π_assoc, hs, sub_self, zero_comp]
  obtain ⟨b, hb, hu⟩ := strictPrincipalLevels l E T P
  apply AdicCompletion.quotientTowerComparison μ (fun n ↦ X.obj (op n)) t u hz
    (fun n ↦ (b n).inv) (fun _ ↦ inferInstance)
  · intro n
    apply (cancel_epi (b (n + 1)).hom).1
    apply (cancel_mono (b n).hom).1
    simp only [Category.assoc, Category.comp_id, Iso.hom_inv_id_assoc, Iso.inv_hom_id]
    exact (hb n).symm
  · intro n
    apply (cancel_mono (b n).hom).1
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using (hu n).symm

private def negativeCoconeIso {A : Type*} [Category A] [Abelian A]
    {K L : CochainComplex A ℤ} (φ : K ⟶ L) :
    CochainComplex.mappingCocone φ ≅ CochainComplex.mappingCocone (-φ) :=
  (shiftFunctor _ (-1 : ℤ)).mapIso
    (coneIso φ (-φ) (Iso.refl K)
      (show L ≅ L from ⟨-𝟙 L, -𝟙 L, by simp, by simp⟩) (by simp))

private theorem negativeCoconeIso_lift {A : Type*} [Category A] [Abelian A]
    {P K L : CochainComplex A ℤ} (φ : K ⟶ L) (u : P ⟶ K) (hu : u ≫ φ = 0) :
    CochainComplex.mappingCocone.lift φ u 0 (by simp [hu]) ≫
        (negativeCoconeIso φ).hom =
      CochainComplex.mappingCocone.lift (-φ) u 0 (by simp [hu]) := by
  simpa only [negativeCoconeIso, Functor.mapIso_hom, coneIso, Iso.refl_hom,
    Category.id_comp, Category.comp_id] using
    (AdicCompletion.zeroLift_natural A φ (-φ) (𝟙 K) (-𝟙 L) (by simp)
      (𝟙 P) u u hu (by simp [hu]) (by simp)).symm

-- Normalize the identity cone map before instantiating its objects with tower products.

private theorem zeroLift_comp
    {A : Type*} [Category A] [Abelian A]
    {C D K L : CochainComplex A ℤ}
    (φ : K ⟶ L) (α : C ⟶ D) (u : C ⟶ K) (v : D ⟶ K)
    (hu : u ≫ φ = 0) (hv : v ≫ φ = 0) (hn : α ≫ v = u) :
    α ≫ CochainComplex.mappingCocone.lift φ v 0 (by simp [hv]) =
      CochainComplex.mappingCocone.lift φ u 0 (by simp [hu]) := by
  have h := AdicCompletion.zeroLift_natural A φ φ (𝟙 _) (𝟙 _) (by simp)
    α u v hu hv (by simpa only [Category.comp_id] using hn)
  simp only [CochainComplex.mappingCone.map_id, CategoryTheory.Functor.map_id] at h
  refine h.trans ?_
  apply HomologicalComplex.Hom.ext
  funext j
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f]
  erw [Category.comp_id]

private theorem adjointRoosAugmentation (T : Scheme.{u})
    (P : CochainComplex (AdicCompletion.Modules l E T) ℤ) :
    (((constLimAdj : constant l E T ⊣ inverseLimit l E T).mapHomologicalComplex (.up ℤ)).homEquiv
        P ((strictRed l E T).obj P) ((strictAugmentation l E T).app P)) ≫
        ExactProductsRoos.comparison.app ((strictRed l E T).obj P) =
      strictRoosAugmentation l E T P ≫
        (negativeCoconeIso
          (ExactProductsRoos.difference.app ((strictRed l E T).obj P))).hom := by
  let A := AdicCompletion.Modules l E T
  let X := (strictRed l E T).obj P
  let α := (strictAugmentation l E T).app P
  let a := (constLimAdj : constant l E T ⊣ inverseLimit l E T).mapHomologicalComplex (.up ℤ)
  let h := a.homEquiv P X α
  have hi : h ≫ ExactProductsRoos.inclusion.app X = strictProductUnit l E T P := by
    apply Pi.hom_ext
    intro n
    have hπ : strictProductUnit l E T P ≫
        Pi.π (fun n : ℕ ↦ X.asFunctor.obj (op n)) n =
          ((ev l E T n).mapHomologicalComplex (.up ℤ)).map α := Pi.lift_π _ n
    rw [hπ]
    change (h ≫ (Pi.lift (f := fun n : ℕ ↦ X.asFunctor.obj (op n))
      (fun n : ℕ ↦ (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app X))) ≫
        Pi.π (fun n : ℕ ↦ X.asFunctor.obj (op n)) n = _
    rw [Category.assoc, Pi.lift_π]
    apply HomologicalComplex.Hom.ext
    funext j
    have he := (a.homEquiv P X).symm_apply_apply α
    rw [Adjunction.homEquiv_counit] at he
    exact congrArg (fun f ↦ (f.f j).app (op n)) he
  have hu := strictProductUnit_difference l E T P
  have hz := ExactProductsRoos.inclusion_difference X
  have hni : h ≫ ExactProductsRoos.comparison.app X =
      CochainComplex.mappingCocone.lift (-ExactProductsRoos.difference.app X)
        (strictProductUnit l E T P) 0 (by
          rw [Preadditive.comp_neg, hu, neg_zero]
          simp) := by
    exact zeroLift_comp (-ExactProductsRoos.difference.app X) h
      (strictProductUnit l E T P) (ExactProductsRoos.inclusion.app X)
      (by rw [Preadditive.comp_neg, hu, neg_zero])
      (by rw [Preadditive.comp_neg, hz, neg_zero]) hi
  exact hni.trans (negativeCoconeIso_lift
    (ExactProductsRoos.difference.app X) (strictProductUnit l E T P) hu).symm

private def coneEvaluationComparison (T : Scheme.{u}) (n : ℕ) :
    strictRed l E T ⋙ (ev l E T n).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ≅
      DerivedNakayama.coneFunctor l E T (uniformizer l E ^ (n + 1)) := by
  let τ : 𝟭 (CochainComplex (AdicCompletion.Modules l E T) ℤ) ⟶ 𝟭 _ :=
    Functor.whiskerRight (complexPowerMap l E T)
      ((ev l E T n).mapHomologicalComplex (.up ℤ))
  let e : strictRed l E T ⋙ (ev l E T n).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ≅ DerivedNakayama.UnitScalar.coneOf τ :=
    NatIso.ofComponents (fun P ↦ DerivedCategory.Q.mapIso
      (CochainComplex.mappingCone.mapHomologicalComplexIso
        ((complexPowerMap l E T).app P) (ev l E T n))) (by
          intro P Q a
          change (DerivedCategory.Q (C := AdicCompletion.Modules l E T)).map _ ≫
              DerivedCategory.Q.map _ = DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map _
          rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
          apply DerivedCategory.Q.congr_map
          exact ConeNaturality.mapCone_natural (ev l E T n)
            ((complexPowerMap l E T).app P) ((complexPowerMap l E T).app Q)
            (((scalarTower l E T).mapHomologicalComplex (.up ℤ)).map a)
            (((constant l E T).mapHomologicalComplex (.up ℤ)).map a)
            ((complexPowerMap l E T).naturality a).symm)
  refine e ≪≫ eqToIso ?_
  change DerivedNakayama.UnitScalar.coneOf
    (Functor.whiskerRight (complexPowerMap l E T)
      ((ev l E T n).mapHomologicalComplex (.up ℤ))) = _
  rw [evaluatedPowerMap]
  rfl

/-- Evaluation of the derived cone tower is naturally the actual finite reduction.
Source: blueprint Assertion 5, the two-term uniformizer resolution
(blueprint: det-pbc-complete-derived-completion).
Proof: exact evaluation carries the tower cone to the scalar cone. Scalar action
preserves powers. The coefficient resolution identifies that cone with derived tensor
by the finite coefficient module. The K-flat scalar comparison identifies this tensor
with restriction of the canonical derived scalar extension. Fully faithful
precomposition with localization descends the resulting natural isomorphism. -/
theorem reductionEvaluation (T : Scheme.{u}) (n : ℕ) :
    Nonempty (red l E T ⋙ dev l E T n ≅
      AdicCompletion.derivedReduction l E T n ⋙ AdicCompletion.restrict l E T n) := by
  obtain ⟨r, _, i, q, _, _, h⟩ :=
    (DerivedNakayama.derived_nakayama_resolution l E).choose_spec.2
  obtain ⟨e, _⟩ := (h T (n + 1) (Nat.succ_le_succ (Nat.zero_le n))).2
  obtain ⟨s⟩ := finiteScalarComparison l E T n
  let e' : DerivedCategory.Q ⋙ (red l E T ⋙ dev l E T n) ≅
      DerivedNakayama.coneFunctor l E T (uniformizer l E ^ (n + 1)) :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (redFactors l E T) (dev l E T n) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (strictRed l E T) (ev l E T n).mapDerivedCategoryFactors ≪≫
      coneEvaluationComparison l E T n
  exact ⟨(Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso (AdicCompletion.Modules l E T) (.up ℤ))
    (DerivedCategory (AdicCompletion.Modules l E T))).preimageIso
      (e' ≪≫ e.some.symm ≪≫ Functor.isoWhiskerLeft DerivedCategory.Q s)⟩

/-- All derived evaluations, assembled into a diagram functor.
Source: blueprint Assertion 2 (blueprint: det-pbc-complete-derived-completion).
The transition transformations descend the ordinary evaluation transformations;
localization is fully faithful on natural transformations and preserves their composition. -/
private def evaluationDiagram (T : Scheme.{u}) :
    ℕᵒᵖ ⥤ (DTow l E T ⥤ DerivedCategory (AdicCompletion.Modules l E T)) where
  obj n := dev l E T n.unop
  map t := towerDerivedEvaluationTransition (AdicCompletion.Modules l E T) t
  map_id n := by
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (Tow l E T) (.up ℤ))
    intro I
    apply (cancel_mono ((ev l E T n.unop).mapDerivedCategoryFactors.hom.app I)).1
    rw [towerTransition_fac]
    simp
  map_comp t t' := by
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (Tow l E T) (.up ℤ))
    intro I
    apply (cancel_mono ((ev l E T _).mapDerivedCategoryFactors.hom.app I)).1
    rw [towerTransition_fac]
    change _ = (_ ≫ _) ≫ _
    rw [Category.assoc, towerTransition_fac, ← Category.assoc, towerTransition_fac,
      Category.assoc, ← DerivedCategory.Q.map_comp]
    congr 2
    apply HomologicalComplex.Hom.ext
    funext j
    exact (I.X j).map_comp t t'

private def evaluationDiagramFactors (T : Scheme.{u}) :
    DerivedCategory.Q ⋙ (evaluationDiagram l E T).flip ≅
      HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
        (Functor.whiskeringRight ℕᵒᵖ _ _).obj DerivedCategory.Q :=
  NatIso.ofComponents (fun I ↦ NatIso.ofComponents
    (fun n ↦ (ev l E T n.unop).mapDerivedCategoryFactors.app I)
    (fun t ↦ towerTransition_fac (AdicCompletion.Modules l E T) t I))
    (fun a ↦ by
      ext n
      exact (ev l E T n.unop).mapDerivedCategoryFactors.hom.naturality a)

/-- Derived inverse limit is a Milnor fibre for the specified derived evaluations.
Source: blueprint Assertion 4, Stacks Tags 0940 and 0941
(blueprint: det-pbc-complete-derived-completion).
Proof: assemble the exact evaluations into a diagram-valued localization. On a
K-injective resolution the inverse-limit inclusion is the kernel of the surjective
product difference. Its short exact sequence gives the Milnor triangle. Descend
that natural triangle to all derived towers using the normalized right derived unit. -/
theorem derivedLimit (T : Scheme.{u}) :
    ∃ (_products : HasCountableProducts (DerivedCategory (AdicCompletion.Modules l E T))),
      ∀ M : DTow l E T,
        IsDerivedLimit (K := fun n : ℕ ↦ (dev l E T n).obj M)
          (fun n : ℕ ↦ (transition l E T n).app M) ((rlim l E T).obj M) := by
  let hp : HasCountableProducts (DerivedCategory (AdicCompletion.Modules l E T)) :=
    derivedCountableProducts
  let η : (inverseLimit l E T).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ rlim l E T :=
    { app := (inverseLimit l E T).rightDerivedFunctorUnitQ
      naturality _ _ a := (inverseLimit l E T).rightDerivedFunctorUnitQ_naturality a }
  have hI (I : CochainComplex (Tow l E T) ℤ) (hI : I.IsKInjective) :
      IsIso (η.app I) := by
    let := hI
    change IsIso ((inverseLimit l E T).rightDerivedFunctorUnitQ I)
    rw [Functor.rightDerivedFunctorUnitQ_eq]
    infer_instance
  obtain ⟨p, δ, h, _, _⟩ := CoreWork.natural_roos (rlim l E T) η hI
    (evaluationDiagram l E T).flip (evaluationDiagramFactors l E T)
  exact ⟨hp, fun M ↦ ⟨p M, δ M, h M⟩⟩

private theorem cochainAdjunctionUnit
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions B]
    {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (a : F ⊣ G) (P : CochainComplex A ℤ) :
    a.mapDerivedCategoryRightDerivedAdjunction.unit.app (DerivedCategory.Q.obj P) ≫
        G.rightDerivedFunctor.map (F.mapDerivedCategoryFactors.hom.app P) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
        UnboundedExactTower.cochainUnit G ((F.mapHomologicalComplex (.up ℤ)).obj P) := by
  change (a.mapDerivedCategoryRightDerivedAdjunction.homEquiv _ _)
    (F.mapDerivedCategoryFactors.hom.app P) = _
  apply (a.mapDerivedCategoryRightDerivedAdjunction.homEquiv _ _).symm.injective
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit,
    F.mapDerivedCategory.map_comp, Category.assoc]
  erw [UnboundedExactTower.cochain_counit a ((F.mapHomologicalComplex (.up ℤ)).obj P)]
  erw [← Category.assoc, F.mapDerivedCategoryFactors.hom.naturality,
    Category.assoc, ← DerivedCategory.Q.map_comp]
  have ht := (a.mapHomologicalComplex (.up ℤ)).left_triangle_components P
  rw [ht, (DerivedCategory.Q (C := B)).map_id
    ((F.mapHomologicalComplex (.up ℤ)).obj P)]
  exact (Category.comp_id _).symm

private theorem augmentation_fac (T : Scheme.{u})
    (P : CochainComplex (AdicCompletion.Modules l E T) ℤ) :
    (augmentation l E T).app (DerivedCategory.Q.obj P) ≫ (redFactors l E T).hom.app P =
      (constant l E T).mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map ((strictAugmentation l E T).app P) := by
  simp only [augmentation, Localization.liftNatTrans_app, Functor.whiskerRight_app]
  change (_ ≫ DerivedCategory.Q.map ((strictAugmentation l E T).app P) ≫
    (redFactors l E T).inv.app P) ≫ (redFactors l E T).hom.app P = _
  simp only [Category.assoc, Iso.inv_hom_id_app]
  simp only [Localization.Lifting.iso]
  exact congrArg (fun g ↦ (constant l E T).mapDerivedCategoryFactors.hom.app P ≫ g)
    (Category.comp_id (DerivedCategory.Q.map ((strictAugmentation l E T).app P)))

private def cochainDerivedUnit {A B : Type*} [Category A] [Category B]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
    [Abelian.HasKInjectiveResolutions A] (G : A ⥤ B) [G.Additive] :
    G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ G.rightDerivedFunctor :=
  (Functor.isoWhiskerLeft (G.mapHomologicalComplex (.up ℤ))
      (DerivedCategory.quotientCompQhIso B)).inv ≫
    Functor.whiskerRight (G.mapHomotopyCategoryFactors (.up ℤ)).inv DerivedCategory.Qh ≫
    Functor.whiskerLeft (HomotopyCategory.quotient A (.up ℤ)) G.rightDerivedFunctorUnit ≫
    Functor.whiskerRight (DerivedCategory.quotientCompQhIso A).hom G.rightDerivedFunctor

private theorem roosComparisonNormalized (T : Scheme.{u}) :
    ∃ e : ExactProductsRoos.fibre ⋙
        (DerivedCategory.Q (C := AdicCompletion.Modules l E T)) ≅
      (DerivedCategory.Q (C := Tow l E T)) ⋙ rlim l E T,
      ∀ I : CochainComplex (Tow l E T) ℤ,
        DerivedCategory.Q.map (ExactProductsRoos.comparison.app I) ≫ e.hom.app I =
          UnboundedExactTower.cochainUnit (inverseLimit l E T) I := by
  let : CountableAB4Star (AdicCompletion.Modules l E T) :=
    .of_epi_π_app_zero (Mod.epiπAppZeroOfEpi
      Scheme.ProEt.epi_π_app_zero_of_epi_addCommGrpCat)
  obtain ⟨e, he⟩ := ExactProductsRoos.comparisonIso (rlim l E T)
    (cochainDerivedUnit (inverseLimit l E T))
    (fun I hI ↦ by
      let := hI
      exact UnboundedExactTower.cochainUnit_isIso (G := inverseLimit l E T) I)
  exact ⟨e, fun I ↦ NatTrans.congr_app he I⟩

/-- On complexes the specified completion unit is the derived ordinary adjoint
of the degree-zero cone inclusion.
Source: blueprint Notation 4 (blueprint: det-pbc-complete-derived-completion).
Proof: apply the factorization equation of the localized augmentation, the derived
adjunction unit formula, and naturality of the total right derived cochain comparison. -/
private theorem kappa_on_complex (T : Scheme.{u})
    (P : CochainComplex (AdicCompletion.Modules l E T) ℤ) :
    (kappa l E T).app (DerivedCategory.Q.obj P) ≫
        (rlim l E T).map ((redFactors l E T).hom.app P) =
      DerivedCategory.Q.map
          (((constLimAdj : constant l E T ⊣ inverseLimit l E T).mapHomologicalComplex
            (.up ℤ)).homEquiv P ((strictRed l E T).obj P)
              ((strictAugmentation l E T).app P)) ≫
        UnboundedExactTower.cochainUnit (inverseLimit l E T) ((strictRed l E T).obj P) := by
  dsimp only [kappa, NatTrans.comp_app, Functor.whiskerRight_app]
  rw [Category.assoc, ← (rlim l E T).map_comp, augmentation_fac,
    (rlim l E T).map_comp, ← Category.assoc]
  erw [cochainAdjunctionUnit (constLimAdj : constant l E T ⊣ inverseLimit l E T)]
  rw [Category.assoc]
  erw [← (cochainDerivedUnit (inverseLimit l E T)).naturality
    ((strictAugmentation l E T).app P)]
  simp only [Functor.comp_map]
  rw [← Category.assoc, ← DerivedCategory.Q.map_comp, Adjunction.homEquiv_unit]
  rfl

private theorem principalCompletionComparison (T : Scheme.{u})
    (P : CochainComplex (AdicCompletion.Modules l E T) ℤ) :
    ∃ b : DerivedCategory.Q.obj (CochainComplex.PrincipalCone.completion
        (principalScalar l E T P)) ≅
      (completion l E T).obj (DerivedCategory.Q.obj P),
      DerivedCategory.Q.map (CochainComplex.PrincipalCone.unit
          (principalScalar l E T P)) ≫ b.hom =
        (kappa l E T).app (DerivedCategory.Q.obj P) := by
  obtain ⟨a, ha⟩ := principalPositiveRoos l E T P
  obtain ⟨e, he⟩ := roosComparisonNormalized l E T
  let X := (strictRed l E T).obj P
  let z := DerivedCategory.Q.mapIso
    (negativeCoconeIso (ExactProductsRoos.difference.app X))
  let r := (rlim l E T).mapIso ((redFactors l E T).app P)
  let b := a ≪≫ z ≪≫ e.app X ≪≫ r.symm
  refine ⟨b, ?_⟩
  apply (cancel_mono r.hom).1
  dsimp only [b, Iso.trans_hom, Iso.symm_hom, Iso.app_hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, ← Category.assoc, ha]
  change (DerivedCategory.Q.map (strictRoosAugmentation l E T P) ≫
    DerivedCategory.Q.map (negativeCoconeIso (ExactProductsRoos.difference.app X)).hom) ≫
      e.hom.app X = _
  rw [← DerivedCategory.Q.map_comp, ← adjointRoosAugmentation,
    DerivedCategory.Q.map_comp, Category.assoc, he]
  exact (kappa_on_complex l E T P).symm

/-- The quotient Roos complex represents the specified completion, preserving its unit.
Source: blueprint Notation 4, Stacks Tags 099B, 0A0E and 0941
(blueprint: det-pbc-complete-derived-completion).
Proof: evaluate the strict reduction cone tower and identify it, with its transitions
and degree-zero inclusions, with the principal power-cone tower. Exact products give
its Roos comparison. Change the sign of the second product to match the normalized
right-derived-limit comparison. The ordinary constant/limit adjoint of the strict
inclusion followed by that comparison is exactly kappa. Finally the K-flat principal
cone-to-quotient comparison identifies its strict augmentation with the quotient unit. -/
theorem completionComparison_on_complex (T : Scheme.{u})
    (P : CochainComplex (AdicCompletion.Modules l E T) ℤ)
    (hP : (HomologicalComplex.quasiIso (AdicCompletion.Modules l E T) (.up ℤ)).kFlat P) :
    ∃ ε : DerivedCategory.Q.obj (AdicCompletion.roos l E T P) ≅
        (completion l E T).obj (DerivedCategory.Q.obj P),
      DerivedCategory.Q.map (AdicCompletion.augmentation l E T P) ≫ ε.hom =
        (kappa l E T).app (DerivedCategory.Q.obj P) := by
  obtain ⟨c, hc⟩ := AdicCompletion.internal_quotient_principal_cone_comparison l E T
    (uniformizer l E) (DerivedNakayama.derived_nakayama_resolution l E).choose_spec.1 P hP
  obtain ⟨b, hb⟩ := principalCompletionComparison l E T P
  refine ⟨c.symm ≪≫ b, ?_⟩
  rw [Iso.trans_hom, Iso.symm_hom, ← hc, Category.assoc, Iso.hom_inv_id_assoc]
  exact hb

/-- Every K-flat representative has the normalized comparison required by Notation 4.
Source: blueprint Notation 4 (blueprint: det-pbc-complete-derived-completion).
Proof: compose the complex comparison with the image of the representative isomorphism.
Naturality of kappa cancels that representative on the specified completion map. -/
theorem completionComparison (T : Scheme.{u})
    (M : DerivedCategory (AdicCompletion.Modules l E T))
    (P : CochainComplex (AdicCompletion.Modules l E T) ℤ)
    (hP : (HomologicalComplex.quasiIso (AdicCompletion.Modules l E T) (.up ℤ)).kFlat P)
    (e : DerivedCategory.Q.obj P ≅ M) :
    ∃ ε : DerivedCategory.Q.obj (AdicCompletion.roos l E T P) ≅
        (completion l E T).obj M,
      AdicCompletion.completionMap l E T M P e ≫ ε.hom = (kappa l E T).app M := by
  obtain ⟨a, ha⟩ := completionComparison_on_complex l E T P hP
  refine ⟨a ≪≫ (completion l E T).mapIso e, ?_⟩
  change (e.inv ≫ DerivedCategory.Q.map (AdicCompletion.augmentation l E T P)) ≫
    (a.hom ≫ (completion l E T).map e.hom) = _
  rw [Category.assoc, ← Category.assoc (DerivedCategory.Q.map _), ha,
    ← (kappa l E T).naturality e.hom]
  simp

private theorem existsKFlatRepresentative (T : Scheme.{u})
    (M : DerivedCategory (AdicCompletion.Modules l E T)) :
    ∃ (P : CochainComplex (AdicCompletion.Modules l E T) ℤ),
      (HomologicalComplex.quasiIso (AdicCompletion.Modules l E T) (.up ℤ)).kFlat P ∧
        Nonempty (DerivedCategory.Q.obj P ≅ M) := by
  obtain ⟨P, q, hq, _, hP⟩ := CochainComplex.exists_quasiIso_flat_kFlat
    (DerivedCategory.Q.objPreimage M)
  let := hq
  exact ⟨P, hP, ⟨asIso (DerivedCategory.Q.map q) ≪≫ DerivedCategory.Q.objObjPreimageIso M⟩⟩

/-- Completeness is equivalent to invertibility of the specified completion unit.
Source: blueprint Notation 4 (blueprint: det-pbc-complete-derived-completion).
Proof: choose a K-flat representative and use the normalized quotient Roos comparison.
The existing representative-independent completeness criterion applies to its unit. -/
theorem isDerivedComplete_iff (T : Scheme.{u})
    (M : DerivedCategory (AdicCompletion.Modules l E T)) :
    IsDerivedComplete l E T M ↔ IsIso ((kappa l E T).app M) := by
  obtain ⟨P, hP, ⟨e⟩⟩ := existsKFlatRepresentative l E T M
  obtain ⟨ε, hε⟩ := completionComparison l E T M P hP e
  rw [AdicCompletion.isDerivedComplete_iff l E T M P hP e, ← hε]
  exact (isIso_comp_right_iff (AdicCompletion.completionMap l E T M P e) ε.hom).symm

/-- The output of completion is derived complete for every input.
Source: blueprint Assertion 6 and Stacks Tag 099B
(blueprint: det-pbc-complete-derived-completion).
Proof: on a K-flat representative the completion is isomorphic to the quotient Roos
output, whose completeness is already proved by the singleton Koszul reflector.
Transport the witnessing K-flat representative along this isomorphism. -/
theorem completion_isDerivedComplete (T : Scheme.{u})
    (M : DerivedCategory (AdicCompletion.Modules l E T)) :
    IsDerivedComplete l E T ((completion l E T).obj M) := by
  obtain ⟨P, hP, ⟨e⟩⟩ := existsKFlatRepresentative l E T M
  obtain ⟨ε, _⟩ := completionComparison l E T M P hP e
  obtain ⟨R, hR, ⟨r⟩, hr⟩ := AdicCompletion.isDerivedComplete_roos l E T P hP
  exact ⟨R, hR, ⟨r ≪≫ ε⟩, hr⟩

/-- The canonical evaluation mates commute with successor transitions.
Source: blueprint Assertion 3, Stacks Tag 0A07
(blueprint: det-pbc-complete-derived-completion).
Proof: apply uniqueness of the normalized tower evaluation comparison. The canonical
mate has exactly that normalization on K-injective complexes, and the uniquely
normalized family commutes with every tower transition. -/
theorem pushEvaluation_transition {T T' : Scheme.{u}} (f : T' ⟶ T) (n : ℕ)
    (M : DTow l E T') :
    (transition l E T n).app ((rpush l E f).obj M) ≫
        (pushEvaluationMap l E f n).app M =
      (pushEvaluationMap l E f (n + 1)).app M ≫
        (rpushModule l E f).map ((transition l E T' n).app M) := by
  let G := CondensedRing.lowerStar (DerivedNakayama.integerRing l E) f
  let GT := (Functor.whiskeringRight ℕᵒᵖ _ _).obj G
  let η : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ G.rightDerivedFunctor :=
    cochainDerivedUnit G
  let ηT : GT.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ GT.rightDerivedFunctor :=
    cochainDerivedUnit GT
  let : G.rightDerivedFunctor.IsRightDerivedFunctor η
      (HomologicalComplex.quasiIso _ (.up ℤ)) := by
    apply (derives G).isRightDerivedFunctor_of_isIso
    intro I
    have : I.obj.IsKInjective := I.property
    exact UnboundedExactTower.cochainUnit_isIso (G := G) I.obj
  let : GT.rightDerivedFunctor.IsRightDerivedFunctor ηT
      (HomologicalComplex.quasiIso _ (.up ℤ)) := by
    apply (derives GT).isRightDerivedFunctor_of_isIso
    intro I
    have : I.obj.IsKInjective := I.property
    exact UnboundedExactTower.cochainUnit_isIso (G := GT) I.obj
  obtain ⟨d, dT, _, _, β, _, huniq, htrans, _⟩ :=
    exists_unique_towerDerivedEvaluation_normalized
      (CondensedRing.upperStar (DerivedNakayama.integerRing l E) f) G
      (CondensedRing.upperStarLowerStarAdjunction (DerivedNakayama.integerRing l E) f)
      G.rightDerivedFunctor GT.rightDerivedFunctor η ηT
  have hβ (k : ℕ) : asIso (pushEvaluationMap l E f k) = β (op k) := by
    apply huniq
    intro I hI
    exact UnboundedExactTower.evaluation_normalization
        (CondensedRing.upperStarLowerStarAdjunction (DerivedNakayama.integerRing l E) f)
        (op k) I
  have h := htrans (op (n + 1)) (op n) (homOfLE (Nat.le_succ n)).op M
  rw [← hβ n, ← hβ (n + 1)] at h
  exact h

private theorem scalarSource_reduction_zero (T : Scheme.{u})
    (P : CochainComplex (AdicCompletion.Modules l E T) ℤ) (n : ℕ) :
    IsZero ((DerivedNakayama.reductionFunctor l E T (n + 1)).obj
      ((rlim l E T).obj (DerivedCategory.Q.obj
        (((scalarTower l E T).mapHomologicalComplex (.up ℤ)).obj P)))) := by
  let A := AdicCompletion.Modules l E T
  let : Linear (CatCenter A) A := Linear.ofRingMorphism (RingHom.id (CatCenter A))
  let r : CatCenter A := scalar l E T
  let X := ((scalarTower l E T).mapHomologicalComplex (.up ℤ)).obj P
  let V := ∏ᶜ (fun _ : ℕ ↦ P)
  let a : V ⟶ V := Limits.Pi.map (fun _ : ℕ ↦ r • 𝟙 P)
  let b : V ⟶ V := Pi.lift (fun n : ℕ ↦ Pi.π (fun _ : ℕ ↦ P) (n + 1))
  have hscalar (C : CochainComplex A ℤ) :
      r • 𝟙 C = DerivedNakayama.scalarOnComplex l E T (uniformizer l E) C := by
    apply HomologicalComplex.Hom.ext
    funext j
    change (scalar l E T).app (C.X j) ≫ 𝟙 _ = (scalar l E T).app (C.X j)
    exact Category.comp_id _
  have ht (n : ℕ) : X.asFunctor.map (homOfLE (Nat.le_succ n)).op = r • 𝟙 P := by
    rw [hscalar]
    apply HomologicalComplex.Hom.ext
    funext j
    change ((Functor.ofOpSequence
      (X := fun _ : ℕ ↦ 𝟭 A) (fun _ ↦ scalar l E T)).map
        (homOfLE (Nat.le_succ n)).op).app (P.X j) = _
    rw [Functor.ofOpSequence_map_homOfLE_succ]
    rfl
  have hd : ExactProductsRoos.difference.app X = 𝟙 V - b ≫ a := by
    apply Pi.hom_ext
    intro n
    simp only [towerTransitionEndomorphism, towerProductShift,
      Preadditive.sub_comp, Category.id_comp, Category.assoc, Pi.lift_π, ht]
    change Pi.π (fun _ : ℕ ↦ P) n - Pi.π (fun _ : ℕ ↦ P) (n + 1) ≫ (r • 𝟙 P) =
      𝟙 V ≫ Pi.π (fun _ : ℕ ↦ P) n - b ≫ a ≫ Pi.π (fun _ : ℕ ↦ P) n
    simp only [Category.id_comp, a, b, Pi.map_π, Pi.lift_π_assoc]
  have hq : QuasiIso
      (DerivedNakayama.scalarOnComplex l E T (uniformizer l E)
        (ExactProductsRoos.fibre.obj X)) := by
    rw [← hscalar]
    change QuasiIso (r • 𝟙 (CochainComplex.mappingCocone
      (-ExactProductsRoos.difference.app X)))
    rw [hd]
    exact CochainComplex.scalarTowerProductFibre_scalar_quasiIso P r
  let F := ExactProductsRoos.fibre.obj X
  have hi : IsIso (DerivedCategory.Q.map (principalScalar l E T F)) := by
    let := hq
    exact inferInstanceAs (IsIso (DerivedCategory.Q.map
      (DerivedNakayama.scalarOnComplex l E T (uniformizer l E) F)))
  have hip : IsIso (DerivedCategory.Q.map
      (DerivedNakayama.scalarOnComplex l E T (uniformizer l E ^ (n + 1)) F)) := by
    rw [scalarOnComplex_pow]
    change IsIso ((DerivedCategory.Q.mapEnd F) (principalScalar l E T F ^ (n + 1)))
    rw [map_pow]
    exact (isUnit_iff_isIso _).1 (((isUnit_iff_isIso _).2 hi).pow (n + 1))
  have hz := (DerivedCategory.Q.mapTriangle.obj
    (CochainComplex.mappingCone.triangle
      (DerivedNakayama.scalarOnComplex l E T (uniformizer l E ^ (n + 1)) F))).isZero₃_of_isIso₁
    (DerivedCategory.mappingCone_triangle_distinguished _) hip
  obtain ⟨r₀, _, i, q, _, _, h⟩ :=
    (DerivedNakayama.derived_nakayama_resolution l E).choose_spec.2
  obtain ⟨e⟩ := (h T (n + 1) (Nat.succ_pos n)).2.1
  have hzF : IsZero ((DerivedNakayama.reductionFunctor l E T (n + 1)).obj
      (DerivedCategory.Q.obj F)) := hz.of_iso (e.app F)
  obtain ⟨c⟩ := roosComparison l E T
  exact hzF.of_iso
    ((DerivedNakayama.reductionFunctor l E T (n + 1)).mapIso (c.app X))

private theorem finiteReduction_kappa_complex (T : Scheme.{u})
    (P : CochainComplex (AdicCompletion.Modules l E T) ℤ) (n : ℕ) :
    IsIso ((DerivedNakayama.reductionFunctor l E T (n + 1)).map
      ((kappa l E T).app (DerivedCategory.Q.obj P))) := by
  let F := DerivedNakayama.reductionFunctor l E T (n + 1)
  let K := (DerivedCategory.singleFunctor (AdicCompletion.Modules l E T) 0).obj
    ((DerivedNakayama.pullback l E T).obj (DerivedNakayama.quotientModule l E (n + 1)))
  let : F.CommShift ℤ := DerivedCategory.commShiftTensorRight
    (C := AdicCompletion.Modules l E T) K
  let : F.IsTriangulated := DerivedCategory.isTriangulated_tensorRight
    (C := AdicCompletion.Modules l E T) K
  let c := (complexPowerMap l E T).app P
  have htri := F.map_distinguished _ ((rlim l E T).map_distinguished _
    (DerivedCategory.mappingCone_triangle_distinguished c))
  have hz := scalarSource_reduction_zero l E T P n
  have hi : IsIso (F.map ((rlim l E T).map
      (DerivedCategory.Q.map ((strictAugmentation l E T).app P)))) :=
    (Pretriangulated.Triangle.isZero₁_iff_isIso₂
      (F.mapTriangle.obj ((rlim l E T).mapTriangle.obj
        (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle c)))) htri).1 hz
  have haug : IsIso (F.map ((rlim l E T).map
      ((augmentation l E T).app (DerivedCategory.Q.obj P)))) := by
    apply (isIso_comp_right_iff _ (F.map ((rlim l E T).map
      ((redFactors l E T).hom.app P)))).1
    rw [← F.map_comp, ← (rlim l E T).map_comp, augmentation_fac,
      (rlim l E T).map_comp, F.map_comp]
    infer_instance
  have := constantLimitUnit_isIso l E T (DerivedCategory.Q.obj P)
  change IsIso (F.map ((constantLimitAdjunction l E T).unit.app _ ≫
    (rlim l E T).map ((augmentation l E T).app _)))
  rw [F.map_comp]
  infer_instance

/-- Finite reduction inverts the specified completion unit.
Source: blueprint Assertion 6, Stacks Tags 0941 and 099B
(blueprint: det-pbc-complete-derived-completion).
Proof: the uniformizer is invertible on the derived limit of the scalar source tower:
its inverse is the index shift up to homotopy on the Roos fibre. Every quotient-power
reduction of that limit is therefore zero, by the uniformizer cone resolution. Apply
reduction and derived inverse limit to the source-constant-cone triangle. Its first
term vanishes, so its second arrow is invertible. This arrow, preceded by the
invertible constant-limit unit, is precisely kappa. Finally use exact conservative
restriction of quotient coefficients and invariance under the choice of complex. -/
theorem finiteReduction_kappa (T : Scheme.{u})
    (M : DerivedCategory (AdicCompletion.Modules l E T)) (n : ℕ) :
    IsIso ((AdicCompletion.derivedReduction l E T n).map ((kappa l E T).app M)) := by
  let P := DerivedCategory.Q.objPreimage M
  let e := DerivedCategory.Q.objObjPreimageIso M
  have hi := finiteReduction_kappa_complex l E T P n
  have hM : IsIso ((DerivedNakayama.reductionFunctor l E T (n + 1)).map
      ((kappa l E T).app M)) := by
    apply (isIso_comp_left_iff
      ((DerivedNakayama.reductionFunctor l E T (n + 1)).map e.hom) _).1
    have hn : e.hom ≫ (kappa l E T).app M =
        (kappa l E T).app (DerivedCategory.Q.obj P) ≫ (completion l E T).map e.hom :=
      (kappa l E T).naturality e.hom
    rw [← CategoryTheory.Functor.map_comp, hn, CategoryTheory.Functor.map_comp]
    infer_instance
  obtain ⟨c⟩ := finiteScalarComparison l E T n
  have hres : IsIso ((AdicCompletion.restrict l E T n).map
      ((AdicCompletion.derivedReduction l E T n).map ((kappa l E T).app M))) :=
    (NatIso.isIso_map_iff c ((kappa l E T).app M)).1 hM
  let G : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (AdicCompletion.finiteRing l E T n) ⥤ AdicCompletion.Modules l E T :=
    Mod.comap (AdicCompletion.quotient l E T n)
  let : IsIso (G.mapDerivedCategory.map
      ((AdicCompletion.derivedReduction l E T n).map ((kappa l E T).app M))) := hres
  apply (DerivedCategory.isIso_iff _ _).2
  intro j
  let hj : IsIso (G.map ((DerivedCategory.homologyFunctor _ j).map
      ((AdicCompletion.derivedReduction l E T n).map ((kappa l E T).app M)))) :=
    (NatIso.isIso_map_iff (G.mapDerivedCategoryHomologyFunctorIso j) _).2 (by
      change IsIso ((DerivedCategory.homologyFunctor (AdicCompletion.Modules l E T) j).map
        (G.mapDerivedCategory.map
          ((AdicCompletion.derivedReduction l E T n).map ((kappa l E T).app M))))
      infer_instance)
  exact isIso_of_reflects_iso _ G

end CompleteDerivedCompletion

/-- All six assertions about integral module towers and their derived completion.
Source: blueprint Notation 1--4 and Assertions 1--6
(blueprint: det-pbc-complete-derived-completion).

Proof:
1. The base module category is Grothendieck. Free diagrams on a separator form a separating
   family; their coproduct is a separator for towers. Filtered colimits are exact levelwise.
2. Evaluation has the usual free-diagram left adjoint. The indexing Hom sets are subsingletons,
   so its finite-limit preservation follows from finite coproduct exactness. The exact-adjoint
   K-injective theorem applies. Derived evaluations jointly reflect isomorphisms by cohomology.
3. Derive the levelwise module adjunction. Evaluation preserves K-injectives, so the normalized
   exact-adjunction square proves that the canonical pushforward mate is an isomorphism. The
   mates identities give its unit/counit equations, and normalized uniqueness gives transitions.
4. Conjugating the constant-pullback comparison under the derived adjunctions gives pushLimitIso.
   The same construction with an equivalence and its inverse gives equivalenceLimitIso.
5. Products of integral module sheaves are exact. The normalized exact-products Roos comparison
   computes the specified Rlim and gives the distinguished derived-limit triangle. Evaluation
   at terminal index zero is left adjoint to constants, so derived constants are fully faithful;
   the specified constant-limit unit is therefore invertible.
6. Give towers functorial flat covers levelwise. Constants are exact strong monoidal and preserve
   flat objects. A bounded finite-free complex is dualizable in the derived category, so the
   adjoint projection formula gives its tensor/limit isomorphism. K-flat realization identifies
   this tensor with the specified tensorTower.
7. The strict reduction functor is the termwise cone of the natural power map. Its homotopy
   exactness descends through localization with its shift. The uniformizer cone resolution and
   internal K-flat scalar realization identify its evaluations with actual finite reductions
   followed by restriction of coefficients.
8. On the Roos fibre of the scalar source tower, multiplication by the uniformizer has index
   shift as homotopy inverse: their composite differs from the identity by the Roos difference,
   with the explicit off-diagonal contraction. Every quotient-power reduction of its derived
   limit is therefore zero, by the uniformizer cone resolution. Apply Rlim and finite reduction
   to the source-constant-cone triangle. Its second arrow is invertible. Preceding it by the
   invertible constant-limit unit is exactly kappa. Conservative derived scalar restriction
   reflects this invertibility in the actual finite-coefficient category. Evaluating red(kappa)
   and using joint conservativity gives the reduction-tower isomorphism as well.
9. Evaluate the strict cone tower and compare its transitions and inclusions with the principal
   power-cone tower. The quotient/principal comparison on K-flat representatives and normalized
   Roos comparison identify its augmentation with the specified kappa. Transport the existing
   quotient Roos completeness theorem and augmentation criterion along this comparison. This
   proves completeness of every output and the stated criterion for every input, with the
   normalized comparison for every K-flat representative. No cofinal tail is needed.
-/
theorem completeDerivedCompletion
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T T' : Scheme.{u}) (f : T' ⟶ T) :
    IsGrothendieckAbelian.{u+1} (CompleteDerivedCompletion.Tow l E T) ∧
    (∀ n : ℕ,
      PreservesFiniteLimits (CompleteDerivedCompletion.ev l E T n) ∧
      PreservesFiniteColimits (CompleteDerivedCompletion.ev l E T n) ∧
      PreservesFiniteLimits (CompleteDerivedCompletion.freeDiagram l E T n) ∧
      PreservesFiniteColimits (CompleteDerivedCompletion.freeDiagram l E T n) ∧
      (∀ I : CochainComplex (CompleteDerivedCompletion.Tow l E T) ℤ,
        I.IsKInjective → CochainComplex.IsKInjective
          (((CompleteDerivedCompletion.ev l E T n).mapHomologicalComplex (.up ℤ)).obj I))) ∧
    (∀ {M N : CompleteDerivedCompletion.DTow l E T} (a : M ⟶ N),
      IsIso a ↔ ∀ n : ℕ, IsIso ((CompleteDerivedCompletion.dev l E T n).map a)) ∧
    (PreservesFiniteLimits (CompleteDerivedCompletion.pull l E f) ∧
      PreservesFiniteColimits (CompleteDerivedCompletion.pull l E f) ∧
      (∀ n : ℕ, CompleteDerivedCompletion.pull l E f ⋙
          CompleteDerivedCompletion.ev l E T' n =
        CompleteDerivedCompletion.ev l E T n ⋙
          CondensedRing.upperStar (DerivedNakayama.integerRing l E) f) ∧
      ∃ β : ∀ n : ℕ,
          CompleteDerivedCompletion.rpush l E f ⋙ CompleteDerivedCompletion.dev l E T n ≅
            CompleteDerivedCompletion.dev l E T' n ⋙ CompleteDerivedCompletion.rpushModule l E f,
        (∀ n : ℕ, (β n).hom = CompleteDerivedCompletion.pushEvaluationMap l E f n) ∧
        (∀ (n : ℕ) (M : CompleteDerivedCompletion.DTow l E T),
          (CompleteDerivedCompletion.dev l E T n).map
              ((CompleteDerivedCompletion.towerAdjunction l E f).unit.app M) ≫
            (β n).hom.app ((CompleteDerivedCompletion.dpull l E f).obj M) =
          (CompleteDerivedCompletion.moduleAdjunction l E f).unit.app
              ((CompleteDerivedCompletion.dev l E T n).obj M) ≫
            (CompleteDerivedCompletion.rpushModule l E f).map
              ((CompleteDerivedCompletion.pullEvaluation l E f n).inv.app M)) ∧
        (∀ (n : ℕ) (N : CompleteDerivedCompletion.DTow l E T'),
          (CompleteDerivedCompletion.dev l E T' n).map
              ((CompleteDerivedCompletion.towerAdjunction l E f).counit.app N) =
          (CompleteDerivedCompletion.pullEvaluation l E f n).hom.app
              ((CompleteDerivedCompletion.rpush l E f).obj N) ≫
            (CompleteDerivedCompletion.dpullModule l E f).map ((β n).hom.app N) ≫
            (CompleteDerivedCompletion.moduleAdjunction l E f).counit.app
              ((CompleteDerivedCompletion.dev l E T' n).obj N)) ∧
        (∀ (n : ℕ) (M : CompleteDerivedCompletion.DTow l E T'),
          (CompleteDerivedCompletion.transition l E T n).app
              ((CompleteDerivedCompletion.rpush l E f).obj M) ≫ (β n).hom.app M =
            (β (n+1)).hom.app M ≫ (CompleteDerivedCompletion.rpushModule l E f).map
              ((CompleteDerivedCompletion.transition l E T' n).app M))) ∧
    Nonempty (CompleteDerivedCompletion.rlim l E T' ⋙
        CompleteDerivedCompletion.rpushModule l E f ≅
      CompleteDerivedCompletion.rpush l E f ⋙ CompleteDerivedCompletion.rlim l E T) ∧
    ((CompleteDerivedCompletion.rlim l E T).IsTriangulated ∧
      (∀ (e : AdicCompletion.Modules l E T ≌ AdicCompletion.Modules l E T')
          [e.functor.Additive],
        Nonempty (CompleteDerivedCompletion.rlim l E T ⋙ e.functor.mapDerivedCategory ≅
          ((Functor.whiskeringRight ℕᵒᵖ _ _).obj e.functor).mapDerivedCategory ⋙
            CompleteDerivedCompletion.rlim l E T')) ∧
      (∀ (P : CochainComplex (AdicCompletion.Modules l E T) ℤ)
          (hb : ∃ a b : ℤ, P.IsStrictlyGE a ∧ P.IsStrictlyLE b)
          (hf : ∀ j : ℤ, Mod.IsFree (AdicCompletion.ring l E T) (P.X j)),
        Nonempty (CompleteDerivedCompletion.rlim l E T ⋙
            (CondensedRing.derivedTensor (DerivedNakayama.integerRing l E) T).flip.obj
              (DerivedCategory.Q.obj P) ≅
          CompleteDerivedCompletion.tensorTower l E T P hb hf ⋙
            CompleteDerivedCompletion.rlim l E T))) ∧
    (∀ M : DerivedCategory (AdicCompletion.Modules l E T),
      IsDerivedComplete l E T ((CompleteDerivedCompletion.completion l E T).obj M) ∧
      IsIso ((CompleteDerivedCompletion.red l E T).map
        ((CompleteDerivedCompletion.kappa l E T).app M)) ∧
      ∀ n : ℕ, IsIso ((AdicCompletion.derivedReduction l E T n).map
        ((CompleteDerivedCompletion.kappa l E T).app M))) ∧
    (∀ M : DerivedCategory (AdicCompletion.Modules l E T),
      IsDerivedComplete l E T M ↔ IsIso ((CompleteDerivedCompletion.kappa l E T).app M)) ∧
    (∀ n : ℕ, Nonempty (CompleteDerivedCompletion.red l E T ⋙
        CompleteDerivedCompletion.dev l E T n ≅
      AdicCompletion.derivedReduction l E T n ⋙ AdicCompletion.restrict l E T n)) ∧
    (∃ (_shift : (CompleteDerivedCompletion.red l E T).CommShift ℤ),
      (CompleteDerivedCompletion.red l E T).IsTriangulated) ∧
    (∀ M : DerivedCategory (AdicCompletion.Modules l E T),
      IsIso ((CompleteDerivedCompletion.constantLimitAdjunction l E T).unit.app M)) ∧
    (∃ (_products : HasCountableProducts (DerivedCategory (AdicCompletion.Modules l E T))),
      ∀ M : CompleteDerivedCompletion.DTow l E T,
        IsDerivedLimit (K := fun n : ℕ ↦ (CompleteDerivedCompletion.dev l E T n).obj M)
          (fun n : ℕ ↦ (CompleteDerivedCompletion.transition l E T n).app M)
          ((CompleteDerivedCompletion.rlim l E T).obj M)) ∧
    Nonempty (DerivedCategory.Q ⋙ CompleteDerivedCompletion.rlim l E T ≅
      ExactProductsRoos.fibre ⋙ DerivedCategory.Q) ∧
    (∀ (M : DerivedCategory (AdicCompletion.Modules l E T))
        (P : CochainComplex (AdicCompletion.Modules l E T) ℤ)
        (_hP : (HomologicalComplex.quasiIso (AdicCompletion.Modules l E T) (.up ℤ)).kFlat P)
        (e : DerivedCategory.Q.obj P ≅ M),
      ∃ ε : DerivedCategory.Q.obj (AdicCompletion.roos l E T P) ≅
          (CompleteDerivedCompletion.completion l E T).obj M,
        AdicCompletion.completionMap l E T M P e ≫ ε.hom =
          (CompleteDerivedCompletion.kappa l E T).app M) := by
  have hfinite (M : DerivedCategory (AdicCompletion.Modules l E T)) (n : ℕ) :
      IsIso ((AdicCompletion.derivedReduction l E T n).map
        ((CompleteDerivedCompletion.kappa l E T).app M)) := by
    exact CompleteDerivedCompletion.finiteReduction_kappa l E T M n
  refine ⟨inferInstance, CompleteDerivedCompletion.evaluationProperties l E T,
    fun a ↦ CompleteDerivedCompletion.evaluation_isIso_iff l E T a, ?_,
    ⟨CompleteDerivedCompletion.pushLimitIso l E f⟩, ?_, ?_,
    CompleteDerivedCompletion.isDerivedComplete_iff l E T,
    CompleteDerivedCompletion.reductionEvaluation l E T,
    CompleteDerivedCompletion.red_triangulated l E T,
    CompleteDerivedCompletion.constantLimitUnit_isIso l E T,
    CompleteDerivedCompletion.derivedLimit l E T,
    CompleteDerivedCompletion.roosComparison l E T,
    CompleteDerivedCompletion.completionComparison l E T⟩
  · refine ⟨inferInstance, inferInstance, fun _ ↦ rfl,
      fun n ↦ asIso (CompleteDerivedCompletion.pushEvaluationMap l E f n),
      fun _ ↦ rfl, CompleteDerivedCompletion.pushEvaluation_unit l E f,
      CompleteDerivedCompletion.pushEvaluation_counit l E f,
      CompleteDerivedCompletion.pushEvaluation_transition l E f⟩
  · exact ⟨inferInstance, fun e _ ↦ ⟨CompleteDerivedCompletion.equivalenceLimitIso l E e⟩,
      CompleteDerivedCompletion.tensorLimitIso l E T⟩
  · intro M
    refine ⟨CompleteDerivedCompletion.completion_isDerivedComplete l E T M, ?_, hfinite M⟩
    apply (CompleteDerivedCompletion.evaluation_isIso_iff l E T _).2
    intro n
    obtain ⟨e⟩ := CompleteDerivedCompletion.reductionEvaluation l E T n
    apply (NatIso.isIso_map_iff e ((CompleteDerivedCompletion.kappa l E T).app M)).2
    have := hfinite M n
    exact inferInstanceAs (IsIso ((AdicCompletion.restrict l E T n).map
      ((AdicCompletion.derivedReduction l E T n).map
        ((CompleteDerivedCompletion.kappa l E T).app M))))

end AlgebraicGeometry.ProEtale
