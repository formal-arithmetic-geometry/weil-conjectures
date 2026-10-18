/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Sheaf.Paper.StrictTowerExchangeMateNormalization
public import Sheaf.Paper.CompletionMateComparison

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Algebra.Homology.KFlat
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.CategoryTheory.DiagramSiteRealization
import Sheaf.CategoryTheory.KInjectiveTotalDerived
import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison
import Sheaf.Paper.CompletedPullbackAdjunction
import Sheaf.Paper.ProEtaleProjectionFormulaArrows
import Sheaf.Paper.ProjectionFormulaTotalization
import Sheaf.Paper.ProjectionMateExact
import Sheaf.Paper.RingedExchangeTensorCoherence
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
/-! # Constant-coefficient strict reduction on the original pro-etale site

Source: Stacks Tags 099M, 099N and 0E48; smooth-purity blueprint, fix-lem-exchanges,
Step 4 (blueprint: lem-sp-completion-mate-comparison).

This is the original-site specialization of the existing strict quotient-tower construction.
The site retains object universe t+1 and morphism universe t.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.OrderedExchange

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- The quotient maps commute with canonical inverse image of the coefficients.
Source: Stacks 099M (blueprint: lem-sp-completion-mate-comparison).
Proof: combine exchangeScalar_comm with the projection compatibility for the profinite
coefficient inverse image. Both composites send a constant to its same finite residue. -/
theorem quotient_comm {U V : Scheme.{t}} (f : U ⟶ V) (n : ℕ) :
    (exchangeConstantIso.{t} f A).hom ≫
        (exchangeScalar.{t} d U ≫ AdicCoefficientDatum.projection.{t} d U n) =
      (proEtaleSheafInverseImage.{t, t + 2} f CommRingCat.{t + 1}).map
        (exchangeScalar.{t} d V ≫ AdicCoefficientDatum.projection.{t} d V n) ≫
          (AdicCoefficientDatum.finiteRingIso.{t} d f n).hom := by
  sorry

/-- The existing ambient constant-coefficient derived category.
Source: Stacks 099M (blueprint: lem-sp-completion-mate-comparison). -/
abbrev D (T : Scheme.{t}) := reductionDerivedCategory T (exchangeConstantRing T A)

/-- The existing derived category of strict constant-coefficient towers.
Source: Stacks 0941 (blueprint: lem-sp-completion-mate-comparison). -/
abbrev TD (T : Scheme.{t}) := DerivedCategory (exchangeTowers T (exchangeConstantRing T A))

/-- The quotient map from constant coefficients to the given finite coefficient sheaf.
Source: Stacks 099M (blueprint: lem-sp-completion-mate-comparison). -/
def quotient (T : Scheme.{t}) (n : ℕ) :
    exchangeConstantRing T A ⟶ d.finiteRing T n := exchangeScalar d T ≫ d.projection T n

/-- Ordinary tensor with the quotient, retaining the original constant scalar action.
Source: Stacks 099M (blueprint: lem-sp-completion-mate-comparison). -/
def level (T : Scheme.{t}) (n : ℕ) :
    reductionModules T (exchangeConstantRing T A) ⥤
      reductionModules T (exchangeConstantRing T A) :=
  reductionChange T (quotient d T n) ⋙ reductionRestrict T (quotient d T n)

/-- The strict quotient transition is determined on sheafified pure tensors.
Source: Stacks 099M, 06YY (blueprint: lem-sp-completion-mate-comparison).
Proof: the quotient coefficient maps commute with the constant scalar maps. Thus
s tensor x maps to q(s) tensor x by a balanced linear map. Sheafification extends
this map uniquely; its formula proves naturality on modules and site restrictions. -/
theorem step_existsUnique (T : Scheme.{t}) (n : ℕ) :
    ∃! τ : level d T (n + 1) ⟶ level d T n,
      ∀ (M : reductionModules T (exchangeConstantRing T A)) (U : T.ProEtᵒᵖ)
        (s : (d.finiteRing T (n + 1)).obj.obj U) (x : M.val.obj U),
        (τ.app M).val.app U (reductionTensorSection T (quotient d T (n + 1)) M U s x) =
          reductionTensorSection T (quotient d T n) M U
            ((reductionCoefficientMap T d (n + 1) n (Nat.le_succ n)).hom.app U s) x := by
  sorry

/-- The actual quotient transition, with its tensor formula retained.
Source: Stacks 099M (blueprint: lem-sp-completion-mate-comparison). -/
def step (T : Scheme.{t}) (n : ℕ) : level d T (n + 1) ⟶ level d T n :=
  (step_existsUnique d T n).exists.choose

/-- The single strict quotient diagram, functorial on ordinary modules.
Source: Stacks 099M (blueprint: lem-sp-completion-mate-comparison). -/
def reductionModule (T : Scheme.{t}) :
    reductionModules T (exchangeConstantRing T A) ⥤
      exchangeTowers T (exchangeConstantRing T A) := (Functor.ofOpSequence (step d T)).flip

/-- Tensor and restriction are additive at every level of this strict diagram.
Source: Stacks 06YY (blueprint: lem-sp-completion-mate-comparison).
Proof: evaluate at each index. Both scalar extension and scalar restriction preserve
addition. Joint faithfulness of ordinary diagram evaluations proves the assertion. -/
@[instance]
theorem reductionModule_additive (T : Scheme.{t}) : (reductionModule d T).Additive := by
  sorry

/-- The homotopy functor of the actual strict quotient construction.
Source: Stacks 06YY (blueprint: lem-sp-completion-mate-comparison). -/
def reductionHomotopy (T : Scheme.{t}) :=
  (reductionModule d T).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh

/-- The reduction functor is specified by its universal derived counit and K-flat models.
Source: Stacks 099M, 06YY (blueprint: lem-sp-completion-mate-comparison).
Proof: flat-term K-flat resolutions exist on the small site. The tower construction
preserves shifts and cones. It sends quasi-isomorphisms between resolving models to
levelwise quasi-isomorphisms, hence to strict tower quasi-isomorphisms. Apply the
left-derived resolving-class theorem. Its universal property determines the pair
up to the unique counit-compatible isomorphism and makes the counit invertible on
K-flat models. This is precisely the same construction as Site.reduction. -/
theorem reduction_exists (T : Scheme.{t}) :
    ∃ (R : D (A := A) T ⥤ TD (A := A) T)
      (ε : DerivedCategory.Qh ⋙ R ⟶ reductionHomotopy d T),
      R.IsLeftDerivedFunctor ε
        (HomotopyCategory.quasiIso (reductionModules T (exchangeConstantRing T A)) (.up ℤ)) ∧
      ∀ P : CochainComplex (reductionModules T (exchangeConstantRing T A)) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, t + 1}
          (R := exchangeConstantRing T A) P →
        IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) := by
  sorry

/-- The canonical total left derived strict reduction, chosen with its universal counit.
Source: Stacks 099M (blueprint: lem-sp-completion-mate-comparison). -/
def reduction (T : Scheme.{t}) : D (A := A) T ⥤ TD (A := A) T := (reduction_exists d T).choose

/-- The universal counit retained in the construction of reduction.
Source: Stacks 06YY (blueprint: lem-sp-completion-mate-comparison). -/
def reductionCounit (T : Scheme.{t}) :
    DerivedCategory.Qh ⋙ reduction d T ⟶ reductionHomotopy d T :=
  (reduction_exists d T).choose_spec.choose

/-- The reduction counit at an actual cochain complex.
Source: Stacks 06YY (blueprint: lem-sp-completion-mate-comparison). -/
def reductionComplexCounit (T : Scheme.{t})
    (P : CochainComplex (reductionModules T (exchangeConstantRing T A)) ℤ) :
    (reduction d T).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj (((reductionModule d T).mapHomologicalComplex (.up ℤ)).obj P) :=
  AlgebraicGeometry.Scheme.reductionComplexCounit (reductionModule d T)
    (reduction d T) (reductionCounit d T) P

/-- The existing total right derived inverse limit on strict constant towers.
Source: Stacks 0941 (blueprint: lem-sp-completion-mate-comparison). -/
abbrev rlim (T : Scheme.{t}) := completedRlim T (exchangeConstantRing T A)

/-- Constant-coefficient quotient-tower completion.
Source: Stacks 099M (blueprint: lem-sp-completion-mate-comparison). -/
def completion (T : Scheme.{t}) : D (A := A) T ⥤ D (A := A) T := reduction d T ⋙ rlim (A := A) T

/-- The exact constant-diagram functor on the ambient derived category.
Source: Stacks 0941 (blueprint: lem-sp-completion-mate-comparison). -/
abbrev diagonal (T : Scheme.{t}) :=
  (Functor.const ℕᵒᵖ : reductionModules T (exchangeConstantRing T A) ⥤
    exchangeTowers T (exchangeConstantRing T A)).mapDerivedCategory

/-- The constant diagram/derived limit adjunction, with its ordinary unit.
Source: Stacks 0941 (blueprint: lem-sp-completion-mate-comparison). -/
def diagonalAdjunction (T : Scheme.{t}) : diagonal (A := A) T ⊣ rlim (A := A) T :=
  (constLimAdj : (Functor.const ℕᵒᵖ) ⊣
    completedTowerLimit T (exchangeConstantRing T A)).mapDerivedCategoryRightDerivedAdjunction

/-- The ordinary quotient augmentation is fixed on every section by x maps to 1 tensor x.
Source: Stacks 099M (blueprint: lem-sp-completion-mate-comparison).
Proof: the tensor-unit insertions commute with the quotient transitions, which preserve
1. They are linear in the original constant coefficients and natural in modules.
Their section formulas determine all components and hence the augmentation uniquely. -/
theorem ordinaryAugmentation_existsUnique (T : Scheme.{t}) :
    ∃! η : (Functor.const ℕᵒᵖ : reductionModules T (exchangeConstantRing T A) ⥤
        exchangeTowers T (exchangeConstantRing T A)) ⟶ reductionModule d T,
      ∀ (M : reductionModules T (exchangeConstantRing T A)) (n : ℕ) (U : T.ProEtᵒᵖ)
        (x : M.val.obj U),
        ((η.app M).app (op n)).val.app U x =
          reductionTensorSection T (quotient d T n) M U 1 x := by
  sorry

/-- The ordinary augmentation with its sectionwise normalization.
Source: Stacks 099M (blueprint: lem-sp-completion-mate-comparison). -/
def ordinaryAugmentation (T : Scheme.{t}) :
    (Functor.const ℕᵒᵖ : reductionModules T (exchangeConstantRing T A) ⥤
      exchangeTowers T (exchangeConstantRing T A)) ⟶ reductionModule d T :=
  (ordinaryAugmentation_existsUnique d T).exists.choose

/-- The derived quotient augmentation is uniquely fixed by the ordinary quotient unit.
Source: Stacks 099M (blueprint: lem-sp-completion-mate-comparison).
Proof: on a K-flat model invert the reduction counit and apply the ordinary quotient
augmentation. Naturality for chain maps and invariance under resolving quasi-isomorphisms
descend the map. Every object has a resolving representative, which proves uniqueness. -/
theorem augmentation_existsUnique (T : Scheme.{t}) :
    ∃! η : diagonal (A := A) T ⟶ reduction d T,
      ∀ P : CochainComplex (reductionModules T (exchangeConstantRing T A)) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, t + 1}
          (R := exchangeConstantRing T A) P →
        η.app (DerivedCategory.Q.obj P) ≫ reductionComplexCounit d T P =
          (Functor.const ℕᵒᵖ).mapDerivedCategoryFactors.hom.app P ≫
            DerivedCategory.Q.map
              ((NatTrans.mapHomologicalComplex (ordinaryAugmentation d T) (.up ℤ)).app P) := by
  sorry

/-- The specified derived quotient augmentation.
Source: Stacks 099M (blueprint: lem-sp-completion-mate-comparison). -/
def augmentation (T : Scheme.{t}) : diagonal (A := A) T ⟶ reduction d T :=
  (augmentation_existsUnique d T).exists.choose

/-- The canonical quotient completion unit, from the diagonal/limit adjunction.
Source: Stacks 099M (blueprint: lem-sp-completion-mate-comparison). -/
def unit (T : Scheme.{t}) : 𝟭 (D (A := A) T) ⟶ completion d T :=
  (diagonalAdjunction (A := A) T).unit ≫
    Functor.whiskerRight (augmentation d T) (rlim (A := A) T)

/-- Completeness means invertibility of this specific quotient completion unit.
Source: Stacks 099M (blueprint: lem-sp-completion-mate-comparison). -/
def IsComplete (T : Scheme.{t}) (K : D (A := A) T) : Prop := IsIso ((unit d T).app K)

/-- The full derived-complete category, with all ambient morphisms.
Source: Stacks 099M (blueprint: lem-sp-completion-mate-comparison). -/
abbrev Complete (T : Scheme.{t}) := ObjectProperty.FullSubcategory (IsComplete d T)

/-- Ordinary constant-coefficient derived pullback, in the recorded ringed presentation.
Source: Stacks 099N (blueprint: lem-sp-completion-mate-comparison). -/
abbrev pull {U V : Scheme.{t}} (f : U ⟶ V) :=
  proEtaleRingDerivedPullback f (exchangeConstantRing V A) (exchangeConstantRing U A)
    (exchangeConstantIso f A)

/-- Ordinary constant-coefficient derived direct image, with its canonical derived unit.
Source: Stacks 099N (blueprint: lem-sp-completion-mate-comparison). -/
abbrev push {U V : Scheme.{t}} (f : U ⟶ V) :=
  proEtaleRingDerivedDirectImage f (exchangeConstantRing V A) (exchangeConstantRing U A)
    (exchangeConstantIso f A)

/-- Completed pullback on ambient objects is ordinary pullback followed by completion.
Source: Stacks 099N (blueprint: lem-sp-completion-mate-comparison). -/
def completePull {U V : Scheme.{t}} (f : U ⟶ V) := pull (A := A) f ⋙ completion d U

variable {U V : Scheme.{t}} (f : U ⟶ V)

/-- The ordinary scalar/pullback mate, in the inverse direction of chi.
Source: blueprint four corners and tower compatibility; Stacks 06YY and 0D6D
(blueprint: lem-sp-completion-mate-comparison). -/
def ordinaryReductionPullInv (n : ℕ) :
    proEtaleRingModulePullback f (exchangeConstantRing V A) (exchangeConstantRing U A)
        (exchangeConstantIso f A) ⋙ proEtaleRingExtension (quotient d U n) ⟶
      proEtaleRingExtension (quotient d V n) ⋙
        proEtaleRingModulePullback f (d.finiteRing V n) (d.finiteRing U n)
          (d.finiteRingIso f n) :=
  (mateEquiv (proEtaleRingExtensionAdjunction (quotient d V n))
    (proEtaleRingExtensionAdjunction (quotient d U n))).symm
      (proEtaleRingRestrictionPullbackInv f (exchangeConstantRing V A) (d.finiteRing V n)
        (exchangeConstantRing U A) (d.finiteRing U n) (quotient d V n) (quotient d U n)
          (exchangeConstantIso f A) (d.finiteRingIso f n) (quotient_comm d f n))

/-- The normalized ordinary mate is the invertible tensor balancing map.
Source: blueprint tower compatibility; Stacks 03EL and 06YY
(blueprint: lem-sp-completion-mate-comparison).
Proof: the tensor-unit normalized adjunctions compute this mate on pure tensors.
It sends the inverse image of m tensored with p to the inverse image of m tensor p.
The coefficient projection square makes the map quotient-linear. The reverse tensor
reassociation is inverse, as checked on pure tensors and then on sheafifications. -/
theorem ordinaryReductionPullInv_isIso (n : ℕ) :
    IsIso (ordinaryReductionPullInv d f n) := by
  sorry

attribute [instance] ordinaryReductionPullInv_isIso

/-- The ordinary reduction-level comparison after restriction to completed coefficients.
Source: blueprint tower compatibility (blueprint: lem-sp-completion-mate-comparison). -/
def levelPullIso (n : ℕ) :
    level d V n ⋙
        proEtaleRingModulePullback f (exchangeConstantRing V A) (exchangeConstantRing U A)
          (exchangeConstantIso f A) ≅
      proEtaleRingModulePullback f (exchangeConstantRing V A) (exchangeConstantRing U A)
        (exchangeConstantIso f A) ⋙ level d U n :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (proEtaleRingExtension (quotient d V n))
      (@asIso _ _ _ _ (proEtaleRingRestrictionPullbackInv f
        (exchangeConstantRing V A) (d.finiteRing V n) (exchangeConstantRing U A) (d.finiteRing U n)
        (quotient d V n) (quotient d U n) (exchangeConstantIso f A)
        (d.finiteRingIso f n) (quotient_comm d f n))
        (proEtaleRingRestrictionPullbackInv_isIso f
          (exchangeConstantRing V A) (d.finiteRing V n)
          (exchangeConstantRing U A) (d.finiteRing U n)
          (quotient d V n) (quotient d U n) (exchangeConstantIso f A)
          (d.finiteRingIso f n) (quotient_comm d f n))) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (asIso (ordinaryReductionPullInv d f n)).symm
      (proEtaleRingRestrictScalars (quotient d U n)) ≪≫
    Functor.associator _ _ _

/-- The level tensor comparisons commute with every quotient transition, including identities.
Source: blueprint tower compatibility, step 1 (blueprint: lem-sp-completion-mate-comparison).
Proof: both composites send a local pure tensor to its pullback with the quotient image
of its coefficient. Equality on pure tensors descends through sheafification. Arbitrary
quotient transitions are composites of consecutive ones, with identities included. -/
theorem levelPullIso_transition
    (M : reductionModules V (exchangeConstantRing V A)) {n m : ℕᵒᵖ} (a : n ⟶ m) :
    ((reductionModule d V ⋙ exchangeTowerModulePull f (exchangeConstantRing V A)
          (exchangeConstantRing U A) (exchangeConstantIso f A)).obj M).map a ≫
        (levelPullIso d f m.unop).hom.app M =
      (levelPullIso d f n.unop).hom.app M ≫
        ((proEtaleRingModulePullback f (exchangeConstantRing V A) (exchangeConstantRing U A)
          (exchangeConstantIso f A) ⋙ reductionModule d U).obj M).map a := by
  sorry

/-- The actual strict tower isomorphism of ordinary tensor/pullback computations.
Source: blueprint tower compatibility (blueprint: lem-sp-completion-mate-comparison). -/
def ordinaryReductionPullIso :
    reductionModule d V ⋙ exchangeTowerModulePull f (exchangeConstantRing V A)
          (exchangeConstantRing U A) (exchangeConstantIso f A) ≅
      proEtaleRingModulePullback f (exchangeConstantRing V A) (exchangeConstantRing U A)
        (exchangeConstantIso f A) ⋙ reductionModule d U :=
  NatIso.ofComponents
    (fun M ↦ NatIso.ofComponents
      (fun n ↦ (levelPullIso d f n.unop).app M)
      (fun a ↦ levelPullIso_transition d f M a))
    (fun a ↦ by
      apply NatTrans.ext
      funext n
      exact (levelPullIso d f n.unop).hom.naturality a)

set_option linter.defProp false in
/-- The strict ordinary comparison and universal counits fix the derived comparison.
Source: blueprint tower compatibility, steps 1--3; Stacks 06YY and 0D6D
(blueprint: lem-sp-completion-mate-comparison). -/
def ReductionPullNormalized
    (τ : reduction d V ⋙ exchangeConstantPull (A := A) f ≅
        pull (A := A) f ⋙ reduction d U) : Prop :=
  ∀ P : CochainComplex (reductionModules V (exchangeConstantRing V A)) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients (R := exchangeConstantRing V A) P →
        τ.hom.app (DerivedCategory.Q.obj P) ≫
            (reduction d U).map
              ((proEtaleRingDerivedPullbackFactors f
                (exchangeConstantRing V A) (exchangeConstantRing U A)
                (exchangeConstantIso f A)).hom.app P) ≫
            reductionComplexCounit d U
              (((proEtaleRingModulePullback f (exchangeConstantRing V A) (exchangeConstantRing U A)
                (exchangeConstantIso f A)).mapHomologicalComplex (.up ℤ)).obj P) =
          (exchangeConstantPull (A := A) f).map (reductionComplexCounit d V P) ≫
            (exchangeTowerModulePull f (exchangeConstantRing V A)
          (exchangeConstantRing U A) (exchangeConstantIso f A)).mapDerivedCategoryFactors.hom.app
              (((reductionModule d V).mapHomologicalComplex (.up ℤ)).obj P) ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex (ordinaryReductionPullIso d f)
                (.up ℤ)).hom.app P)

/-- The canonical derived comparison is uniquely fixed on K-flat representatives by the
strict ordinary comparison and the two universal derived counits.
Source: blueprint tower compatibility, steps 1--3; Stacks 06YY and 0D6D
(blueprint: lem-sp-completion-mate-comparison).
Proof: choose a K-flat flat-term representative P. Its pullback remains K-flat with flat
terms. The two reduction-tower counits are invertible there, so the displayed equation
uniquely defines the component by the ordinary strict tower isomorphism above. Naturality
for chain maps, compatible homotopies, and inverse quasi-isomorphisms descends this to
all derived objects. Every object has a K-flat representative; hence the natural
isomorphism is unique. Its evaluation is chi, since both have the same ordinary tensor
normalization, and the transition compatibility is retained from the strict comparison. -/
theorem reductionPullIso_existsUnique :
    ∃! τ : reduction d V ⋙ exchangeConstantPull (A := A) f ≅
        pull (A := A) f ⋙ reduction d U,
      ReductionPullNormalized d f τ := by
  sorry

/-- The normalized reduction-tower/pullback isomorphism, rather than an arbitrary lift
of levelwise maps. Source: blueprint tower compatibility
(blueprint: lem-sp-completion-mate-comparison). -/
def reductionPullIso :
    reduction d V ⋙ exchangeConstantPull (A := A) f ≅
      pull (A := A) f ⋙ reduction d U :=
  (reductionPullIso_existsUnique d f).choose



/-- The strict projection is the adjunct of reduction of the ambient counit.
Source: Stacks 0B56, 099M (blueprint: lem-sp-completion-mate-comparison). -/
def projection (K : D (A := A) U) :
    (reduction d V).obj ((push (A := A) f).obj K) ⟶
      (exchangeConstantPush (A := A) f).obj ((reduction d U).obj K) :=
  (exchangeTowerAdjunction f (exchangeConstantRing V A) (exchangeConstantRing U A)
    (exchangeConstantIso f A)).homEquiv _ _
      ((reductionPullIso d f).hom.app ((push (A := A) f).obj K) ≫
        (reduction d U).map ((proEtaleRingDerivedAdjunction f (exchangeConstantRing V A)
          (exchangeConstantRing U A) (exchangeConstantIso f A)).counit.app K))

/-- Perfect quotients make the strict projection invertible, on all ambient inputs.
Source: Stacks 0944, 099M (blueprint: lem-sp-completion-mate-comparison).
Proof: evaluate its counit-tensor adjunct at every finite quotient. The canonical
finite pullback/tensor balancing identifies it with the perfect projection formula.
Every evaluated cone is acyclic. Levelwise cohomology makes the strict cone acyclic,
so the strict projection is invertible. No faithfulness of derived evaluations is used. -/
@[instance]
theorem projection_isIso (K : D (A := A) U) : IsIso (projection d f K) := by
  sorry

/-- The identity comparison of ordinary constant diagrams and termwise pullback.
Source: Stacks 0941 (blueprint: lem-sp-completion-mate-comparison). -/
def ordinaryDiagonalPullIso :
    (Functor.const ℕᵒᵖ) ⋙ exchangeTowerModulePull f
        (exchangeConstantRing V A) (exchangeConstantRing U A) (exchangeConstantIso f A) ≅
      proEtaleRingModulePullback f (exchangeConstantRing V A) (exchangeConstantRing U A)
        (exchangeConstantIso f A) ⋙ (Functor.const ℕᵒᵖ) :=
  NatIso.ofComponents
    (fun M ↦ NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by simp))
    (fun _ ↦ by ext n; simp)

/-- Exact descent of the identity comparison, retaining the derived units and counits.
Source: Stacks 0941 (blueprint: lem-sp-completion-mate-comparison). -/
def diagonalPullIso :
    diagonal (A := A) V ⋙ exchangeConstantPull (A := A) f ≅
      pull (A := A) f ⋙ diagonal (A := A) U :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (ordinaryDiagonalPullIso (A := A) f) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

/-- The direct-image/limit comparison is the adjunction conjugate of the identity square.
It is the same K-injective comparison used by comparisonT in the generic interface.
Source: Stacks 0A07 (blueprint: lem-sp-completion-mate-comparison). -/
def directLimitIso :
    rlim (A := A) U ⋙ push (A := A) f ≅
      exchangeConstantPush (A := A) f ⋙ rlim (A := A) V :=
  conjugateIsoEquiv
    ((proEtaleRingDerivedAdjunction f (exchangeConstantRing V A) (exchangeConstantRing U A)
      (exchangeConstantIso f A)).comp (diagonalAdjunction (A := A) U))
    ((diagonalAdjunction (A := A) V).comp
      (exchangeTowerAdjunction f (exchangeConstantRing V A) (exchangeConstantRing U A)
        (exchangeConstantIso f A))) (diagonalPullIso (A := A) f)

/-- The prescribed reconstruction of constant-coefficient completed pullback.
Source: Stacks 099M, 099N (blueprint: lem-sp-completion-mate-comparison). -/
def reconstruction (K : D (A := A) V) :
    (completePull d f).obj K ≅
      (rlim (A := A) U).obj ((exchangeConstantPull (A := A) f).obj ((reduction d V).obj K)) :=
  (rlim (A := A) U).mapIso ((reductionPullIso d f).symm.app K)

variable {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The constant-coefficient H is pullback of the counit-tensor projection.
Source: Stacks 0B56, 099M (blueprint: lem-sp-completion-mate-comparison). -/
def H (K : D (A := A) X) :
    (reduction d Y').obj ((pull (A := A) g).obj ((push (A := A) f).obj K)) ≅
      (exchangeConstantPull (A := A) g).obj
        ((exchangeConstantPush (A := A) f).obj ((reduction d X).obj K)) :=
  (reductionPullIso d g).symm.app _ ≪≫
    (exchangeConstantPull (A := A) g).mapIso (asIso (projection d f K))

/-- Exactly the prescribed s: derived strict inverse limit of H after reconstruction.
Source: Stacks 099M, 0E48 (blueprint: lem-sp-completion-mate-comparison). -/
def S (K : D (A := A) X) :=
  (rlim (A := A) Y').mapIso (H (f := f) (g := g) d K)

/-- Exactly the prescribed t: reconstruction followed by direct-image/limit comparison.
Source: Stacks 0A07, 099N (blueprint: lem-sp-completion-mate-comparison). -/
def T (K : D (A := A) X) :=
  (push (A := A) f').mapIso (reconstruction d g' K) ≪≫
    (directLimitIso (A := A) f').app
      ((exchangeConstantPull (A := A) g').obj ((reduction d X).obj K))

end AlgebraicGeometry.Scheme.OrderedExchange

namespace CategoryTheory.AdicSites.OrderedExchangeInterface

/-- Reexport the existing whole-diagram mate comparison, including invertibility and
the two finite coefficient normalization clauses. No second postponed proof is introduced.

Source: smooth-purity blueprint, fix-lem-exchanges Proof Step 4; ingredient sources
Stacks 099M, 099N, 0E48, 0941, 0B56, 0944
(blueprint: lem-sp-completion-mate-comparison).

Proof, following the ten steps of the DAG node:
1. Realize the strict sequence category on the diagram site. Use one flat-term
K-flat model for K and tensor it with the whole strict quotient diagram; its diagonal
is K-flat by levelwise acyclicity. This identifies the reduction/pullback comparisons.
2. The constant-tower functor preserves K-injectives, since evaluation at its terminal
index is exact and left adjoint to it. Its derived units and counits are the ordinary
ones termwise. The derived quotient augmentation therefore gives exactly the fixed
completion unit.
3. Evaluation of the strict projection adjunct gives finiteProjection. Each quotient
is perfect, hence has a bounded finite-projective model. Constant sheafification and
inverse image preserve its finite-free retracts. The finite total projection formula
makes every evaluated projection invertible; levelwise cohomology detects its cone.
Thus H is invertible and has the stated finite evaluation.
4. The identity-component constant/pullback square gives directLimitIso by adjunction
conjugation. On a K-injective strict tower it is the ordinary direct-image/limit map;
its projections are the direct images of the tower projections. This is t.
5. Apply ringedExchangeTensorCoherence on the diagram sites with the diagonal of K
and the whole quotient diagram. The diagram exchange on the diagonal is the diagonal
of the ordinary mate. The resulting equality holds before any evaluation or limit.
6. Naturality of the projection adjunct in the coefficient, and its tensor-unit
normalization, identify its composition with the quotient augmentation with direct
image of that augmentation. Apply total derived limit to obtain the corresponding
completion-unit equation.
7. The strict expression t inverse followed by limit(v) followed by s extends the
ordinary mate followed by the completed target unit. Completeness of that target
and direct-image preservation give uniqueness of this extension.
8. For each pair of edges, transpose under the ordinary and completion adjunctions.
The comparison C(v^* unit) is invertible by reflection and preservation of complete
objects under direct image. This calculation identifies the completed pullback square
with the conjugate of the prescribed right-adjoint square, including units and counits.
9. Transpose the completed mate and precompose with the completion unit. The triangle
identities give the same extension as in step 7. Uniqueness proves the displayed
natural-transformation equality, not merely equality of evaluated tower maps.
10. Evaluate the strict derived adjunction on a K-injective tower and use its exact
left adjoint. Finite scalar restriction commutes with direct image by adjunction
conjugation and with inverse image on generalized sections. These comparisons turn
the evaluated tower mate into ordinaryExchange over the original quotient ring.
No properness, smoothness, constructibility, boundedness or etale-origin condition
is used. Empty sites, the zero ideal and the unit ideal are included. -/
abbrev completionMateComparison
    {Y X Y' X' : Site.{u}}
    {f : Morphism Y X} {g : Morphism Y Y'} {h : Morphism X X'} {k : Morphism Y' X'}
    (sq : Square f g h k) (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (_hperfect : PerfectQuotients A I) :
    (∀ K : X.Complete A I,
      IsIso (projectionComparison (f := f) (g := g) A I K.obj)) ∧
    (∀ (K : X.Complete A I) (n : ℕ),
      (Y'.evaluate A n).map (projectionComparison (f := f) (g := g) A I K.obj) ≫
          (finiteSourceIso (f := f) (g := g) A I n K.obj).hom =
        (Y'.finiteEvaluationIso A I n).hom.app ((g.pull A).obj ((f.push A).obj K.obj)) ≫
          (Y'.finiteRestriction A I n).map
            (finiteProjectionComparison (f := f) (g := g) A I n K.obj)) ∧
    (Functor.whiskerRight (completeExchange sq A I) (ObjectProperty.ι (Y'.IsComplete A I)) ≫
        (comparisonT (h := h) (k := k) A I).hom =
      comparisonS (f := f) (g := g) A I ≫
        Functor.whiskerRight
          (Functor.whiskerLeft (ObjectProperty.ι (X.IsComplete A I) ⋙ X.reduction A I)
            (towerExchange sq A)) (Y'.rlim A)) ∧
    (∀ (K : X.Complete A I) (n : ℕ),
      (Y'.evaluate A n).map ((towerExchange sq A).app ((X.reduction A I).obj K.obj)) ≫
          (finiteTargetIso (h := h) (k := k) A I n K.obj).hom =
        (finiteSourceIso (f := f) (g := g) A I n K.obj).hom ≫
          (Y'.finiteRestriction A I n).map
            ((ordinaryExchange sq (quotientRing A I n)).app
              ((X.finiteReduction A I n).obj K.obj))) :=
  CategoryTheory.AdicSites.completionMateComparison sq A I _hperfect


end CategoryTheory.AdicSites.OrderedExchangeInterface
