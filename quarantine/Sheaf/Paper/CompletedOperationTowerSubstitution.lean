/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q45
-/
module

public import Sheaf.Paper.CompletedOperationExpressions
public import Sheaf.Paper.IntegralComparisonRealizationModels
public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import Sheaf.Paper.SemilinearDerivedSections
public import Mathlib.CategoryTheory.Pi.Basic
import Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence
import Sheaf.AlgebraicGeometry.ProEtaleModulePullbackComposition
import Sheaf.CategoryTheory.StrictRoosComparison
import Sheaf.Paper.NormalizedDVREffectivity
import Sheaf.Paper.IntegralReductionTowerCanonical
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatTotalTensorModel
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
import Sheaf.Paper.IntegralOperationsWellDefined
import Sheaf.Paper.NormalizedDVRTower

/-! # Substitution into completed tensor and pullback

Source: Bhatt--Scholze, Definition 3.4.10 and Lemma 6.5.9(4); blueprint
main-20261015, order 2232, coefficient twists; explicit coherent-counit refinement
in proof steps 1--12 of the node below
(blueprint: lem-pur-completed-operation-tower-substitution).

All comparisons live in the ordinary derived category of the ringed sequence
site before restriction or total derived limit. The natural-number index n
means positive quotient exponent n+1. Site and coefficient universes are independent.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe t u s i j
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
namespace WeilConjectures.CompletedOperations

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Compatible presentations of the *specified* operations. The tensor structures
are normalized on K-flat total complexes by RingedSiteDualityModel; the reduction
calculus fixes every quotient map and both adjunction projections. Completion's
comparison is pinned by the actual quotient/Roos augmentation. Pullback's
comparison is pinned on every simultaneous quotient presentation, not chosen
separately on evaluated objects.
Source: node proof steps 1, 4--5; Stacks 06YY, 07A4, 0941
(blueprint: lem-pur-completed-operation-tower-substitution). -/
structure Models {S : Type s} (W : S → Scheme.{t}) where
  /-- The recorded reduction/total-limit adjunction. -/
  calculus : ∀ a : S, CoefficientDerivedSystemCalculus l E (W a)
  /-- Canonical total tensor, action unit and signed interchange on whole systems. -/
  system : ∀ a : S, RingedSiteDualityModel.{t + 1, t, u, (max u (t + 1)) + 1}
    (coefficientSequenceTopology (Scheme.ProEt.topology (W a)))
    (coefficientSequenceCommRingSheaf l E (W a))
  /-- These are presentations of the same system closed tensor. -/
  system_closed : ∀ a : S, (system a).closed = (calculus a).systemClosed
  /-- The integral tensor is the recorded ordinary tensor used by completion. -/
  integral_closed : ∀ a : S,
    (calculus a).integralClosed = (IntegralOnSlice.duality l E (W a) none).closed
  /-- Completion as the reduction/total-limit composite. -/
  completion : ∀ a : S, IntegralOnSlice.completion l E (W a) none ≅
    (calculus a).reduction ⋙ coefficientSequenceLimit l E (W a)
  /-- Unit normalization determines this comparison, including its maps. -/
  completion_unit : ∀ (a : S) (K : DerivedCategory (scalarReductionSource l E (W a))),
    (IntegralOnSlice.completionUnit l E (W a) none).app K ≫
        (completion a).hom.app K = (calculus a).adjunction.unit.app K
  /-- The actual total-limit/Roos comparison with its K-injective normalization. -/
  roos : ∀ a : S, IntegralComparisonRoosModel l E (W a)
  /-- Pullback is normalized on all K-flat quotient presentations. -/
  pullback : ∀ {a b : S} (f : W a ⟶ W b),
    IntegralComparisonPullbackModel l E f (calculus b) (roos a)

variable {S : Type s} {W : S → Scheme.{t}} (M : Models l E W)

/-- The system tensor in the fixed canonical total-complex presentation.
Source: node proof steps 1--2 (blueprint: lem-pur-completed-operation-tower-substitution). -/
def tensor (a : S) := (M.system a).closed.tensor

/-- The coefficient unit system B_n[0], including its actual quotient transitions.
Source: node proof steps 3 and 7 (blueprint: lem-pur-completed-operation-tower-substitution). -/
def unit (a : S) : coefficientSequenceDerived l E (W a) :=
  ringedSiteDualityUnit.{t + 1, t, u}
    (coefficientSequenceTopology (Scheme.ProEt.topology (W a)))
    (coefficientSequenceCommRingSheaf l E (W a))

/-- The defining quotient-limit tensor realization. Each factor is fixed by the
reduction tensor model, closed-tensor presentation, or completion augmentation.
Source: node proof step 5 (blueprint: lem-pur-completed-operation-tower-substitution). -/
def tensorRealization (a : S) : IntegralOnSlice.completedTensor l E (W a) none ≅
    ((M.calculus a).reduction.prod (M.calculus a).reduction) ⋙
      tensor l E M a ⋙ coefficientSequenceLimit l E (W a) :=
  isoWhiskerLeft (IntegralOnSlice.duality l E (W a) none).closed.tensor (M.completion a) ≪≫
    isoWhiskerRight
      (isoWhiskerRight
        (eqToIso (congrArg CoefficientClosedStructure.tensor (M.integral_closed a).symm))
          (M.calculus a).reduction ≪≫
        (M.calculus a).reductionTensor ≪≫
        isoWhiskerLeft ((M.calculus a).reduction.prod (M.calculus a).reduction)
          (eqToIso (congrArg CoefficientClosedStructure.tensor (M.system_closed a).symm)))
      (coefficientSequenceLimit l E (W a))

/-- The primitive tensor comparison is L(T(e_A,e_N)), after its defining realization.
This is a formula using the coherent counit, before any invertibility assertion.
Source: node proof step 6 (blueprint: lem-pur-completed-operation-tower-substitution). -/
def tensorComparison (a : S) (A N : coefficientSequenceDerived l E (W a)) :
    (IntegralOnSlice.completedTensor l E (W a) none).obj
        ((coefficientSequenceLimit l E (W a)).obj A,
         (coefficientSequenceLimit l E (W a)).obj N) ⟶
      (coefficientSequenceLimit l E (W a)).obj ((tensor l E M a).obj (A, N)) :=
  (tensorRealization l E M a).hom.app _ ≫
    (coefficientSequenceLimit l E (W a)).map
      ((tensor l E M a).map (Prod.mkHom
        ((M.calculus a).adjunction.counit.app A) ((M.calculus a).adjunction.counit.app N)))

/-- The primitive pullback comparison is L(F(e_C)), after quotient-model realization.
Source: node proof step 6 (blueprint: lem-pur-completed-operation-tower-substitution). -/
def pullbackComparison {a b : S} (f : W a ⟶ W b)
    (C : coefficientSequenceDerived l E (W b)) :
    (integralDerivedPullback l E f).obj ((coefficientSequenceLimit l E (W b)).obj C) ⟶
      (coefficientSequenceLimit l E (W a)).obj
        ((integralComparisonDerivedSequencePullback l E f).obj C) :=
  (M.pullback f).realization.hom.app _ ≫
    (coefficientSequenceLimit l E (W a)).map
      ((integralComparisonDerivedSequencePullback l E f).map
        ((M.calculus b).adjunction.counit.app C))

variable {I : Type i} {location : I → S}

/-- Evaluate an expression on *whole* coefficient systems, functorially in all inputs.
Source: node proof step 7 (blueprint: lem-pur-completed-operation-tower-substitution). -/
def systemValue {a : S} : Expression W location a →
    ((∀ k : I, coefficientSequenceDerived l E (W (location k))) ⥤
      coefficientSequenceDerived l E (W a))
  | .input k => Pi.eval _ k
  | .unit a => (Functor.const _).obj (unit l E (W := W) a)
  | .tensor P Q => (systemValue P).prod' (systemValue Q) ⋙ tensor l E M a
  | .pullback f P => systemValue P ⋙ integralComparisonDerivedSequencePullback l E f

/-- Evaluate with the same parentheses using the recorded completed operations.
Source: node proof step 7 (blueprint: lem-pur-completed-operation-tower-substitution). -/
def completedValue {a : S} : Expression W location a →
    ((∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k)))) ⥤
      DerivedCategory (scalarReductionSource l E (W a)))
  | .input k => Pi.eval _ k
  | .unit a => (Functor.const _).obj
      ((coefficientSequenceLimit l E (W a)).obj (unit l E (W := W) a))
  | .tensor P Q => (completedValue P).prod' (completedValue Q) ⋙
      IntegralOnSlice.completedTensor l E (W a) none
  | .pullback f P => completedValue P ⋙ integralDerivedPullback l E f

/-- The recursive comparison: identities at leaves, then the primitive counit formulas.
It is defined as a morphism, without choosing objectwise isomorphisms.
Source: node proof step 7 (blueprint: lem-pur-completed-operation-tower-substitution). -/
def comparison {a : S} (P : Expression W location a)
    (N : ∀ k : I, coefficientSequenceDerived l E (W (location k))) :
    (completedValue l E P).obj (fun k ↦ (coefficientSequenceLimit l E _).obj (N k)) ⟶
      (coefficientSequenceLimit l E (W a)).obj ((systemValue l E M P).obj N) :=
  match P with
  | .input _ => 𝟙 _
  | .unit _ => 𝟙 _
  | .tensor P Q =>
      (IntegralOnSlice.completedTensor l E (W a) none).map
        (Prod.mkHom (comparison P N) (comparison Q N)) ≫
          tensorComparison l E M a ((systemValue l E M P).obj N) ((systemValue l E M Q).obj N)
  | .pullback f P => (integralDerivedPullback l E f).map (comparison P N) ≫
      pullbackComparison l E M f ((systemValue l E M P).obj N)

/-- Coherent reduction comparison e_(S_P) after R(beta_P).
Source: node proof step 8 (blueprint: lem-pur-completed-operation-tower-substitution). -/
def reductionComparison {a : S} (P : Expression W location a)
    (N : ∀ k : I, coefficientSequenceDerived l E (W (location k))) :=
  (M.calculus a).reduction.map (comparison l E M P N) ≫
    (M.calculus a).adjunction.counit.app ((systemValue l E M P).obj N)

/-- Canonical comparison between substitution and system evaluation, recursively using
functoriality, with identity components at inputs and units.
Source: node proof step 12 (blueprint: lem-pur-completed-operation-tower-substitution). -/
def systemSubstitution {J : Type j} {location' : J → S}
    (σ : ∀ k : I, Expression W location' (location k)) {a : S}
    (P : Expression W location a)
    (N : ∀ k : J, coefficientSequenceDerived l E (W (location' k))) :
    (systemValue l E M (P.substitute σ)).obj N ≅
      (systemValue l E M P).obj (fun k ↦ (systemValue l E M (σ k)).obj N) :=
  match P with
  | .input _ => Iso.refl _
  | .unit _ => Iso.refl _
  | .tensor P Q => (tensor l E M a).mapIso
      (Iso.prod (systemSubstitution σ P N) (systemSubstitution σ Q N))
  | .pullback f P => (integralComparisonDerivedSequencePullback l E f).mapIso
      (systemSubstitution σ P N)

/-- The analogous parenthesis-preserving substitution comparison for completed evaluation.
Source: node proof step 12 (blueprint: lem-pur-completed-operation-tower-substitution). -/
def completedSubstitution {J : Type j} {location' : J → S}
    (σ : ∀ k : I, Expression W location' (location k)) {a : S}
    (P : Expression W location a)
    (N : ∀ k : J, DerivedCategory (scalarReductionSource l E (W (location' k)))) :
    (completedValue l E (P.substitute σ)).obj N ≅
      (completedValue l E P).obj (fun k ↦ (completedValue l E (σ k)).obj N) :=
  match P with
  | .input _ => Iso.refl _
  | .unit _ => Iso.refl _
  | .tensor P Q => (IntegralOnSlice.completedTensor l E (W a) none).mapIso
      (Iso.prod (completedSubstitution σ P N) (completedSubstitution σ Q N))
  | .pullback f P => (integralDerivedPullback l E f).mapIso
      (completedSubstitution σ P N)

/-- The named primitive constraints and their finite contexts. The composition
constraint has the direction (h >> f)* -> f* >> h* of the finite adjunction comparison.
Inverses and composites are included, so this also covers arrows inside a larger expression.
Source: node proof steps 9--12 (blueprint: lem-pur-completed-operation-tower-substitution). -/
inductive StructuralMap : {a : S} → Expression W location a →
    Expression W location a → Type (max t s i)
  | associator {a : S} (P Q R : Expression W location a) :
      StructuralMap (.tensor (.tensor P Q) R) (.tensor P (.tensor Q R))
  | leftUnitor {a : S} (P : Expression W location a) : StructuralMap (.tensor (.unit a) P) P
  | rightUnitor {a : S} (P : Expression W location a) : StructuralMap (.tensor P (.unit a)) P
  | symmetry {a : S} (P Q : Expression W location a) : StructuralMap (.tensor P Q) (.tensor Q P)
  | composition {a b c : S} (h : W c ⟶ W a) (f : W a ⟶ W b)
      (P : Expression W location b) :
      StructuralMap (.pullback (h ≫ f) P) (.pullback h (.pullback f P))
  | identity {a : S} (P : Expression W location a) : StructuralMap P P
  | inverse {a : S} {P Q : Expression W location a} : StructuralMap P Q → StructuralMap Q P
  | compose {a : S} {P Q R : Expression W location a} :
      StructuralMap P Q → StructuralMap Q R → StructuralMap P R
  | tensor {a : S} {P Q R V : Expression W location a} :
      StructuralMap P Q → StructuralMap R V → StructuralMap (.tensor P R) (.tensor Q V)
  | pullback {a b : S} (f : W a ⟶ W b) {P Q : Expression W location b} :
      StructuralMap P Q → StructuralMap (.pullback f P) (.pullback f Q)

/-- The actual system constraint: total-complex reassociation, action, Koszul sign,
or the localization of the finite adjunction-normalized composition map.
Source: node proof steps 9 and 11 (blueprint: lem-pur-completed-operation-tower-substitution). -/
def structuralValue {a : S} {P Q : Expression W location a} (α : StructuralMap P Q)
    (N : ∀ k : I, coefficientSequenceDerived l E (W (location k))) :
    (systemValue l E M P).obj N ≅ (systemValue l E M Q).obj N :=
  match α with
  | .associator P Q R => (M.system a).closed.monoidal.associator
      ((systemValue l E M P).obj N) ((systemValue l E M Q).obj N)
        ((systemValue l E M R).obj N)
  | .leftUnitor P => (tensor l E M a).mapIso
      (Iso.prod (M.system a).unitIso.symm (Iso.refl _)) ≪≫
        (M.system a).closed.monoidal.leftUnitor ((systemValue l E M P).obj N)
  | .rightUnitor P => (tensor l E M a).mapIso
      (Iso.prod (Iso.refl _) (M.system a).unitIso.symm) ≪≫
        (M.system a).closed.monoidal.rightUnitor ((systemValue l E M P).obj N)
  | .symmetry P Q => (M.system a).symmetric.braiding
      ((systemValue l E M P).obj N) ((systemValue l E M Q).obj N)
  | .composition h f P => (integralComparisonSystemComposition l E h f).app
      ((systemValue l E M P).obj N)
  | .identity _ => Iso.refl _
  | .inverse α => (structuralValue α N).symm
  | .compose α β => structuralValue α N ≪≫ structuralValue β N
  | .tensor α β => (tensor l E M a).mapIso
      (Iso.prod (structuralValue α N) (structuralValue β N))
  | .pullback f α => (integralComparisonDerivedSequencePullback l E f).mapIso (structuralValue α N)

/-- The normalization and comparison assertions, with explicit whole-system naturality
and every quotient-transition square. No equality of derived maps is inferred from evaluations.
Source: node statement paragraphs 1--3, proof steps 2--10
(blueprint: lem-pur-completed-operation-tower-substitution). -/
structure ComparisonLaws : Prop where
  /-- The canonical coherent counit, not merely its independently evaluated components. -/
  counit : ∀ (a : S) (N : coefficientSequenceDerived l E (W a)),
    IsNormalizedCoefficientSequence l E (W a) N →
      IsIso ((M.calculus a).adjunction.counit.app N)
  /-- Unit, tensor and inverse image preserve normalization, hence so does every expression. -/
  normalized : ∀ {I : Type i} {location : I → S} {a : S}
    (P : Expression W location a)
    (N : ∀ k : I, coefficientSequenceDerived l E (W (location k))),
    (∀ k, IsNormalizedCoefficientSequence l E _ (N k)) →
      IsNormalizedCoefficientSequence l E _ ((systemValue l E M P).obj N)
  /-- Both the recursive comparison and its specified coherent reduction are invertible. -/
  invertible : ∀ {I : Type i} {location : I → S} {a : S}
    (P : Expression W location a)
    (N : ∀ k : I, coefficientSequenceDerived l E (W (location k))),
    (∀ k, IsNormalizedCoefficientSequence l E _ (N k)) →
      IsIso (comparison l E M P N) ∧ IsIso (reductionComparison l E M P N)
  /-- Naturality in morphisms of every normalized input system. -/
  naturality : ∀ {I : Type i} {location : I → S} {a : S}
    (P : Expression W location a)
    (N N' : ∀ k : I, coefficientSequenceDerived l E (W (location k)))
    (_hN : ∀ k, IsNormalizedCoefficientSequence l E _ (N k))
    (_hN' : ∀ k, IsNormalizedCoefficientSequence l E _ (N' k))
    (v : ∀ k, N k ⟶ N' k),
    (completedValue l E P).map (fun k ↦ (coefficientSequenceLimit l E _).map (v k)) ≫
        comparison l E M P N' =
      comparison l E M P N ≫
        (coefficientSequenceLimit l E _).map ((systemValue l E M P).map v)
  /-- Every actual quotient transition is respected by gamma, including identity quotients. -/
  transitions : ∀ {I : Type i} {location : I → S} {a : S}
    (P : Expression W location a)
    (N : ∀ k : I, coefficientSequenceDerived l E (W (location k)))
    (_hN : ∀ k, IsNormalizedCoefficientSequence l E _ (N k))
    {m n : ℕ} (h : n ≤ m),
    (coefficientSequenceDerivedTransition l E (W a) h).app _ ≫
        (normalizedDVRRes l E (W a) h).map
          ((coefficientSequenceDerivedEvaluation l E (W a) n).map
            (reductionComparison l E M P N)) =
      (coefficientSequenceDerivedEvaluation l E (W a) m).map
          (reductionComparison l E M P N) ≫
        (coefficientSequenceDerivedTransition l E (W a) h).app _

/-- Compatibility of the *recursive* comparisons with simultaneous substitution.
The two evaluation isomorphisms preserve parentheses; the middle arrow applies
completed operations to the comparisons for the substituted expressions.
Source: node proof step 12 (blueprint: lem-pur-completed-operation-tower-substitution). -/
def SubstitutionLaw : Prop :=
  ∀ {I : Type i} {J : Type j} {location : I → S} {location' : J → S}
    (σ : ∀ k : I, Expression W location' (location k)) {a : S}
    (P : Expression W location a)
    (N : ∀ k : J, coefficientSequenceDerived l E (W (location' k)))
    (_hN : ∀ k, IsNormalizedCoefficientSequence l E _ (N k)),
    (completedSubstitution l E σ P
        (fun k ↦ (coefficientSequenceLimit l E _).obj (N k))).hom ≫
        (completedValue l E P).map (fun k ↦ comparison l E M (σ k) N) ≫
        comparison l E M P (fun k ↦ (systemValue l E M (σ k)).obj N) =
      comparison l E M (P.substitute σ) N ≫
        (coefficientSequenceLimit l E _).map (systemSubstitution l E M σ P N).hom

/-- The canonical completed constraints are characterized uniquely by their limit
and coherent reduction squares. In particular their forward map is exactly
beta_P >> L(alpha) >> beta_Q inverse. Uniqueness specifies the canonical map;
RingedSiteDualityModel fixes the system tensor maps on total-complex generators.
Source: node proof steps 9--11 (blueprint: lem-pur-completed-operation-tower-substitution). -/
def StructuralLaw : Prop :=
  ∀ {I : Type i} {location : I → S} {a : S}
    {P Q : Expression W location a} (α : StructuralMap P Q)
    (N : ∀ k : I, coefficientSequenceDerived l E (W (location k)))
    (_hN : ∀ k, IsNormalizedCoefficientSequence l E _ (N k)),
    ∃! c : (completedValue l E P).obj
          (fun k ↦ (coefficientSequenceLimit l E _).obj (N k)) ≅
        (completedValue l E Q).obj
          (fun k ↦ (coefficientSequenceLimit l E _).obj (N k)),
      c.hom ≫ comparison l E M Q N = comparison l E M P N ≫
          (coefficientSequenceLimit l E _).map (structuralValue l E M α N).hom ∧
        (M.calculus a).reduction.map c.hom ≫ reductionComparison l E M Q N =
          reductionComparison l E M P N ≫ (structuralValue l E M α N).hom

/-- Coherent substitution of normalized systems into completed operations.
All system and completed comparisons use their canonical quotient-complex models;
no finiteness, boundedness, Tor-amplitude or constructibility restriction is imposed.

Source: Bhatt--Scholze, Definition 3.4.10 and Lemma 6.5.9(4), motivating the completed
operations; agent refinement in blueprint main-20261015, order 2232, and node proof
steps 1--12 (blueprint: lem-pur-completed-operation-tower-substitution).

Proof plan:
1. Use lem-coef-semilinear-derived-sections on the whole ringed sequence site.
Choose flat-term K-flat representatives by lem-pc-kflat-resolution. Total tensor
and inverse image preserve them by lem-pur-kflat-total-tensor-model and
lem-weil-pbc-ringed-pullback-preserves-kflat, including quotient coefficient maps.
2. For m >= n, monoidal scalar extension identifies the tensor transition adjunct
with the tensor of the two normalization isomorphisms. On generators it sends
(a tensor x) tensor b to tau_A(a) tensor b tau_N(x). The quotient cocycle follows
from the input cocycles and scalar association, by
lem-weil-pbc-ringed-topoi-derived-tensor-pullback.
3. For inverse image, use the commuting constant-coefficient square and the inverse
scalar-association map of lem-pur-cochain-pullback-tensor-coherence. Compose with
the pullback of the input transition adjunct. Factor the actual input transition
through its scalar-extension unit before this adjunct. Multiplication of three
coefficient factors proves the cocycle. The coefficient unit is normalized.
4. lem-coef-derived-system-evaluation-calculus gives R -| L and its natural counit.
lem-coef-normalized-dvr-effectivity makes that *system map* invertible on normalized
systems. Its naturality is an equality before evaluation.
5. Identify the quotient-complex operations with reduction, the whole-system
operation, and total limit. Exact pro-etale countable products and
lem-weil-strict-roos-comparison identify the Cone(1-s)[-1] model naturally with
that total limit. The representative comparisons of
lem-pur-integral-operations-well-defined fix the functor identifications. The
augmentation fixes completion_unit and the normalized closed tensor fixes Models.
6. Apply L to T(e_A,e_N) or F(e_C) to obtain exactly tensorComparison and
pullbackComparison; their inverses are images of the inverse counits.
7. Induct on Expression. Inputs and units have identity comparisons; tensor and
pullback use the preceding comparisons after applying their functors to the child
comparisons. Every factor is invertible and every system value is normalized.
8. The reduction comparison is e after R(beta). This is a whole-system isomorphism,
so it commutes with every quotient transition, including m=n.
9. On total-complex representatives, reassociation preserves x tensor (y tensor z),
unitors multiply scalars, and symmetry multiplies by (-1)^(pq). Scalar association
preserves these formulas. Factor arbitrary transitions through their normalization
adjuncts and use naturality; no canonical-unit-transition hypothesis is imposed.
10. Conjugating L of these system maps by beta defines the completed constraints.
Counit naturality gives the gamma square, as an equation of system maps.
11. The pullback compositor is the mate of finite direct-image composition in
lem-pur-proetale-module-pullback-composition. Exact finite inverse image derives
it termwise. Scalar association multiplies coefficients, so it respects quotients;
its inverse inserts 1. Apply the same conjugation to obtain completed composition.
12. Naturality follows by induction and counit naturality. Induct again on the
outer expression for substitution: the two routes have identical leaf maps, and
the tensor/pullback induction steps reduce to counit naturality and functoriality.
This gives SubstitutionLaw and extends the structural equations through all finite
contexts. No faithfulness of evaluations or tensor/limit interchange is used. -/
theorem completedOperationTowerSubstitution {S : Type s} (W : S → Scheme.{t})
    (_hl : ∀ (a : S) (x : W a), IsUnit (l : (W a).residueField x)) :
    ∃ M : Models l E W,
      ComparisonLaws.{t, u, s, i} l E M ∧
      SubstitutionLaw.{t, u, s, i, j} l E M ∧ StructuralLaw.{t, u, s, i} l E M := by
  sorry

end WeilConjectures.CompletedOperations
