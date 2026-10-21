/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O2
-/
module

public import Sheaf.Paper.CompletedOperationExpressions
public import Sheaf.Paper.CompletedPrimitiveCounitComparison

/-! # Naturality and substitution of recursive coherent-counit comparisons

Source: blueprint main-20261015, order 2232, coefficient-passage compatibility,
and the explicit typed-tree argument of the node
(blueprint: lem-pur-expression-counit-substitution-coherence).

The primitive operations and their quotient/Roos realizations are the recorded
ones. All equations are in ordinary derived categories of whole systems.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u s i j
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures.CounitExpressions
open CompletedOperations

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The specified primitive comparison data, simultaneously at all expression locations.
The reduction, limit, tensor, geometric inverse image and their representative
normalizations are exactly those of the primitive comparison dependency.
Source: node paragraphs 1--3 and proof steps 1--2, blueprint order 2232
(blueprint: lem-pur-expression-counit-substitution-coherence). -/
structure Data {S : Type s} (W : S → Scheme.{t}) where
  reduction : ∀ a : S, CoefficientDerivedSystemReduction l E (W a)
  roos : ∀ a : S, PrimitiveCounit.RoosRealization l E (W a)
  primitive : ∀ (a b : S) (f : W a ⟶ W b),
    PrimitiveCounit.Comparisons l E f (W a) (reduction a) (reduction b) (roos a) (roos a)

variable {S : Type s} {W : S → Scheme.{t}} (D : Data l E W)

/-- The coefficient unit B_n[0], with its actual quotient transitions.
Source: node paragraph 1, blueprint order 2232
(blueprint: lem-pur-expression-counit-substitution-coherence). -/
def unit (a : S) : coefficientSequenceDerived l E (W a) :=
  DerivedCategory.Q.obj
    ((HomologicalComplex.single (coefficientSequenceModules l E (W a))
      (ComplexShape.up ℤ) 0).obj
        (SheafOfModules.unit
          ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)}
            RingCat.{max u (t + 1)})).obj (coefficientSequenceCommRingSheaf l E (W a)))))

variable {I : Type i} {location : I → S}

/-- Functorial whole-system evaluation using the primitive dependency's tensor and pullback.
Source: node paragraph 3 and proof step 1, blueprint order 2232
(blueprint: lem-pur-expression-counit-substitution-coherence). -/
def system {a : S} : Expression W location a →
    ((∀ k : I, coefficientSequenceDerived l E (W (location k))) ⥤
      coefficientSequenceDerived l E (W a))
  | .input k => Pi.eval _ k
  | .unit a => (Functor.const _).obj (unit l E (W := W) a)
  | .tensor P Q => (system P).prod' (system Q) ⋙ (D.reduction a).systemClosed.tensor
  | .pullback f P => system P ⋙ PrimitiveCounit.pull l E f

/-- Functorial completed evaluation, with unchanged parentheses and unit L(U).
Source: node paragraph 3 and proof step 1, blueprint order 2232
(blueprint: lem-pur-expression-counit-substitution-coherence). -/
def completed {a : S} : Expression W location a →
    ((∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k)))) ⥤
      DerivedCategory (scalarReductionSource l E (W a)))
  | .input k => Pi.eval _ k
  | .unit a => (Functor.const _).obj
      ((coefficientSequenceLimit l E (W a)).obj (unit l E (W := W) a))
  | .tensor P Q => (completed P).prod' (completed Q) ⋙ integralCompletedTensor l E (W a)
  | .pullback f P => completed P ⋙ integralDerivedPullback l E f

/-- Recursive beta: identities at leaves, then the specified primitive counit maps.
Source: node paragraph 3 and proof steps 1--2, blueprint order 2232
(blueprint: lem-pur-expression-counit-substitution-coherence). -/
def beta {a : S} (P : Expression W location a)
    (N : ∀ k : I, coefficientSequenceDerived l E (W (location k))) :
    (completed l E P).obj (fun k ↦ (coefficientSequenceLimit l E _).obj (N k)) ⟶
      (coefficientSequenceLimit l E (W a)).obj ((system l E D P).obj N) :=
  match P with
  | .input _ => 𝟙 _
  | .unit _ => 𝟙 _
  | .tensor P Q =>
      (integralCompletedTensor l E (W a)).map (Prod.mkHom (beta P N) (beta Q N)) ≫
        PrimitiveCounit.tensorBeta l E (W a) (D.reduction a)
          (D.primitive a a (𝟙 (W a))).tensor
          ((system l E D P).obj N) ((system l E D Q).obj N)
  | .pullback f P => (integralDerivedPullback l E f).map (beta P N) ≫
      PrimitiveCounit.pullBeta l E f (D.reduction _) (D.primitive _ _ f).geometric
        ((system l E D P).obj N)

/-- Recursive gamma is the actual whole-system counit after reduction of beta.
Source: node paragraph 3 and proof step 6, blueprint order 2232
(blueprint: lem-pur-expression-counit-substitution-coherence). -/
def gamma {a : S} (P : Expression W location a)
    (N : ∀ k : I, coefficientSequenceDerived l E (W (location k))) :=
  (D.reduction a).reduction.map (beta l E D P N) ≫
    (D.reduction a).adjunction.counit.app ((system l E D P).obj N)

/-- Parenthesis-preserving system substitution identification d.
Source: node paragraph 5 and proof step 7, blueprint order 2232
(blueprint: lem-pur-expression-counit-substitution-coherence). -/
def systemSubstitution {J : Type j} {location' : J → S}
    (H : ∀ k : I, Expression W location' (location k)) {a : S}
    (P : Expression W location a)
    (N : ∀ k : J, coefficientSequenceDerived l E (W (location' k))) :
    (system l E D (P.substitute H)).obj N ≅
      (system l E D P).obj (fun k ↦ (system l E D (H k)).obj N) :=
  match P with
  | .input _ => Iso.refl _
  | .unit _ => Iso.refl _
  | .tensor P Q => (D.reduction a).systemClosed.tensor.mapIso
      (Iso.prod (systemSubstitution H P N) (systemSubstitution H Q N))
  | .pullback f P => (PrimitiveCounit.pull l E f).mapIso (systemSubstitution H P N)

/-- Parenthesis-preserving completed substitution identification c.
Source: node paragraph 5 and proof step 7, blueprint order 2232
(blueprint: lem-pur-expression-counit-substitution-coherence). -/
def completedSubstitution {J : Type j} {location' : J → S}
    (H : ∀ k : I, Expression W location' (location k)) {a : S}
    (P : Expression W location a)
    (N : ∀ k : J, DerivedCategory (scalarReductionSource l E (W (location' k)))) :
    (completed l E (P.substitute H)).obj N ≅
      (completed l E P).obj (fun k ↦ (completed l E (H k)).obj N) :=
  match P with
  | .input _ => Iso.refl _
  | .unit _ => Iso.refl _
  | .tensor P Q => (integralCompletedTensor l E (W a)).mapIso
      (Iso.prod (completedSubstitution H P N) (completedSubstitution H Q N))
  | .pullback f P => (integralDerivedPullback l E f).mapIso (completedSubstitution H P N)

/-- Closure of normalization under precisely the three non-input constructors.
Source: node paragraph 4, blueprint order 2232
(blueprint: lem-pur-expression-counit-substitution-coherence). -/
structure Normalization : Prop where
  unit : ∀ a : S, IsNormalizedCoefficientSequence l E (W a) (unit l E (W := W) a)
  tensor : ∀ (a : S) (A N : coefficientSequenceDerived l E (W a)),
    IsNormalizedCoefficientSequence l E (W a) A →
    IsNormalizedCoefficientSequence l E (W a) N →
    IsNormalizedCoefficientSequence l E (W a) ((D.reduction a).systemClosed.tensor.obj (A, N))
  pullback : ∀ {a b : S} (f : W a ⟶ W b) (C : coefficientSequenceDerived l E (W b)),
    IsNormalizedCoefficientSequence l E (W b) C →
    IsNormalizedCoefficientSequence l E (W a) ((PrimitiveCounit.pull l E f).obj C)

/-- Both structural compatibility equations, writing the conjugation formula as
ahat followed by beta_Q equals beta_P followed by L(a). Beta_Q is invertible
on normalized inputs, so this is precisely the node's conjugation formula.
Source: node last paragraph and proof step 11, blueprint order 2232
(blueprint: lem-pur-expression-counit-substitution-coherence). -/
def Compatible {a : S} {P Q : Expression W location a}
    (N : ∀ k : I, coefficientSequenceDerived l E (W (location k)))
    (v : (system l E D P).obj N ⟶ (system l E D Q).obj N)
    (w : (completed l E P).obj (fun k ↦ (coefficientSequenceLimit l E _).obj (N k)) ⟶
      (completed l E Q).obj (fun k ↦ (coefficientSequenceLimit l E _).obj (N k))) : Prop :=
  w ≫ beta l E D Q N = beta l E D P N ≫ (coefficientSequenceLimit l E _).map v ∧
    (D.reduction a).reduction.map w ≫ gamma l E D Q N = gamma l E D P N ≫ v

/-- Naturality, both substitution equations, and invertibility of the recursive maps.
Source: node paragraphs 4--5 and proof steps 2--10, blueprint order 2232
(blueprint: lem-pur-expression-counit-substitution-coherence). -/
structure EvaluationLaws : Prop where
  invertible : ∀ {a : S} (P : Expression W location a)
    (N : ∀ k : I, coefficientSequenceDerived l E (W (location k))),
    (∀ k, IsNormalizedCoefficientSequence l E _ (N k)) →
      IsIso (beta l E D P N) ∧ IsIso (gamma l E D P N)
  naturality : ∀ {a : S} (P : Expression W location a)
    (N N' : ∀ k : I, coefficientSequenceDerived l E (W (location k)))
    (_hN : ∀ k, IsNormalizedCoefficientSequence l E _ (N k))
    (_hN' : ∀ k, IsNormalizedCoefficientSequence l E _ (N' k)) (v : ∀ k, N k ⟶ N' k),
    (completed l E P).map (fun k ↦ (coefficientSequenceLimit l E _).map (v k)) ≫
        beta l E D P N' = beta l E D P N ≫
          (coefficientSequenceLimit l E _).map ((system l E D P).map v) ∧
      (D.reduction a).reduction.map
          ((completed l E P).map (fun k ↦ (coefficientSequenceLimit l E _).map (v k))) ≫
        gamma l E D P N' = gamma l E D P N ≫ (system l E D P).map v
  substitution : ∀ {J : Type j} {location' : J → S}
    (H : ∀ k : I, Expression W location' (location k)) {a : S}
    (P : Expression W location a)
    (N : ∀ k : J, coefficientSequenceDerived l E (W (location' k)))
    (_hN : ∀ k, IsNormalizedCoefficientSequence l E _ (N k)),
    beta l E D (P.substitute H) N ≫
        (coefficientSequenceLimit l E _).map (systemSubstitution l E D H P N).hom =
      (completedSubstitution l E H P
        (fun k ↦ (coefficientSequenceLimit l E _).obj (N k))).hom ≫
        (completed l E P).map (fun k ↦ beta l E D (H k) N) ≫
        beta l E D P (fun k ↦ (system l E D (H k)).obj N) ∧
      gamma l E D (P.substitute H) N ≫ (systemSubstitution l E D H P N).hom =
        (D.reduction a).reduction.map
          ((completedSubstitution l E H P
            (fun k ↦ (coefficientSequenceLimit l E _).obj (N k))).hom ≫
            (completed l E P).map (fun k ↦ beta l E D (H k) N)) ≫
          gamma l E D P (fun k ↦ (system l E D (H k)).obj N)

/-- Persistence of the two structural equations under all operations of the node.
Structural maps in the substitution clause are natural transformations of evaluations;
the displayed maps conjugate their components by the recursively defined c and d.
Source: node last paragraph and proof steps 11--15, blueprint order 2232
(blueprint: lem-pur-expression-counit-substitution-coherence). -/
structure StructuralLaws : Prop where
  identity : ∀ {a : S} (P : Expression W location a)
    (N : ∀ k : I, coefficientSequenceDerived l E (W (location k)))
    (_hN : ∀ k, IsNormalizedCoefficientSequence l E _ (N k)),
    Compatible l E D (P := P) (Q := P) N (𝟙 _) (𝟙 _)
  composition : ∀ {a : S} {P Q R : Expression W location a}
    (N : ∀ k : I, coefficientSequenceDerived l E (W (location k)))
    (_hN : ∀ k, IsNormalizedCoefficientSequence l E _ (N k))
    (v : (system l E D P).obj N ⟶ (system l E D Q).obj N)
    (v' : (system l E D Q).obj N ⟶ (system l E D R).obj N)
    (w : (completed l E P).obj (fun k ↦ (coefficientSequenceLimit l E _).obj (N k)) ⟶
      (completed l E Q).obj (fun k ↦ (coefficientSequenceLimit l E _).obj (N k)))
    (w' : (completed l E Q).obj (fun k ↦ (coefficientSequenceLimit l E _).obj (N k)) ⟶
      (completed l E R).obj (fun k ↦ (coefficientSequenceLimit l E _).obj (N k))),
    Compatible l E D N v w → Compatible l E D N v' w' →
      Compatible l E D N (v ≫ v') (w ≫ w')
  inverse : ∀ {a : S} {P Q : Expression W location a}
    (N : ∀ k : I, coefficientSequenceDerived l E (W (location k)))
    (_hN : ∀ k, IsNormalizedCoefficientSequence l E _ (N k))
    (v : (system l E D P).obj N ≅ (system l E D Q).obj N)
    (w : (completed l E P).obj (fun k ↦ (coefficientSequenceLimit l E _).obj (N k)) ≅
      (completed l E Q).obj (fun k ↦ (coefficientSequenceLimit l E _).obj (N k))),
    Compatible l E D N v.hom w.hom → Compatible l E D N v.inv w.inv
  tensor : ∀ {a : S} {P Q R V : Expression W location a}
    (N : ∀ k : I, coefficientSequenceDerived l E (W (location k)))
    (_hN : ∀ k, IsNormalizedCoefficientSequence l E _ (N k))
    (v : (system l E D P).obj N ⟶ (system l E D Q).obj N)
    (v' : (system l E D R).obj N ⟶ (system l E D V).obj N)
    (w : (completed l E P).obj (fun k ↦ (coefficientSequenceLimit l E _).obj (N k)) ⟶
      (completed l E Q).obj (fun k ↦ (coefficientSequenceLimit l E _).obj (N k)))
    (w' : (completed l E R).obj (fun k ↦ (coefficientSequenceLimit l E _).obj (N k)) ⟶
      (completed l E V).obj (fun k ↦ (coefficientSequenceLimit l E _).obj (N k))),
    Compatible l E D N v w → Compatible l E D N v' w' →
      Compatible l E D (P := .tensor P R) (Q := .tensor Q V) N
        ((D.reduction a).systemClosed.tensor.map (Prod.mkHom v v'))
        ((integralCompletedTensor l E (W a)).map (Prod.mkHom w w'))
  pullback : ∀ {a b : S} (f : W a ⟶ W b) {P Q : Expression W location b}
    (N : ∀ k : I, coefficientSequenceDerived l E (W (location k)))
    (_hN : ∀ k, IsNormalizedCoefficientSequence l E _ (N k))
    (v : (system l E D P).obj N ⟶ (system l E D Q).obj N)
    (w : (completed l E P).obj (fun k ↦ (coefficientSequenceLimit l E _).obj (N k)) ⟶
      (completed l E Q).obj (fun k ↦ (coefficientSequenceLimit l E _).obj (N k))),
    Compatible l E D N v w →
      Compatible l E D (P := .pullback f P) (Q := .pullback f Q) N
        ((PrimitiveCounit.pull l E f).map v) ((integralDerivedPullback l E f).map w)
  substitution : ∀ {J : Type j} {location' : J → S}
    (H : ∀ k : I, Expression W location' (location k)) {a : S}
    {P Q : Expression W location a}
    (v : system l E D P ⟶ system l E D Q) (w : completed l E P ⟶ completed l E Q),
    (∀ (A : ∀ k : I, coefficientSequenceDerived l E (W (location k)))
      (_hA : ∀ k, IsNormalizedCoefficientSequence l E _ (A k)),
      Compatible l E D A (v.app A)
        (w.app (fun k ↦ (coefficientSequenceLimit l E _).obj (A k)))) →
    ∀ (N : ∀ k : J, coefficientSequenceDerived l E (W (location' k)))
      (_hN : ∀ k, IsNormalizedCoefficientSequence l E _ (N k)),
      Compatible l E D (P := P.substitute H) (Q := Q.substitute H) N
        ((systemSubstitution l E D H P N).hom ≫
          v.app (fun k ↦ (system l E D (H k)).obj N) ≫
          (systemSubstitution l E D H Q N).inv)
        ((completedSubstitution l E H P
          (fun k ↦ (coefficientSequenceLimit l E _).obj (N k))).hom ≫
          w.app (fun k ↦ (completed l E (H k)).obj
            (fun k ↦ (coefficientSequenceLimit l E _).obj (N k))) ≫
          (completedSubstitution l E H Q
            (fun k ↦ (coefficientSequenceLimit l E _).obj (N k))).inv)

private theorem pair_comp {C : Type*} [Category C] {A B C' X Y Z : C}
    (f : A ⟶ B) (f' : B ⟶ C') (g : X ⟶ Y) (g' : Y ⟶ Z) :
    Prod.mkHom (f ≫ f') (g ≫ g') = Prod.mkHom f g ≫ Prod.mkHom f' g' := rfl

private theorem system_normalized (h : Normalization l E D) {a : S}
    (P : Expression W location a)
    (N : ∀ k : I, coefficientSequenceDerived l E (W (location k)))
    (hN : ∀ k, IsNormalizedCoefficientSequence l E _ (N k)) :
    IsNormalizedCoefficientSequence l E (W a) ((system l E D P).obj N) := by
  induction P with
  | input k => exact hN k
  | unit a => exact h.unit a
  | tensor P Q hp hq => exact h.tensor _ _ _ hp hq
  | pullback f P hp => exact h.pullback f _ hp

private theorem beta_isIso (h : Normalization l E D) {a : S}
    (P : Expression W location a)
    (N : ∀ k : I, coefficientSequenceDerived l E (W (location k)))
    (hN : ∀ k, IsNormalizedCoefficientSequence l E _ (N k)) :
    IsIso (beta l E D P N) := by
  induction P with
  | input k => change IsIso (𝟙 _); infer_instance
  | unit a => change IsIso (𝟙 _); infer_instance
  | @tensor a P Q hp hq =>
    have := hp
    have := hq
    have := (D.primitive a a (𝟙 _)).tensor_iso _ _
      (system_normalized l E D h P N hN) (system_normalized l E D h Q N hN)
    have : IsIso (Prod.mkHom (beta l E D P N) (beta l E D Q N)) :=
      (Iso.prod (asIso (beta l E D P N)) (asIso (beta l E D Q N))).isIso_hom
    dsimp only [beta]
    infer_instance
  | @pullback a b f P hp =>
    have := hp
    have := (D.primitive a b f).geometric_iso _ (system_normalized l E D h P N hN)
    dsimp only [beta]
    infer_instance

private theorem beta_natural {a : S} (P : Expression W location a)
    (N N' : ∀ k : I, coefficientSequenceDerived l E (W (location k)))
    (v : ∀ k, N k ⟶ N' k) :
    (completed l E P).map (fun k ↦ (coefficientSequenceLimit l E _).map (v k)) ≫
        beta l E D P N' = beta l E D P N ≫
          (coefficientSequenceLimit l E _).map ((system l E D P).map v) := by
  induction P with
  | input k => simp [completed, system, beta, Pi.eval]
  | unit a => simp [completed, system, beta]
  | @tensor a P Q hp hq =>
    dsimp only [completed, system, beta, Functor.comp_map, Functor.prod'_map]
    rw [← Category.assoc, ← Functor.map_comp, prod_comp, hp, hq,
      pair_comp, Functor.map_comp, Category.assoc,
      (D.primitive a a (𝟙 _)).tensor_naturality, Category.assoc]
  | @pullback a b f P hp =>
    dsimp only [completed, system, beta, Functor.comp_map]
    rw [← Category.assoc, ← Functor.map_comp, hp, Functor.map_comp,
      Category.assoc, (D.primitive a b f).geometric_naturality, Category.assoc]

private theorem reduction_square {a : S}
    {A B : coefficientSequenceDerived l E (W a)}
    {K K' : DerivedCategory (scalarReductionSource l E (W a))}
    (b : K ⟶ (coefficientSequenceLimit l E _).obj A)
    (b' : K' ⟶ (coefficientSequenceLimit l E _).obj B)
    (v : A ⟶ B) (w : K ⟶ K')
    (h : w ≫ b' = b ≫ (coefficientSequenceLimit l E _).map v) :
    (D.reduction a).reduction.map w ≫
        ((D.reduction a).reduction.map b' ≫ (D.reduction a).adjunction.counit.app B) =
      ((D.reduction a).reduction.map b ≫ (D.reduction a).adjunction.counit.app A) ≫ v := by
  rw [← Category.assoc, ← Functor.map_comp, h, Functor.map_comp, Category.assoc,
    (D.primitive a a (𝟙 _)).counit_naturality, Category.assoc]

private theorem compatible_of_beta {a : S} {P Q : Expression W location a}
    (N : ∀ k : I, coefficientSequenceDerived l E (W (location k)))
    (v : (system l E D P).obj N ⟶ (system l E D Q).obj N)
    (w : (completed l E P).obj (fun k ↦ (coefficientSequenceLimit l E _).obj (N k)) ⟶
      (completed l E Q).obj (fun k ↦ (coefficientSequenceLimit l E _).obj (N k)))
    (h : w ≫ beta l E D Q N = beta l E D P N ≫ (coefficientSequenceLimit l E _).map v) :
    Compatible l E D N v w :=
  ⟨h, reduction_square l E D _ _ v w h⟩

private theorem beta_substitution {J : Type j} {location' : J → S}
    (H : ∀ k : I, Expression W location' (location k)) {a : S}
    (P : Expression W location a)
    (N : ∀ k : J, coefficientSequenceDerived l E (W (location' k))) :
    beta l E D (P.substitute H) N ≫
        (coefficientSequenceLimit l E _).map (systemSubstitution l E D H P N).hom =
      (completedSubstitution l E H P
        (fun k ↦ (coefficientSequenceLimit l E _).obj (N k))).hom ≫
        (completed l E P).map (fun k ↦ beta l E D (H k) N) ≫
        beta l E D P (fun k ↦ (system l E D (H k)).obj N) := by
  induction P with
  | input k => simp [Expression.substitute, systemSubstitution, completedSubstitution,
      beta, completed, Pi.eval]
  | unit a => simp [Expression.substitute, systemSubstitution, completedSubstitution,
      beta, completed]
  | @tensor a P Q hp hq =>
    dsimp only [Expression.substitute, beta, systemSubstitution, completedSubstitution,
      completed, system, Functor.comp_map, Functor.prod'_map, Functor.mapIso_hom,
      Iso.prod]
    rw [Category.assoc, ← (D.primitive a a (𝟙 _)).tensor_naturality,
      ← Category.assoc, ← Functor.map_comp, prod_comp, hp, hq]
    simp only [pair_comp, Functor.map_comp, Category.assoc]
  | @pullback a b f P hp =>
    dsimp only [Expression.substitute, beta, systemSubstitution, completedSubstitution,
      completed, system, Functor.comp_map, Functor.mapIso_hom]
    rw [Category.assoc, ← (D.primitive a b f).geometric_naturality,
      ← Category.assoc, ← Functor.map_comp, hp]
    simp only [Functor.map_comp, Category.assoc]

/-- Recursive comparisons are natural, commute with simultaneous substitution,
and preserve both structural compatibility equations in every finite context.
The primitive data retains the actual quotient-complex/Roos realization; the only
closure hypothesis is that unit, tensor and geometric inverse image preserve normalization.

Source: blueprint main-20261015, order 2232, final coefficient-passage assertion;
explicit proof steps 1--15 of the node
(blueprint: lem-pur-expression-counit-substitution-coherence).

Proof plan:
1. Evaluate typed finite expressions recursively on objects and maps. Functor laws
hold at leaves and are preserved at tensor and pullback vertices; repeated inputs
use the same object and map. Closure gives normalized system evaluations.
2. The primitive dependency gives natural invertible tensor and pullback comparisons,
with their specified coherent counit. Induction makes beta and gamma invertible.
3. At input leaves naturality is the identity on L(v); at units all input maps are
identities. This includes the empty input context.
4. At a tensor expand beta, use both child squares and bifunctoriality, then the
primitive tensor naturality square at the two child system maps.
5. At a pullback expand beta, apply the child square and primitive pullback naturality.
6. Apply reduction to beta naturality and use e R L(u) = u e, proving gamma naturality
as a whole-system equation before evaluation.
7. Induct on the outer expression for simultaneous substitution. At inputs the map
is beta_H; at units it is identity. The maps c and d are recursive functor images.
8. At tensor apply primitive naturality to the two child d maps, then the child
substitution equations and bifunctoriality.
9. At pullback use primitive naturality at the child d map and the child equation.
The primitive maps use exactly L T(e,e) and L F(e), so no new comparison is chosen.
10. Apply reduction and counit naturality at d to obtain the displayed gamma equation.
11. A beta structural square implies its gamma square by counit naturality at the
whole-system structural map; invertibility gives the stated conjugation formula.
12. Identity, composition and inverse closure follow by composing the beta squares
and cancelling invertible factors. Functors preserve the corresponding inverse words.
13. Tensor and pullback contexts follow by expanding beta at their root, using the
child structural squares and primitive naturality at the structural system maps.
14. For simultaneous substitution, use the two substitution equations and naturality
of the completed structural transformation at the family beta_H. The resulting
square is the flattened structural square; step 11 gives its reduction equation.
15. This applies to any supplied primitive tensor constraints or finite normalized
pullback compositors once their primitive squares hold, without asserting them here.
Unit-only expressions, empty scheme/input sets and repeated slots are included.
No equality of arbitrary derived morphisms is inferred from evaluation. -/
theorem expressionCounitSubstitutionCoherence
    (_hl : ∀ (a : S) (x : W a), IsUnit (l : (W a).presheaf.stalk x))
    (_h : Normalization l E D) :
    EvaluationLaws.{t, u, s, i, j} l E D (location := location) ∧
      StructuralLaws.{t, u, s, i, j} l E D (location := location) := by
  constructor
  · constructor
    · intro a P N hN
      have hb := beta_isIso l E D _h P N hN
      have := (D.primitive a a (𝟙 _)).counit_effective _
        (system_normalized l E D _h P N hN)
      exact ⟨hb, by dsimp only [gamma]; infer_instance⟩
    · intro a P N N' hN hN' v
      have hb := beta_natural l E D P N N' v
      exact ⟨hb, reduction_square l E D _ _ _ _ hb⟩
    · intro J location' H a P N hN
      have hb := beta_substitution l E D H P N
      refine ⟨hb, ?_⟩
      apply Eq.symm
      apply reduction_square
      simpa only [Category.assoc] using hb.symm
  · constructor
    · intro a P N hN
      apply compatible_of_beta
      simp
    · intro a P Q R N hN v v' w w' hv hv'
      apply compatible_of_beta
      dsimp only [Compatible] at hv hv'
      rw [Category.assoc, hv'.1, ← Category.assoc, hv.1,
        Category.assoc, Functor.map_comp]
    · intro a P Q N hN v w hv
      apply compatible_of_beta
      dsimp only [Compatible] at hv
      apply (cancel_mono ((coefficientSequenceLimit l E _).map v.hom)).mp
      simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id]
      rw [← hv.1, ← Category.assoc, w.inv_hom_id, Category.id_comp]
      rw [(coefficientSequenceLimit l E (W a)).map_id]
      exact (Category.comp_id _).symm
    · intro a P Q R V N hN v v' w w' hv hv'
      apply compatible_of_beta
      dsimp only [Compatible] at hv hv'
      dsimp only [beta, system, completed]
      rw [← Category.assoc, ← Functor.map_comp, prod_comp, hv.1, hv'.1,
        pair_comp, Functor.map_comp, Category.assoc,
        (D.primitive a a (𝟙 _)).tensor_naturality, Category.assoc]
    · intro a b f P Q N hN v w hv
      apply compatible_of_beta
      dsimp only [Compatible] at hv
      dsimp only [beta, system, completed]
      rw [← Category.assoc, ← Functor.map_comp, hv.1, Functor.map_comp,
        Category.assoc, (D.primitive a b f).geometric_naturality, Category.assoc]
    · intro J location' H a P Q v w hv N hN
      apply compatible_of_beta
      have h := (hv (fun k ↦ (system l E D (H k)).obj N)
        (fun k ↦ system_normalized l E D _h (H k) N hN)).1
      have hp := beta_substitution l E D H P N
      have hq := beta_substitution l E D H Q N
      have hn := w.naturality (fun k ↦ beta l E D (H k) N)
      apply (cancel_mono ((coefficientSequenceLimit l E _).map
        (systemSubstitution l E D H Q N).hom)).mp
      simp only [Functor.map_comp, Category.assoc]
      rw [hq, Iso.inv_hom_id_assoc]
      rw [← Category.assoc (w.app _), ← hn, Category.assoc, h]
      have hp' := congrArg (fun z ↦ z ≫ (coefficientSequenceLimit l E _).map
        (v.app (fun k ↦ (system l E D (H k)).obj N))) hp
      simpa only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
        Functor.map_id, Category.comp_id] using hp'.symm

end WeilConjectures.CounitExpressions
