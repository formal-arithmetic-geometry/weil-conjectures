/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q56
-/
module

public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import Sheaf.CategoryTheory.KInjectiveDerivedMapComputation
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.AlgebraicGeometry.CondensedModulePullbackExact

/-!
# Simultaneous K-injective models for direct-image and open-restriction words

Source: Stacks Project, Derived Categories, Tags 08BJ, 070I and 070Y; Modules on Sites,
Section 07A5, and Injectives, Theorem 079P. The finite-word and diagram argument is the
agent formulation in the DAG (blueprint: lem-sfb-kinjective-direct-image-open-word-model).

The helpers describe the words, their actual functors, canonical evaluations, and finite
pasting expressions occurring in this single statement. They introduce no alternative
module category, module operation, localization, or notion of K-injectivity.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.KInjectiveWords

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The module category with the stipulated pulled-back coefficients.
Source: the node's notation M_T (blueprint: lem-sfb-kinjective-direct-image-open-word-model). -/
abbrev Modules (T : Scheme.{u}) :=
  CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)

/-- Finite composable words of the two allowed kinds of letters; `comp` retains parentheses.
Source: the finite words in clauses (i)--(iii), including empty words
(blueprint: lem-sfb-kinjective-direct-image-open-word-model). -/
inductive Word : Scheme.{u} → Scheme.{u} → Type (u + 1)
  | nil (S : Scheme.{u}) : Word S S
  | push {S T : Scheme.{u}} (a : S ⟶ T) : Word S T
  | restrict {U T : Scheme.{u}} (j : U ⟶ T) (hj : IsOpenImmersion j) : Word T U
  | comp {S T U : Scheme.{u}} (w : Word S T) (v : Word T U) : Word S U

/-- Interpret a word using the specified module direct images and open restrictions.
Source: clause (i), specified adjunctions of the two operations, Stacks Tag 08BJ
(blueprint: lem-sfb-kinjective-direct-image-open-word-model). -/
def Word.ordinary {S T : Scheme.{u}} : Word S T → (Modules Λ S ⥤ Modules Λ T)
  | .nil S => 𝟭 (Modules Λ S)
  | .push a => CondensedRing.lowerStar Λ a
  | .restrict j hj => letI := hj; CondensedRing.upperStar Λ j
  | .comp w v => ordinary w ⋙ ordinary v

/-- Additivity inherited from the actual letters and functor composition.
Source: proof step 3, the degreewise homotopy equation
(blueprint: lem-sfb-kinjective-direct-image-open-word-model).
Proof: induct on words. The identity functor is additive; the supplied lowerStar and
upperStar instances give additivity for each letter. Composition of additive functors
is additive, giving the induction step. -/
theorem Word.ordinary_additive_of_letters {S T : Scheme.{u}} (w : Word S T) :
    (w.ordinary Λ).Additive := by
  sorry

/-- The additive structure on the word functor, supplied by the named additivity theorem.
Source: proof step 3, additivity of all letters and composites
(blueprint: lem-sfb-kinjective-direct-image-open-word-model). -/
instance Word.ordinary_additive {S T : Scheme.{u}} (w : Word S T) :
    (w.ordinary Λ).Additive := w.ordinary_additive_of_letters Λ

/-- The derived word: total right derivation for pushforward, exact induction for restriction.
Source: clauses (ii)--(iii), Stacks Tag 070Y
(blueprint: lem-sfb-kinjective-direct-image-open-word-model). -/
def Word.derived {S T : Scheme.{u}} : Word S T →
    (DerivedCategory (Modules Λ S) ⥤ DerivedCategory (Modules Λ T))
  | .nil S => 𝟭 (DerivedCategory (Modules Λ S))
  | .push a => (CondensedRing.lowerStar Λ a).rightDerivedFunctor
  | .restrict j hj => letI := hj; (CondensedRing.upperStar Λ j).mapDerivedCategory
  | .comp w v => derived w ⋙ derived v

/-- Every unbounded complex admits a K-injective resolution in the actual internal modules.
Source: Stacks Section 07A5 and Theorem 079P
(blueprint: lem-sfb-kinjective-direct-image-open-word-model).

Proof (step 1): use the exact additive section-ring equivalence of
lem-sfb-internal-module-operations-transport. Apply prop-pur-kinjective-resolutions-exist
on the small site. Exactness preserves acyclicity and full faithfulness and additivity
transport null-homotopies, so the sectionwise resolution transports back. -/
theorem resolutions (S : Scheme.{u}) (N : CochainComplex (Modules Λ S) ℤ) :
    ∃ (I : CochainComplex (Modules Λ S) ℤ) (a : N ⟶ I), I.IsKInjective ∧ QuasiIso a := by
  sorry

/-- Every allowed letter and word preserves K-injective complexes.
Source: Stacks Tag 08BJ (blueprint: lem-sfb-kinjective-direct-image-open-word-model).

Proof (steps 2--3): apply lem-weil-pbc-right-adjoint-preserves-kinjective to the specified
adjunction a^* ⊣ a_*, using det-prop-sfb-module-pullback-exact-main; for an open use the
specified exact left adjoint j_! ⊣ j^*. Induct on the word. The empty word fixes I;
composition applies the two preservation results successively. -/
theorem Word.preservesKInjectives {S T : Scheme.{u}} (w : Word S T) :
    (w.ordinary Λ).PreservesKInjectiveComplexes := by
  sorry

/-- A simultaneous evaluation family on all K-injective models of the allowed words.
Source: clause (ii), proof step 5, Stacks Tag 070Y
(blueprint: lem-sfb-kinjective-direct-image-open-word-model). -/
abbrev EvaluationFamily :=
  ∀ {S T : Scheme.{u}} (w : Word S T) (I : CochainComplex (Modules Λ S) ℤ)
    [I.IsKInjective], (w.derived Λ).obj (DerivedCategory.Q.obj I) ≅
      DerivedCategory.Q.obj (((w.ordinary Λ).mapHomologicalComplex (.up ℤ)).obj I)

/-- The composition rule for evaluations, using the actual degreewise compositor.
Source: proof step 5, Stacks Tag 070Y
(blueprint: lem-sfb-kinjective-direct-image-open-word-model). -/
def compositeEvaluation (e : EvaluationFamily Λ) {S T U : Scheme.{u}}
    (w : Word S T) (v : Word T U) (I : CochainComplex (Modules Λ S) ℤ)
    [I.IsKInjective] :
    ((w.comp v).derived Λ).obj (DerivedCategory.Q.obj I) ≅
      DerivedCategory.Q.obj ((((w.comp v).ordinary Λ).mapHomologicalComplex (.up ℤ)).obj I) :=
  letI := w.preservesKInjectives Λ
  (v.derived Λ).mapIso (e w I) ≪≫
    e v (((w.ordinary Λ).mapHomologicalComplex (.up ℤ)).obj I) ≪≫
    DerivedCategory.Q.mapIso
      ((Functor.mapHomologicalComplexCompIso
        (Iso.refl (w.ordinary Λ ⋙ v.ordinary Λ)) (.up ℤ)).app I)

/-- The canonical recursive normalization: identity for the empty word, inverse derived
unit for direct image, exact factorization for restriction, and successive evaluations
for a composite. These equations determine all evaluation data uniquely.
Source: proof steps 4--5, Stacks Tag 070Y
(blueprint: lem-sfb-kinjective-direct-image-open-word-model). -/
def EvaluationNormalized (e : EvaluationFamily Λ) : Prop :=
  (∀ (S : Scheme.{u}) (I : CochainComplex (Modules Λ S) ℤ) [I.IsKInjective],
    e (.nil S) I = (DerivedCategory.Q.mapIso
      ((Functor.mapHomologicalComplexIdIso _ (.up ℤ)).app I)).symm) ∧
  (∀ {S T : Scheme.{u}} (a : S ⟶ T) (I : CochainComplex (Modules Λ S) ℤ)
    [I.IsKInjective],
    e (.push a) I = (CondensedRing.lowerStar Λ a).rightDerivedFunctorObjQIso I) ∧
  (∀ {U T : Scheme.{u}} (j : U ⟶ T) [hj : IsOpenImmersion j]
    (I : CochainComplex (Modules Λ T) ℤ) [I.IsKInjective],
    e (.restrict j hj) I = (CondensedRing.upperStar Λ j).mapDerivedCategoryFactors.app I) ∧
  (∀ {S T U : Scheme.{u}} (w : Word S T) (v : Word T U)
    (I : CochainComplex (Modules Λ S) ℤ) [I.IsKInjective],
    e (.comp w v) I = compositeEvaluation Λ e w v I)

/-- Existence and uniqueness of the canonically normalized simultaneous evaluations.
Source: clause (ii), proof steps 4--5, Stacks Tag 070Y
(blueprint: lem-sfb-kinjective-direct-image-open-word-model).

Proof: induct on words. The empty word has the identity evaluation. For direct image,
lem-sf-kinjective-derived-map-computation supplies the inverse-unit evaluation; for
restriction use its exact factorization. The preservation result makes each intermediate
word image K-injective. A composite evaluates its first word, applies the second derived
word, evaluates at the intermediate K-injective, and uses the degreewise compositor.
These formulas give the family. Induction and the four normalization equations show
that any other family has equal evaluations on every word and every I; extensionality
then gives equality of families. Thus no unspecified comparison is chosen. -/
theorem evaluations_existsUnique : ∃! e : EvaluationFamily Λ, EvaluationNormalized Λ e := by
  sorry

/-- The evaluation specified uniquely by the inverse-unit and composition equations.
Source: clause (ii), proof steps 4--5, Stacks Tag 070Y
(blueprint: lem-sfb-kinjective-direct-image-open-word-model). -/
def Word.evaluation {S T : Scheme.{u}} (w : Word S T)
    (I : CochainComplex (Modules Λ S) ℤ) [I.IsKInjective] :
    (w.derived Λ).obj (DerivedCategory.Q.obj I) ≅
      DerivedCategory.Q.obj (((w.ordinary Λ).mapHomologicalComplex (.up ℤ)).obj I) :=
  (evaluations_existsUnique Λ).exists.choose w I

/-- Evaluation on any quasi-isomorphic K-injective resolution, with no monomorphism condition.
Source: proof step 5, Stacks Tag 070Y
(blueprint: lem-sfb-kinjective-direct-image-open-word-model). -/
def Word.resolutionEvaluation {S T : Scheme.{u}} (w : Word S T)
    {N I : CochainComplex (Modules Λ S) ℤ} [I.IsKInjective]
    (a : N ⟶ I) [QuasiIso a] :
    (w.derived Λ).obj (DerivedCategory.Q.obj N) ≅
      DerivedCategory.Q.obj (((w.ordinary Λ).mapHomologicalComplex (.up ℤ)).obj I) :=
  (w.derived Λ).mapIso (asIso (DerivedCategory.Q.map a)) ≪≫ w.evaluation Λ I

/-- Arbitrary derived arrows have a unique homotopy-class lift, and every word computes
that arrow on the common resolutions.
Source: proof step 6, Stacks Tags 070I and 070Y
(blueprint: lem-sfb-kinjective-direct-image-open-word-model).

Proof: lem-weil-pbc-kinjective-hom-derived gives the unique lift. Induct on the word.
For a pushforward letter apply lem-sf-kinjective-derived-map-computation; for a restriction
use naturality of its exact factorization. Composition substitutes these equalities in
the recursive evaluations; for the empty word the assertion is the defining lift equation.
Degreewise additivity ensures that the image depends only on the homotopy class. -/
theorem word_map_computation {S T : Scheme.{u}} (w : Word S T)
    {N N' I J : CochainComplex (Modules Λ S) ℤ} [I.IsKInjective] [J.IsKInjective]
    (a : N ⟶ I) (b : N' ⟶ J) [QuasiIso a] [QuasiIso b]
    (h : DerivedCategory.Q.obj N ⟶ DerivedCategory.Q.obj N') :
    (∃! t : (HomotopyCategory.quotient (Modules Λ S) (.up ℤ)).obj I ⟶
      (HomotopyCategory.quotient (Modules Λ S) (.up ℤ)).obj J,
      DerivedCategory.Qh.map t = Functor.kInjectiveResolutionHomTarget a b h) ∧
    (∀ t : (HomotopyCategory.quotient (Modules Λ S) (.up ℤ)).obj I ⟶
      (HomotopyCategory.quotient (Modules Λ S) (.up ℤ)).obj J,
      DerivedCategory.Qh.map t = Functor.kInjectiveResolutionHomTarget a b h →
      (w.resolutionEvaluation Λ a).inv ≫ (w.derived Λ).map h ≫
        (w.resolutionEvaluation Λ b).hom = (w.ordinary Λ).kInjectiveHomotopyImage t) := by
  sorry

/-- The same word on ordinary sheaves over the reconstructed section-ring sheaves.
Source: clause (i), proof step 1 (blueprint: lem-sfb-kinjective-direct-image-open-word-model). -/
def Word.sectionwise {S T : Scheme.{u}} : Word S T →
    (SheafOfModules.{u + 1} (InternalModuleOperations.ring Λ S) ⥤
      SheafOfModules.{u + 1} (InternalModuleOperations.ring Λ T))
  | .nil S => 𝟭 _
  | .push a => InternalModuleOperations.lowerStar Λ a
  | .restrict j hj => letI := hj; InternalModuleOperations.upperStar Λ j
  | .comp w v => sectionwise w ⋙ sectionwise v

/-- The canonical operation comparison under the existing section-ring equivalences.
Source: clause (i), the comparisons of lem-sfb-internal-module-operations-transport,
iterated with functor associators (blueprint: lem-sfb-kinjective-direct-image-open-word-model). -/
def Word.sectionComparison {S T : Scheme.{u}} (w : Word S T) :
    w.ordinary Λ ⋙ (InternalModuleOperations.equivalence Λ T).functor ≅
      (InternalModuleOperations.equivalence Λ S).functor ⋙ w.sectionwise Λ :=
  match w with
  | .nil S => (Functor.leftUnitor _ ) ≪≫ (Functor.rightUnitor _).symm
  | .push a => InternalModuleOperations.lowerComparison Λ a
  | .restrict j hj => letI := hj; InternalModuleOperations.upperComparison Λ j
  | .comp w v =>
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (w.ordinary Λ) (sectionComparison v) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (sectionComparison w) (v.sectionwise Λ) ≪≫
        Functor.associator _ _ _

/-- K-injectivity and quasi-isomorphisms identify under the actual section-ring equivalence.
Together with sectionComparison this is the same-representatives-and-functors clause.
Source: clause (i), proof step 1, Stacks Section 07A5
(blueprint: lem-sfb-kinjective-direct-image-open-word-model).

Proof: the equivalence and inverse are additive and exact by
lem-sfb-internal-module-operations-transport. They preserve and reflect acyclic complexes,
quasi-isomorphisms, and the degreewise null-homotopy equation. Full faithfulness then
identifies all maps from every acyclic complex, in both directions. -/
theorem sectionwise_representatives (S : Scheme.{u})
    (I J : CochainComplex (Modules Λ S) ℤ) (a : I ⟶ J) :
    (I.IsKInjective ↔ CochainComplex.IsKInjective
      (((InternalModuleOperations.equivalence Λ S).mapHomologicalComplex (.up ℤ)).functor.obj
        I)) ∧
    (QuasiIso a ↔ QuasiIso
      (((InternalModuleOperations.equivalence Λ S).mapHomologicalComplex (.up ℤ)).functor.map
        a)) := by
  sorry

/-- Canonical change of resolution, oriented from the first evaluated model to the second.
Source: clause (ii), proof step 7, Stacks Tag 070I
(blueprint: lem-sfb-kinjective-direct-image-open-word-model). -/
def Word.transition {S T : Scheme.{u}} (w : Word S T)
    {N I J : CochainComplex (Modules Λ S) ℤ} [I.IsKInjective] [J.IsKInjective]
    (a : N ⟶ I) (b : N ⟶ J) [QuasiIso a] [QuasiIso b] :
    DerivedCategory.Q.obj (((w.ordinary Λ).mapHomologicalComplex (.up ℤ)).obj I) ≅
      DerivedCategory.Q.obj (((w.ordinary Λ).mapHomologicalComplex (.up ℤ)).obj J) :=
  (w.resolutionEvaluation Λ a).symm ≪≫ w.resolutionEvaluation Λ b

/-- Transition computation and the three-resolution cocycle.
Source: clause (ii), proof step 7, Stacks Tags 070I and 070Y
(blueprint: lem-sfb-kinjective-direct-image-open-word-model).

Proof: specialize word_map_computation to the identity derived arrow, giving exactly
the displayed image of u. The hom-bijection makes the reverse lift its homotopy inverse.
The word preserves homotopies, so this remains an inverse after applying the word.
The product of two transitions cancels the middle evaluation; equivalently uniqueness
identifies the composite homotopy class with the third transition class. -/
theorem transition_computation_and_cocycle {S T : Scheme.{u}} (w : Word S T)
    {N I J K : CochainComplex (Modules Λ S) ℤ}
    [I.IsKInjective] [J.IsKInjective] [K.IsKInjective]
    (a : N ⟶ I) (b : N ⟶ J) (c : N ⟶ K) [QuasiIso a] [QuasiIso b] [QuasiIso c] :
    (∀ t : (HomotopyCategory.quotient (Modules Λ S) (.up ℤ)).obj I ⟶
      (HomotopyCategory.quotient (Modules Λ S) (.up ℤ)).obj J,
      DerivedCategory.Qh.map t =
        Functor.kInjectiveResolutionHomTarget a b (𝟙 (DerivedCategory.Q.obj N)) →
      (w.transition Λ a b).hom = (w.ordinary Λ).kInjectiveHomotopyImage t) ∧
    w.transition Λ a b ≪≫ w.transition Λ b c = w.transition Λ a c := by
  sorry

/-- Homotopic chain-map representatives give the same localized image under every word.
Source: clauses (ii)--(iii), proof step 3, the additive homotopy equation
(blueprint: lem-sfb-kinjective-direct-image-open-word-model).

Proof: applying each additive letter to t-t'=dh+hd preserves this equation degreewise.
Iterate over the word, including the empty word. Localization through the homotopy
category identifies the resulting homotopic maps. -/
theorem homotopic_representatives {S T : Scheme.{u}} (w : Word S T)
    {I J : CochainComplex (Modules Λ S) ℤ} (t t' : I ⟶ J) (h : Homotopy t t') :
    DerivedCategory.Q.map (((w.ordinary Λ).mapHomologicalComplex (.up ℤ)).map t) =
      DerivedCategory.Q.map (((w.ordinary Λ).mapHomologicalComplex (.up ℤ)).map t') := by
  sorry

/-- The normalization that characterizes descent, required for every complex and every
K-injective resolution simultaneously.
Source: clause (iii), Stacks Tag 070Y
(blueprint: lem-sfb-kinjective-direct-image-open-word-model). -/
def IsEvaluationLift {S T : Scheme.{u}} {w v : Word S T}
    (θ : w.ordinary Λ ⟶ v.ordinary Λ) (δ : w.derived Λ ⟶ v.derived Λ) : Prop :=
  ∀ (N I : CochainComplex (Modules Λ S) ℤ) [I.IsKInjective]
    (a : N ⟶ I) [QuasiIso a],
    (w.resolutionEvaluation Λ a).inv ≫ δ.app (DerivedCategory.Q.obj N) ≫
      (v.resolutionEvaluation Λ a).hom =
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex θ (.up ℤ)).app I)

/-- Unique descent of an arbitrary, possibly noninvertible, underived transformation.
Source: clause (iii), proof steps 8--9, Stacks Tags 070I and 070Y
(blueprint: lem-sfb-kinjective-direct-image-open-word-model).

Proof: on QN conjugate Q(theta_I) by the two evaluations. Naturality for the transition
u and the transition computation prove independence of the resolution. For any derived
arrow h, word_map_computation identifies its conjugate with the image of a homotopy class
t:I→J. Naturality of theta on a chain representative proves the naturality square, and
additivity makes it independent of that representative. Every derived object is represented
by a complex up to canonical localization isomorphism, so the component formula determines
a unique natural transformation on the entire unbounded derived category. -/
theorem descent_existsUnique {S T : Scheme.{u}} {w v : Word S T}
    (θ : w.ordinary Λ ⟶ v.ordinary Λ) :
    ∃! δ : w.derived Λ ⟶ v.derived Λ, IsEvaluationLift Λ θ δ := by
  sorry

/-- The unique normalized descent, chosen from its uniqueness theorem rather than from
an unconstrained existence statement.
Source: clause (iii), proof steps 8--9
(blueprint: lem-sfb-kinjective-direct-image-open-word-model). -/
def Word.cell {S T : Scheme.{u}} {w v : Word S T}
    (θ : w.ordinary Λ ⟶ v.ordinary Λ) : w.derived Λ ⟶ v.derived Λ :=
  (descent_existsUnique Λ θ).exists.choose

/-- The prescribed descent satisfies its normalization for every resolution.
Source: clause (iii), proof steps 8--9
(blueprint: lem-sfb-kinjective-direct-image-open-word-model).

Proof: take the defining property of the unique transformation in descent_existsUnique.
This property quantifies over all resolutions, hence includes their independence. -/
theorem cell_evaluation {S T : Scheme.{u}} {w v : Word S T}
    (θ : w.ordinary Λ ⟶ v.ordinary Λ) : IsEvaluationLift Λ θ (Word.cell Λ θ) := by
  sorry

/-- Finite diagrams built from arbitrary cells, identities, vertical compositions, both
whiskerings, and the canonical associators and unitors in both directions.
Source: clause (iii), proof steps 10--11
(blueprint: lem-sfb-kinjective-direct-image-open-word-model). -/
inductive Expression : {S T : Scheme.{u}} → Word S T → Word S T → Type (u + 2)
  | cell {S T : Scheme.{u}} {w v : Word S T}
      (θ : w.ordinary Λ ⟶ v.ordinary Λ) : Expression w v
  | id {S T : Scheme.{u}} (w : Word S T) : Expression w w
  | vcomp {S T : Scheme.{u}} {w v z : Word S T}
      (e : Expression w v) (f : Expression v z) : Expression w z
  | input {R S T : Scheme.{u}} (x : Word R S) {w v : Word S T}
      (e : Expression w v) : Expression (.comp x w) (.comp x v)
  | output {R S T : Scheme.{u}} {w v : Word R S} (e : Expression w v)
      (y : Word S T) : Expression (.comp w y) (.comp v y)
  | assoc {R S T U : Scheme.{u}} (w : Word R S) (v : Word S T) (z : Word T U) :
      Expression (.comp (.comp w v) z) (.comp w (.comp v z))
  | assocInv {R S T U : Scheme.{u}} (w : Word R S) (v : Word S T) (z : Word T U) :
      Expression (.comp w (.comp v z)) (.comp (.comp w v) z)
  | leftUnit {S T : Scheme.{u}} (w : Word S T) : Expression (.comp (.nil S) w) w
  | leftUnitInv {S T : Scheme.{u}} (w : Word S T) : Expression w (.comp (.nil S) w)
  | rightUnit {S T : Scheme.{u}} (w : Word S T) : Expression (.comp w (.nil T)) w
  | rightUnitInv {S T : Scheme.{u}} (w : Word S T) : Expression w (.comp w (.nil T))

/-- The actual underived transformation evaluated by a finite diagram expression.
Source: clause (iii), proof step 11
(blueprint: lem-sfb-kinjective-direct-image-open-word-model). -/
def Expression.ordinary {S T : Scheme.{u}} {w v : Word S T} :
    Expression Λ w v → (w.ordinary Λ ⟶ v.ordinary Λ)
  | .cell θ => θ
  | .id _ => 𝟙 _
  | .vcomp e f => ordinary e ≫ ordinary f
  | .input x e => Functor.whiskerLeft (x.ordinary Λ) (ordinary e)
  | .output e y => Functor.whiskerRight (ordinary e) (y.ordinary Λ)
  | .assoc w v z => (Functor.associator (w.ordinary Λ) (v.ordinary Λ) (z.ordinary Λ)).hom
  | .assocInv w v z => (Functor.associator (w.ordinary Λ) (v.ordinary Λ) (z.ordinary Λ)).inv
  | .leftUnit w => (Functor.leftUnitor (w.ordinary Λ)).hom
  | .leftUnitInv w => (Functor.leftUnitor (w.ordinary Λ)).inv
  | .rightUnit w => (Functor.rightUnitor (w.ordinary Λ)).hom
  | .rightUnitInv w => (Functor.rightUnitor (w.ordinary Λ)).inv

/-- Evaluate the same finite expression using descended cells and the actual derived
whiskerings, associators and unitors.
Source: clause (iii), proof steps 10--11
(blueprint: lem-sfb-kinjective-direct-image-open-word-model). -/
def Expression.derived {S T : Scheme.{u}} {w v : Word S T} :
    Expression Λ w v → (w.derived Λ ⟶ v.derived Λ)
  | .cell θ => Word.cell Λ θ
  | .id _ => 𝟙 _
  | .vcomp e f => derived e ≫ derived f
  | .input x e => Functor.whiskerLeft (x.derived Λ) (derived e)
  | .output e y => Functor.whiskerRight (derived e) (y.derived Λ)
  | .assoc w v z => (Functor.associator (w.derived Λ) (v.derived Λ) (z.derived Λ)).hom
  | .assocInv w v z => (Functor.associator (w.derived Λ) (v.derived Λ) (z.derived Λ)).inv
  | .leftUnit w => (Functor.leftUnitor (w.derived Λ)).hom
  | .leftUnitInv w => (Functor.leftUnitor (w.derived Λ)).inv
  | .rightUnit w => (Functor.rightUnitor (w.derived Λ)).hom
  | .rightUnitInv w => (Functor.rightUnitor (w.derived Λ)).inv

/-- Descent preserves every finite composition-and-whiskering equality with the canonical
associators, and sends underived isomorphisms to derived isomorphisms.
Source: clause (iii), proof steps 9--11, Stacks Tag 070Y
(blueprint: lem-sfb-kinjective-direct-image-open-word-model).

Proof: step 9 descends the inverse of an invertible theta; uniqueness and cancellation
make its two composites identities. Step 10 checks identities and vertical composition
by cancelling the middle evaluation. For input whiskering use the identity resolution
of the K-injective word image xI and the concatenation evaluation formula. For output
whiskering apply word_map_computation to theta_I between the K-injective images wI and vI.
The recursive evaluation and the functor compositors give this concatenation formula
also for empty words and all parenthesizations. Step 11 inducts on the finite expression:
its derived value is the uniquely normalized descent of its ordinary value. Equal
ordinary expressions therefore have equal derived values; associators and unitors have
exactly their canonical functor components. No right-adjoint exactness, boundedness,
or constructibility assumption is used anywhere in these steps. -/
theorem word_diagram_descent :
    (∀ {S T : Scheme.{u}} {w v : Word S T} (e : Expression Λ w v),
      e.derived Λ = Word.cell Λ (e.ordinary Λ)) ∧
    (∀ {S T : Scheme.{u}} {w v : Word S T} (e f : Expression Λ w v),
      e.ordinary Λ = f.ordinary Λ → e.derived Λ = f.derived Λ) ∧
    (∀ {S T : Scheme.{u}} {w v : Word S T} (θ : w.ordinary Λ ⟶ v.ordinary Λ),
      IsIso θ → IsIso (Word.cell Λ θ)) := by
  sorry

end AlgebraicGeometry.ProEtale.KInjectiveWords
