/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q32
-/
module

public import Sheaf.Paper.SfCbcExtensionZeroCompletion
public import Sheaf.Paper.CompletionMateComparison
import Sheaf.Paper.CompletedPullbackAdjunction
import Sheaf.Paper.PbcActualStrictPullback
import Sheaf.Paper.CompletedPullbackReduction
import Sheaf.AlgebraicGeometry.ProEtaleCanonicalPullbackComposition
import Sheaf.Paper.ProjectionMateExact
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Sheaf.CategoryTheory.DiagramSiteRealization
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Sites.Limits
import Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison

import Sheaf.CategoryTheory.RingedToposMorphism
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.Paper.CompletedPullbackUnitTower
import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.Paper.ConstantTowerDirectImageNormalization
import Sheaf.Paper.IntegralFinitePullbackComposition
import Sheaf.Paper.PbcQbarCompletedPullback
import Sheaf.Paper.ProEtaleConstantReductionTower
/-! # Normalized reconstruction of composable completed operations

Source: blueprint fix-lem-exchanges, Proof Step 5, and its strict-diagram refinement
(blueprint: lem-sf-cbc-compact-support-composition-limit).

All categories are the published equivalent small models of the small pro-etale sites.
The model enlarges only Hom universes. Letters carry scheme maps, and both functors
are computed from those maps. Words are indexed composable chains.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency.types false
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
namespace AlgebraicGeometry.Scheme

/-- The published small model, retaining every pro-etale object.
Source: Stacks 00VC, 099M (blueprint: lem-sf-cbc-compact-support-composition-limit). -/
def sfCbcSite (T : Scheme.{t}) : AdicSites.Site.{t + 1} where
  objects := proEtaleSiteModel T
  topology := proEtaleModelTopology T

/-- Continuity of the published transported base change.
Source: Stacks 00VC (blueprint: lem-sf-cbc-compact-support-composition-limit). -/
instance sfCbcModelContinuous {U V : Scheme.{t}} (u : U ⟶ V) :
    (proEtaleModelBaseChange u).IsContinuous
      (proEtaleModelTopology V) (proEtaleModelTopology U) :=
  proEtaleModelBaseChange_isContinuous u

/-- Geometric inverse image on the equivalent small models, by sheafified Kan extension.
Source: Stacks 00VC, 099N (blueprint: lem-sf-cbc-compact-support-composition-limit). -/
abbrev sfCbcModelInverse {U V : Scheme.{t}} (u : U ⟶ V) :=
  (proEtaleModelBaseChange u).sheafPullback (Type (t + 1))
    (proEtaleModelTopology V) (proEtaleModelTopology U)

/-- Geometric direct image is precomposition with the transported base-change functor.
Source: Stacks 00VC, 099N (blueprint: lem-sf-cbc-compact-support-composition-limit). -/
abbrev sfCbcModelDirect {U V : Scheme.{t}} (u : U ⟶ V) :=
  (proEtaleModelBaseChange u).sheafPushforwardContinuous (Type (t + 1))
    (proEtaleModelTopology V) (proEtaleModelTopology U)

/-- The canonical geometric adjunction on the small models.
Source: Stacks 00VC, 099N (blueprint: lem-sf-cbc-compact-support-composition-limit). -/
def sfCbcModelAdjunction {U V : Scheme.{t}} (u : U ⟶ V) :
    sfCbcModelInverse u ⊣ sfCbcModelDirect u :=
  Functor.sheafAdjunctionContinuous (proEtaleModelBaseChange u) (Type (t + 1))
    (proEtaleModelTopology V) (proEtaleModelTopology U)

/-- The downward site equivalence preserves finite limits.
Source: Stacks 00VC (blueprint: lem-sf-cbc-compact-support-composition-limit). -/
instance sfCbcModelDownLimits (T : Scheme.{t}) :
    PreservesFiniteLimits (AsSmall.down : proEtaleSiteModel T ⥤ T.ProEt) :=
  inferInstanceAs (PreservesFiniteLimits (AsSmall.equiv.{t, t + 1, t + 1}
    (C := T.ProEt)).inverse)

/-- The upward site equivalence preserves finite limits.
Source: Stacks 00VC (blueprint: lem-sf-cbc-compact-support-composition-limit). -/
instance sfCbcModelUpLimits (T : Scheme.{t}) :
    PreservesFiniteLimits (AsSmall.up : T.ProEt ⥤ proEtaleSiteModel T) :=
  inferInstanceAs (PreservesFiniteLimits (AsSmall.equiv.{t, t + 1, t + 1}
    (C := T.ProEt)).functor)

/-- Transported base change preserves finite limits through the two site equivalences.
Source: Stacks 00VC, 09A5 (blueprint: lem-sf-cbc-compact-support-composition-limit). -/
instance sfCbcModelBaseChangeFiniteLimits {U V : Scheme.{t}} (u : U ⟶ V) :
    PreservesFiniteLimits (proEtaleModelBaseChange u) :=
  inferInstanceAs (PreservesFiniteLimits
    ((AsSmall.down : proEtaleSiteModel V ⥤ V.ProEt) ⋙ proEtaleBaseChange u ⋙ AsSmall.up))

/-- Finite limits on the site model are transported from the original site.
Source: Stacks 00VC (blueprint: lem-sf-cbc-compact-support-composition-limit). -/
instance sfCbcModelHasFiniteLimits (T : Scheme.{t}) :
    HasFiniteLimits (proEtaleSiteModel T) :=
  hasFiniteLimits_of_hasLimitsLimits_of_createsFiniteLimits
    (AsSmall.equiv.{t, t + 1, t + 1} (C := T.ProEt)).inverse

/-- Geometric inverse image is left exact on the small models.
Source: Stacks 00VC, 09A5 (blueprint: lem-sf-cbc-compact-support-composition-limit). -/
instance sfCbcModelInverseFiniteLimits {U V : Scheme.{t}} (u : U ⟶ V) :
    PreservesFiniteLimits (sfCbcModelInverse u) :=
  letI := flat_of_preservesFiniteLimits (proEtaleModelBaseChange u)
  Functor.sheafPullbackConstruction.preservesFiniteLimits
    (proEtaleModelBaseChange u) (Type (t + 1))
    (proEtaleModelTopology V) (proEtaleModelTopology U)

/-- The actual geometric morphism, with the existing algebraic lift of inverse image.
Its module functors are the constant-ring inverse image and its representing right adjoint.
Source: Stacks 00YV, 03D2, 099N
(blueprint: lem-sf-cbc-compact-support-composition-limit). -/
def sfCbcMorphism {U V : Scheme.{t}} (u : U ⟶ V) :
    AdicSites.Morphism (sfCbcSite V) (sfCbcSite U) :=
  letI := sfCbcModelInverseFiniteLimits u
  { inverse := sfCbcModelInverse u
    direct := sfCbcModelDirect u
    adjunction := sfCbcModelAdjunction u
    finiteLimits := sfCbcModelInverseFiniteLimits u
    algebra := Classical.choice (ConstantCompletion.inverseImageData_exists
      (sfCbcModelInverse u) (sfCbcModelDirect u) (sfCbcModelAdjunction u)) }


/-- A letter contains exactly its geometric map, with open immersions certified.
Source: blueprint fix-lem-exchanges Step 5
(blueprint: lem-sf-cbc-compact-support-composition-limit). -/
inductive SfCbcLetter : Scheme.{t} → Scheme.{t} → Type (t + 1) where
  | pullback {U V : Scheme.{t}} (u : U ⟶ V) : SfCbcLetter V U
  | directImage {U V : Scheme.{t}} (u : U ⟶ V) : SfCbcLetter U V
  | openExtension {U V : Scheme.{t}} (j : U ⟶ V) (hj : IsOpenImmersion j) :
      SfCbcLetter U V

/-- A finite composable chain; the indices enforce source/target matching.
Source: blueprint fix-lem-exchanges Step 5
(blueprint: lem-sf-cbc-compact-support-composition-limit). -/
inductive SfCbcWord : Scheme.{t} → Scheme.{t} → Type (t + 1) where
  | nil (T : Scheme.{t}) : SfCbcWord T T
  | snoc {S U V : Scheme.{t}} (W : SfCbcWord S U) (F : SfCbcLetter U V) : SfCbcWord S V

variable {A : Type t} [CommRing A] (d : CompleteCoefficientDatum A)

/-- The completed functor of a letter is computed from its map.
Source: Stacks 099N; blueprint fix-lem-exchanges Step 5
(blueprint: lem-sf-cbc-compact-support-composition-limit). -/
def SfCbcLetter.complete {S T : Scheme.{t}} (F : SfCbcLetter S T) :
    (sfCbcSite S).derived (ULift.{t + 1, t} A) ⥤
      (sfCbcSite T).derived (ULift.{t + 1, t} A) :=
  match F with
  | .pullback u => (sfCbcMorphism u).pull _ ⋙ (sfCbcSite T).completion _ (sfCbcModelIdeal d)
  | .directImage u => (sfCbcMorphism u).push _
  | .openExtension j hj =>
    letI := hj
    sfCbcModelDerivedExtension j A ⋙ (sfCbcSite T).completion _ (sfCbcModelIdeal d)

/-- The strict functor is termwise inverse image, derived termwise direct image,
or the published exact termwise extension, according to the letter.
Source: Stacks 0941, 099N; blueprint fix-lem-exchanges Step 5
(blueprint: lem-sf-cbc-compact-support-composition-limit). -/
def SfCbcLetter.strict {S T : Scheme.{t}} (F : SfCbcLetter S T) :
    (sfCbcSite S).towerDerived (ULift.{t + 1, t} A) ⥤
      (sfCbcSite T).towerDerived (ULift.{t + 1, t} A) :=
  match F with
  | .pullback u => (sfCbcMorphism u).towerPull _
  | .directImage u => (sfCbcMorphism u).towerPush _
  | .openExtension j hj =>
    letI := hj
    sfCbcDerivedTowerExtension j A

/-- Completed word functors are recursive composites, with identity at length zero.
Source: blueprint fix-lem-exchanges Step 5
(blueprint: lem-sf-cbc-compact-support-composition-limit). -/
def SfCbcWord.complete {S T : Scheme.{t}} (W : SfCbcWord S T) :
    (sfCbcSite S).derived (ULift.{t + 1, t} A) ⥤
      (sfCbcSite T).derived (ULift.{t + 1, t} A) :=
  match W with
  | .nil _ => 𝟭 _
  | .snoc W F => complete W ⋙ F.complete d

/-- Strict word functors are recursive composites of the actual strict letters.
Source: blueprint fix-lem-exchanges Step 5
(blueprint: lem-sf-cbc-compact-support-composition-limit). -/
def SfCbcWord.strict {S T : Scheme.{t}} (W : SfCbcWord S T) :
    (sfCbcSite S).towerDerived (ULift.{t + 1, t} A) ⥤
      (sfCbcSite T).towerDerived (ULift.{t + 1, t} A) :=
  match W with
  | .nil _ => 𝟭 _
  | .snoc W F => strict W ⋙ F.strict (A := A)

/-- The specified reduced completion unit, before any tower evaluation.
Source: Stacks 099M; blueprint fix-lem-exchanges Steps 1--2
(blueprint: lem-sf-cbc-compact-support-composition-limit). -/
def sfCbcModelReducedUnit (T : Scheme.{t}) :
    (sfCbcSite T).reduction _ (sfCbcModelIdeal d) ⟶
      (sfCbcSite T).completion _ (sfCbcModelIdeal d) ⋙
        (sfCbcSite T).reduction _ (sfCbcModelIdeal d) :=
  whiskerRight ((sfCbcSite T).unit _ (sfCbcModelIdeal d))
    ((sfCbcSite T).reduction _ (sfCbcModelIdeal d))

/-- The proof needed to take the unique inverse of the specified reduced unit.
It is a conclusion of the reconstruction theorem, never an assumption of that theorem.
Source: Stacks 099M; blueprint fix-lem-exchanges Step 2
(blueprint: lem-sf-cbc-compact-support-composition-limit). -/
def SfCbcReducedUnitsInvertible : Prop := ∀ T : Scheme.{t}, IsIso (sfCbcModelReducedUnit d T)

/-- The counit-tensor projection map as one natural transformation of strict towers.
Its component is exactly AdicSites.Morphism.towerProjection.
Source: Stacks 0B56; blueprint fix-lem-exchanges Step 3
(blueprint: lem-sf-cbc-compact-support-composition-limit). -/
def sfCbcDirectQ {U V : Scheme.{t}} (u : U ⟶ V) :
    (sfCbcMorphism u).push (ULift.{t + 1, t} A) ⋙
        (sfCbcSite V).reduction _ (sfCbcModelIdeal d) ⟶
      (sfCbcSite U).reduction _ (sfCbcModelIdeal d) ⋙ (sfCbcMorphism u).towerPush _ :=
  whiskerLeft ((sfCbcMorphism u).push _ ⋙
      (sfCbcSite V).reduction _ (sfCbcModelIdeal d))
    ((sfCbcMorphism u).towerAdjunction _).unit ≫
  whiskerRight (whiskerLeft ((sfCbcMorphism u).push _)
    ((sfCbcMorphism u).reductionPullIso _ (sfCbcModelIdeal d)).hom)
      ((sfCbcMorphism u).towerPush _) ≫
  whiskerRight (whiskerRight ((sfCbcMorphism u).adj _).counit
    ((sfCbcSite U).reduction _ (sfCbcModelIdeal d))) ((sfCbcMorphism u).towerPush _)

/-- The three specified one-letter maps. Pullback is inverse reduced unit followed by
strict pullback/tensor comparison. Direct image is the diagram counit-tensor mate.
Open extension uses exactly the normalized tensor comparison of the published extension
lemma, preceded by inverse reduced unit, hence is its q_j in the small model.
Source: blueprint fix-lem-exchanges Steps 2--4
(blueprint: lem-sf-cbc-compact-support-composition-limit). -/
def SfCbcLetter.q (hunit : SfCbcReducedUnitsInvertible d)
    {S T : Scheme.{t}} (F : SfCbcLetter S T) :
    F.complete d ⋙ (sfCbcSite T).reduction _ (sfCbcModelIdeal d) ⟶
      (sfCbcSite S).reduction _ (sfCbcModelIdeal d) ⋙ F.strict (A := A) :=
  match F with
  | .pullback u =>
    whiskerLeft ((sfCbcMorphism u).pull _)
      (@asIso _ _ _ _ (sfCbcModelReducedUnit d T) (hunit T)).inv ≫
        ((sfCbcMorphism u).reductionPullIso _ (sfCbcModelIdeal d)).inv
  | .directImage u => sfCbcDirectQ d u
  | .openExtension j hj =>
    letI := hj
    whiskerLeft (sfCbcModelDerivedExtension j A)
      (@asIso _ _ _ _ (sfCbcModelReducedUnit d T) (hunit T)).inv ≫
        (sfCbcTensorComparison_existsUnique j d).exists.choose.hom

/-- The strict comparison is recursively defined by the stipulated concatenation formula.
For the empty word it is the identity, expressed by the canonical functor unitors.
Source: blueprint fix-lem-exchanges Steps 1 and 5
(blueprint: lem-sf-cbc-compact-support-composition-limit). -/
def SfCbcWord.q (hunit : SfCbcReducedUnitsInvertible d) :
    {S T : Scheme.{t}} → (W : SfCbcWord S T) →
    W.complete d ⋙ (sfCbcSite T).reduction _ (sfCbcModelIdeal d) ⟶
      (sfCbcSite S).reduction _ (sfCbcModelIdeal d) ⋙ W.strict (A := A)
  | _, _, .nil _ => (Functor.leftUnitor _).hom ≫ (Functor.rightUnitor _).inv
  | _, _, .snoc W F => whiskerLeft (W.complete d) (F.q d hunit) ≫
      whiskerRight (SfCbcWord.q hunit W) (F.strict (A := A))

/-- Reconstruction is eta followed by derived strict inverse limit of q, by definition.
Source: blueprint fix-lem-exchanges Step 5
(blueprint: lem-sf-cbc-compact-support-composition-limit). -/
def SfCbcWord.a (hunit : SfCbcReducedUnitsInvertible d)
    {S T : Scheme.{t}} (W : SfCbcWord S T) :
    W.complete d ⟶ (sfCbcSite S).reduction _ (sfCbcModelIdeal d) ⋙
      W.strict (A := A) ⋙ (sfCbcSite T).rlim (ULift.{t + 1, t} A) :=
  whiskerLeft (W.complete d) ((sfCbcSite T).unit _ (sfCbcModelIdeal d)) ≫
    whiskerRight (W.q d hunit) ((sfCbcSite T).rlim _)


/-- Concatenation appends the letters of V after those of W, with matching middle scheme.
Source: blueprint fix-lem-exchanges Step 5
(blueprint: lem-sf-cbc-compact-support-composition-limit). -/
def SfCbcWord.append {S U T : Scheme.{t}} (W : SfCbcWord S U)
    (V : SfCbcWord U T) : SfCbcWord S T :=
  match V with
  | .nil _ => W
  | .snoc V F => (append W V).snoc F

/-- The canonical reassociation of completed functors for concatenation.
Source: blueprint fix-lem-exchanges Step 5
(blueprint: lem-sf-cbc-compact-support-composition-limit). -/
def SfCbcWord.appendCompleteIso {S U T : Scheme.{t}} (W : SfCbcWord S U)
    (V : SfCbcWord U T) : (W.append V).complete d ≅ W.complete d ⋙ V.complete d :=
  match (generalizing := true) V with
  | .nil _ => (Functor.rightUnitor _).symm
  | .snoc V F => isoWhiskerRight (appendCompleteIso W V) (F.complete d) ≪≫
      Functor.associator _ _ _

/-- The same canonical reassociation for the actual strict tower functors.
Source: blueprint fix-lem-exchanges Step 5
(blueprint: lem-sf-cbc-compact-support-composition-limit). -/
def SfCbcWord.appendStrictIso {S U T : Scheme.{t}} (W : SfCbcWord S U)
    (V : SfCbcWord U T) :
    (W.append V).strict (A := A) ≅ W.strict (A := A) ⋙ V.strict (A := A) :=
  match (generalizing := true) V with
  | .nil _ => (Functor.rightUnitor _).symm
  | .snoc V F => isoWhiskerRight (appendStrictIso W V) (F.strict (A := A)) ≪≫
      Functor.associator _ _ _

/-- A parenthesized expression in composable subwords. Every finite bracketing is included.
Source: blueprint fix-lem-exchanges Step 5
(blueprint: lem-sf-cbc-compact-support-composition-limit). -/
inductive SfCbcExpression : Scheme.{t} → Scheme.{t} → Type (t + 1) where
  | word {S T : Scheme.{t}} (W : SfCbcWord S T) : SfCbcExpression S T
  | comp {S U T : Scheme.{t}} (E : SfCbcExpression S U) (F : SfCbcExpression U T) :
      SfCbcExpression S T

/-- Forget the parentheses, retaining the complete composable chain.
Source: blueprint fix-lem-exchanges Step 5
(blueprint: lem-sf-cbc-compact-support-composition-limit). -/
def SfCbcExpression.flatten {S T : Scheme.{t}} (E : SfCbcExpression S T) : SfCbcWord S T :=
  match E with
  | .word W => W
  | .comp E F => (flatten E).append (flatten F)

/-- The completed functor with precisely the parentheses of the expression.
Source: blueprint fix-lem-exchanges Step 5
(blueprint: lem-sf-cbc-compact-support-composition-limit). -/
def SfCbcExpression.complete {S T : Scheme.{t}} (E : SfCbcExpression S T) :
    (sfCbcSite S).derived (ULift.{t + 1, t} A) ⥤
      (sfCbcSite T).derived (ULift.{t + 1, t} A) :=
  match E with
  | .word W => W.complete d
  | .comp E F => complete E ⋙ complete F

/-- The strict functor with the same parentheses.
Source: blueprint fix-lem-exchanges Step 5
(blueprint: lem-sf-cbc-compact-support-composition-limit). -/
def SfCbcExpression.strict {S T : Scheme.{t}} (E : SfCbcExpression S T) :
    (sfCbcSite S).towerDerived (ULift.{t + 1, t} A) ⥤
      (sfCbcSite T).towerDerived (ULift.{t + 1, t} A) :=
  match E with
  | .word W => W.strict (A := A)
  | .comp E F => strict E ⋙ strict F

/-- Reassociation from the flattened completed chain to the chosen parentheses.
Source: blueprint fix-lem-exchanges Step 5
(blueprint: lem-sf-cbc-compact-support-composition-limit). -/
def SfCbcExpression.completeIso {S T : Scheme.{t}} (E : SfCbcExpression S T) :
    E.flatten.complete d ≅ E.complete d :=
  match (generalizing := true) E with
  | .word _ => Iso.refl _
  | .comp E F => SfCbcWord.appendCompleteIso d E.flatten F.flatten ≪≫
      isoWhiskerRight (completeIso E) (F.flatten.complete d) ≪≫
      isoWhiskerLeft (E.complete d) (completeIso F)

/-- Reassociation from the flattened strict chain to the chosen parentheses.
Source: blueprint fix-lem-exchanges Step 5
(blueprint: lem-sf-cbc-compact-support-composition-limit). -/
def SfCbcExpression.strictIso {S T : Scheme.{t}} (E : SfCbcExpression S T) :
    E.flatten.strict (A := A) ≅ E.strict (A := A) :=
  match (generalizing := true) E with
  | .word _ => Iso.refl _
  | .comp E F => SfCbcWord.appendStrictIso E.flatten F.flatten ≪≫
      isoWhiskerRight (strictIso E) (F.flatten.strict (A := A)) ≪≫
      isoWhiskerLeft (E.strict (A := A)) (strictIso F)

/-- The comparison obtained by composing with the chosen parentheses.
Source: blueprint fix-lem-exchanges Step 5
(blueprint: lem-sf-cbc-compact-support-composition-limit). -/
def SfCbcExpression.q (hunit : SfCbcReducedUnitsInvertible d)
    {S T : Scheme.{t}} (E : SfCbcExpression S T) :
    E.complete d ⋙ (sfCbcSite T).reduction _ (sfCbcModelIdeal d) ⟶
      (sfCbcSite S).reduction _ (sfCbcModelIdeal d) ⋙ E.strict (A := A) :=
  match (generalizing := true) E with
  | .word W => W.q d hunit
  | .comp E F => whiskerLeft (E.complete d) (SfCbcExpression.q hunit F) ≫
      whiskerRight (SfCbcExpression.q hunit E) (F.strict (A := A))

/-- Reconstruction with the chosen parentheses uses the same eta then L(q) rule.
Source: blueprint fix-lem-exchanges Step 5
(blueprint: lem-sf-cbc-compact-support-composition-limit). -/
def SfCbcExpression.a (hunit : SfCbcReducedUnitsInvertible d)
    {S T : Scheme.{t}} (E : SfCbcExpression S T) :
    E.complete d ⟶ (sfCbcSite S).reduction _ (sfCbcModelIdeal d) ⋙
      E.strict (A := A) ⋙ (sfCbcSite T).rlim (ULift.{t + 1, t} A) :=
  whiskerLeft (E.complete d) ((sfCbcSite T).unit _ (sfCbcModelIdeal d)) ≫
    whiskerRight (E.q d hunit) ((sfCbcSite T).rlim _)

/-- Every clause of normalized reconstruction, on the canonical recursive maps.
No functor, arbitrary comparison or composability proposition is supplied as a field.
Source: blueprint fix-lem-exchanges, strict-diagram refinement, Steps 1--6
(blueprint: lem-sf-cbc-compact-support-composition-limit). -/
structure SfCbcNormalizedFamily (hunit : SfCbcReducedUnitsInvertible d) : Prop where
  q_isIso : ∀ {S T : Scheme.{t}} (W : SfCbcWord S T)
    (K : (sfCbcSite S).derived (ULift.{t + 1, t} A)),
    (sfCbcSite S).IsComplete _ (sfCbcModelIdeal d) K → IsIso ((W.q d hunit).app K)
  a_isIso : ∀ {S T : Scheme.{t}} (W : SfCbcWord S T)
    (K : (sfCbcSite S).derived (ULift.{t + 1, t} A)),
    (sfCbcSite S).IsComplete _ (sfCbcModelIdeal d) K → IsIso ((W.a d hunit).app K)
  empty_q : ∀ (T : Scheme.{t}) (K : (sfCbcSite T).derived (ULift.{t + 1, t} A)),
    ((SfCbcWord.nil T).q d hunit).app K =
      𝟙 (((sfCbcSite T).reduction _ (sfCbcModelIdeal d)).obj K)
  empty_a : ∀ (T : Scheme.{t}) (K : (sfCbcSite T).derived (ULift.{t + 1, t} A)),
    ((SfCbcWord.nil T).a d hunit).app K =
      ((sfCbcSite T).unit _ (sfCbcModelIdeal d)).app K
  concatenation : ∀ {S U T : Scheme.{t}} (W : SfCbcWord S U) (V : SfCbcWord U T)
    (K : (sfCbcSite S).derived (ULift.{t + 1, t} A)),
    ((W.append V).q d hunit).app K ≫
        (SfCbcWord.appendStrictIso W V).hom.app
          (((sfCbcSite S).reduction _ (sfCbcModelIdeal d)).obj K) =
      ((sfCbcSite T).reduction _ (sfCbcModelIdeal d)).map
          ((SfCbcWord.appendCompleteIso d W V).hom.app K) ≫
        (V.q d hunit).app ((W.complete d).obj K) ≫
        (V.strict (A := A)).map ((W.q d hunit).app K)
  parenthesization_q : ∀ {S T : Scheme.{t}} (E : SfCbcExpression S T)
    (K : (sfCbcSite S).derived (ULift.{t + 1, t} A)),
    (E.flatten.q d hunit).app K ≫
        (E.strictIso (A := A)).hom.app
          (((sfCbcSite S).reduction _ (sfCbcModelIdeal d)).obj K) =
      ((sfCbcSite T).reduction _ (sfCbcModelIdeal d)).map
        ((E.completeIso d).hom.app K) ≫ (E.q d hunit).app K
  parenthesization_a : ∀ {S T : Scheme.{t}} (E : SfCbcExpression S T)
    (K : (sfCbcSite S).derived (ULift.{t + 1, t} A)),
    (E.flatten.a d hunit).app K ≫
        ((sfCbcSite T).rlim _).map ((E.strictIso (A := A)).hom.app
          (((sfCbcSite S).reduction _ (sfCbcModelIdeal d)).obj K)) =
      (E.completeIso d).hom.app K ≫ (E.a d hunit).app K
  directImage : ∀ {U V : Scheme.{t}} (u : U ⟶ V)
    (K : (sfCbcSite U).derived (ULift.{t + 1, t} A)),
    (sfCbcSite U).IsComplete _ (sfCbcModelIdeal d) K →
    (((SfCbcWord.nil U).snoc (.directImage u)).a d hunit).app K =
      ((sfCbcMorphism u).push _).map (((sfCbcSite U).unit _ (sfCbcModelIdeal d)).app K) ≫
        ((sfCbcMorphism u).directLimitIso _).hom.app
          (((sfCbcSite U).reduction _ (sfCbcModelIdeal d)).obj K)

/-- Normalized strict-diagram reconstruction for finite composable words.
The finite perfect quotients, torsion quotient and Noetherianness are packaged in d,
with finiteness of every positive quotient explicit. All schemes and all unbounded
locally complete objects are allowed. The existential hunit proves invertibility of
reduction of the prescribed completion unit; the definitions then use its unique
inverse, so it is not an additional hypothesis or a choice of comparison maps.
The conclusions concern the maps of actual derived strict towers, before evaluation.

Source: blueprint fix-lem-exchanges, Proof Step 5, strict-diagram refinement
(blueprint: lem-sf-cbc-compact-support-composition-limit).

Proof:
1. Use lem-weil-pbc-diagram-site-realization to regard strict towers as modules on one
   site. By lem-weil-tower-category-levelwise-abelian their evaluations are exact.
   lem-weil-pbc-ringed-strict-tower-homotopy-limit supplies total derived inverse limit.
   lem-sp-completed-pullback-adjunction identifies completion and its specified unit.
   The empty chain gives identity q and the completion unit a.
2. By lem-sf-cbc-completed-pullback-unit-tower, reduction of the completion unit is
   invertible for every ambient object; its finite inverse is adjoint to the limit
   projection. This gives hunit. Its strict tensor comparison gives the pullback
   letter, inverse reduced unit followed by tau. The finite comparisons agree with
   lemma-weil-pbc-completed-pullback-reduction under
   lem-weil-pbc-constant-completion-equivalence and def-weil-pbc-completed-pullback.
   Successive pullbacks use lem-weil-pbc-proetale-derived-pullback-composition.
3. The direct-image q is the diagram counit-tensor projection mate of
   lem-weil-pbc-ringed-projection-mate-exact. The identity-square specialization of
   lem-sp-completion-mate-comparison proves it invertible on complete objects.
   lem-sf-cbc-constant-tower-direct-image-normalization identifies the constant towers.
   Successive direct images use lem-weil-pbc-ringed-topoi-derived-pushforward-composition.
4. lem-sf-cbc-extension-zero-completion supplies the normalized strict tensor
   comparison for extension by zero. Precompose by inverse reduced unit to obtain
   exactly q_j. It is natural and respects every quotient transition.
5. Induct on the composable chain. Whisker and compose the generator comparisons
   in the displayed order. Completed letters have complete output, and direct image
   preserves completeness by lem-sp-completed-pullback-adjunction. Thus eta is
   invertible on W_c K; applying derived inverse limit to q proves the a assertion.
   Induction on concatenations gives the normalization formula; induction on binary
   expressions and functoriality give both parenthesization equations.
6. By lem-sf-cbc-constant-tower-direct-image-normalization, the projection mate h and
   quotient augmentation i satisfy h i = R^T(i) chi in the strict diagram category.
   Apply derived inverse limit, using its canonical constant-tower normalization,
   naturality, and L(i)=eta. This gives rho eta = Ru_*(eta), with rho=L(h) followed by
   inverse direct-image/limit comparison. Rearranging gives the directImage equation
   for the canonical comparison of lem-weil-ringed-tower-pushforward-limit-comparison.
   AdicSites.Morphism.directLimitIso is its adjunction-conjugate construction from the
   identity-component constant/inverse-image comparison; its projections are therefore
   the stipulated projections. No equality is inferred from derived evaluations.
No uniform Tor or cohomological bound, compactification, exchange-pasting axiom or
faithfulness of derived evaluations is used. -/
theorem sfCbcCompactSupportCompositionLimit
    {A : Type t} [CommRing A] (d : CompleteCoefficientDatum A)
    [∀ n : ℕ, Finite (A ⧸ d.ideal ^ (n + 1))] :
    ∃ hunit : SfCbcReducedUnitsInvertible d, SfCbcNormalizedFamily d hunit := by
  sorry

end AlgebraicGeometry.Scheme
