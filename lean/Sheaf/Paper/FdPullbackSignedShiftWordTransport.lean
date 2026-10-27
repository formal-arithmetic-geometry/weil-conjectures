/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q105
-/
module

public import Sheaf.Paper.FdPullbackAugmentationCounitMatching
public import Sheaf.Paper.FdCompletedCompositorNormalization
public import Sheaf.Paper.FdScalarPullbackRealizationIdentification
public import Sheaf.Paper.IntegralPullbackShiftCoordinates
public import Sheaf.Paper.FdNormalizedIntegralCompletionComparison
public import Sheaf.Paper.SfRationalizationKaroubi
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Sheaf.CategoryTheory.StrictRoosShiftLocalization
import Sheaf.Paper.FinitePullbackStrictTowerComparison
import Sheaf.Paper.IntegralOperationsWellDefined
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Mathlib.CategoryTheory.Localization.Predicate

/-! # Signed shifts and finite-word transport for normalized pullback comparisons

Source: trace-definition auxiliary whole-tower argument, step 11; Stacks Project,
Tags 014E and 0941 (blueprint: lem-fd-pullback-signed-shift-word-transport).
The word syntax, normalized realization and scalar associators are the dependencies'
actual constructions. The records below specify their transport to the PBC presentation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.pbcIntegralDatum AlgebraicGeometry.Scheme.completedAdicChangeData
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]

/-- The canonical exact coefficient-identity shift. Source: Stacks 014E, 0941
(blueprint: lem-fd-pullback-signed-shift-word-transport). -/
instance fdSignedTransportShift (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) :
    (integralDetailedTransport X l E).CommShift ℤ :=
  inferInstanceAs ((fdCoefficientTransport l E X).mapDerivedCategory.CommShift ℤ)

/-- The canonical right-derived shift of total limit. Source: Stacks 0941
(blueprint: lem-fd-pullback-signed-shift-word-transport). -/
instance fdSignedConstantLimitShift (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) :
    (coefficientConstantTowerLimit l E X).CommShift ℤ :=
  inferInstanceAs ((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E X) ⥤
    scalarReductionSource l E X).rightDerivedFunctor.CommShift ℤ)

/-- Exact quotient restriction followed by the canonical right-derived limit shift.
Source: Stacks 0941 (blueprint: lem-fd-pullback-signed-shift-word-transport). -/
instance fdSignedRealizationShift (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) :
    (coefficientSequenceLimit l E X).CommShift ℤ :=
  inferInstanceAs (((coefficientSequenceRestriction l E X).mapDerivedCategory ⋙
    coefficientConstantTowerLimit l E X).CommShift ℤ)

namespace FdSignedWord
open CounitRealization

/-- Evaluate a primitive by the actual PBC pullback or ordinary coefficient tensor.
Source: trace-definition whole-tower argument, Stacks 099N and 06YY
(blueprint: lem-fd-pullback-signed-shift-word-transport). -/
def pbcPrimitive {a b : Location.{u} l} (O : Primitive l a b) :
    PbcCompletedDerived a.scheme (pbcIntegralDatum l a.coefficient.carrier) ⥤
      PbcCompletedDerived b.scheme (pbcIntegralDatum l b.coefficient.carrier) :=
  match O with
  | @Primitive.pullback _ _ E X Y _hX _hY f =>
      pbcActualCompletedPull f (pbcIntegralDatum l E.carrier)
  | @Primitive.scalar _ _ E L ι X _hX =>
      pbcEmbeddingAmbientTensor l E.carrier L.carrier ι X

/-- Evaluate the same parenthesized word in the PBC presentation, before restriction.
Source: trace-definition whole-tower argument, finite-word clause
(blueprint: lem-fd-pullback-signed-shift-word-transport). -/
def pbcWord {a b : Location.{u} l} (w : Word l a b) :
    PbcCompletedDerived a.scheme (pbcIntegralDatum l a.coefficient.carrier) ⥤
      PbcCompletedDerived b.scheme (pbcIntegralDatum l b.coefficient.carrier) :=
  match w with
  | .nil _ => 𝟭 _
  | .atom O => pbcPrimitive l O
  | .comp w v => pbcWord w ⋙ pbcWord v

/-- Canonical PBC shift of a primitive. Source: Stacks 014E, 099N
(blueprint: lem-fd-pullback-signed-shift-word-transport). -/
@[instance_reducible] def pbcPrimitiveShift {a b : Location.{u} l}
    (O : Primitive l a b) : (pbcPrimitive l O).CommShift ℤ :=
  match O with
  | @Primitive.pullback _ _ E X Y _hX _hY f =>
      inferInstanceAs ((pbcActualCompletedPull f (pbcIntegralDatum l E.carrier)).CommShift ℤ)
  | @Primitive.scalar _ _ E L ι X _hX =>
      inferInstanceAs ((pbcEmbeddingAmbientTensor l E.carrier L.carrier ι X).CommShift ℤ)

/-- PBC words use precisely the existing exact-functor shifts on each letter.
Source: Stacks 014E, 099N (blueprint: lem-fd-pullback-signed-shift-word-transport). -/
@[instance_reducible] def pbcWordShift {a b : Location.{u} l}
    (w : Word l a b) : (pbcWord l w).CommShift ℤ :=
  match w with
  | .nil _ => inferInstanceAs ((𝟭 _).CommShift ℤ)
  | .atom O => pbcPrimitiveShift l O
  | .comp w v =>
      @Functor.CommShift.comp _ _ _ _ _ _ (pbcWord l w) (pbcWord l v) ℤ _ _ _ _
        (pbcWordShift w) (pbcWordShift v)

/-- Only scheme-isomorphism letters occur in the comparison assertion.
Source: trace-definition finite-word clause
(blueprint: lem-fd-pullback-signed-shift-word-transport). -/
def primitiveIso {a b : Location.{u} l} (O : Primitive l a b) : Prop :=
  match O with
  | @Primitive.pullback _ _ E X Y _hX _hY f => IsIso f
  | @Primitive.scalar _ _ E L _ι X _hX => True

/-- The node's standing scheme hypotheses, attached to an existing word location.
Source: integral stratified-perfect characterization and the trace-definition extraction
(blueprint: lem-fd-pullback-signed-shift-word-transport). -/
def geometry (a : Location.{u} l) : Prop :=
  IsNoetherian a.scheme ∧ (∃ n : ℕ, topologicalKrullDim a.scheme ≤ n) ∧
    ∀ x : a.scheme, IsUnit (l : a.scheme.presheaf.stalk x)

/-- Every scheme along the word has the standing hypotheses; scheme letters are isomorphisms.
Source: trace-definition finite-word clause
(blueprint: lem-fd-pullback-signed-shift-word-transport). -/
def geometric {a b : Location.{u} l} (w : Word l a b) : Prop :=
  match w with
  | .nil a => geometry l a
  | .atom O => geometry l a ∧ geometry l b ∧ primitiveIso l O
  | .comp w v => geometric w ∧ geometric v

/-- Restrict only to the common full integral categories at all intermediate objects.
Source: trace-definition finite-word clause; no condition on finite quotient Tor amplitude
(blueprint: lem-fd-pullback-signed-shift-word-transport). -/
def input {a b : Location.{u} l} (w : Word l a b)
    (K : DerivedCategory (scalarReductionSource l a.coefficient.carrier a.scheme)) : Prop :=
  match w with
  | .nil a => sfIntegralConstructible l a.coefficient.carrier a.scheme K
  | .atom O => sfIntegralConstructible l a.coefficient.carrier a.scheme K ∧
      sfIntegralConstructible l b.coefficient.carrier b.scheme (O.completed.obj K)
  | .comp w v => input w K ∧ input v (w.completed.obj K)

/-- The signed representative shift descends to the *given normalized ambient comparison*.
The canonical shifts on coefficient restriction and on the PBC functor are fixed above.
Source: trace-definition auxiliary step 11, Stacks 014E, 0941
(blueprint: lem-fd-pullback-signed-shift-word-transport).

Proof: finite reduction, inverse image and restriction commute with reindexing and
its signed differential. Their quotient transitions give productShift. The signed
Roos shift multiplies only the shifted coordinate by (-1)^r and fixes (0,z).
Shift an injective-term K-injective resolution: H(q) and the inclusion commute with
this sign, hence so does rho=[iota]^-1[H(q)]. Shifted good representatives remain
good. Resolving-class localization gives exactly ShiftDescent, including its retained
comparison factors. FinitePullbackStrictTowerComparison identifies the PBC shift
with reduction, levelwise pullback and the canonical Rlim shift. The defining
realization equation of N therefore gives the displayed ambient square. -/
theorem pullbackShift (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
    [Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
    (_hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (_hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (f : X ⟶ Y) [IsIso f] (rho : FdCompletedRoosNormalization l E X)
    (N : FdCompletedPullbackNormalization l E f _hX _hY rho) :
    ∃ (c : (integralOperationsPullbackComplexFunctor l E f).CommShift ℤ)
      (d : (integralDerivedPullback l E f).CommShift ℤ),
      IntegralCompletedComparison.ShiftCoordinates l E f c ∧
      IntegralCompletedComparison.ShiftDescent l E f c d ∧
      (fun [_d : (integralDerivedPullback l E f).CommShift ℤ] ↦
        NatTrans.CommShift N.comparison.hom ℤ ∧ NatTrans.CommShift N.comparison.inv ℤ)
        (_d := d) := by
  sorry

/-- Canonical shift of the PBC word preceded by coefficient identity transport.
Source: Stacks 014E, 0941 (blueprint: lem-fd-pullback-signed-shift-word-transport). -/
@[instance_reducible] def pbcInputShift {a b : Location.{u} l} (w : Word l a b) :
    (integralDetailedTransport a.scheme l a.coefficient.carrier ⋙ pbcWord l w).CommShift ℤ :=
  @Functor.CommShift.comp _ _ _ _ _ _
    (integralDetailedTransport a.scheme l a.coefficient.carrier) (pbcWord l w)
    ℤ _ _ _ _ (fdSignedTransportShift l a.coefficient.carrier a.scheme) (pbcWordShift l w)

/-- Invert precisely the counit-built comparison on its stated normalized domain.
Source: Stacks 0941, counit-realization substitution
(blueprint: lem-fd-pullback-signed-shift-word-transport). -/
def realizationIso (D : IntegralComparisonSystem.{u} l)
    (laws : WordLaws (fdCounitRealizationModels l D)) {a b : Location.{u} l}
    (w : Word l a b) (C : coefficientSequenceDerived l a.coefficient.carrier a.scheme)
    (hC : IsNormalizedCoefficientSequence l a.coefficient.carrier a.scheme C)
    (hA : w.Allowed C) :=
  letI := (laws.invertible w C hC hA).1
  asIso (w.comparison (fdCounitRealizationModels l D) C)

/-- Data and equations for the actual PBC word maps. Primitive normalization, rather
than the transport equation, specifies the maps. All quantifiers keep the existing
parenthesized word syntax and the actual entire-system counits.
Source: trace-definition auxiliary step 11; Stacks 014E, 0941, 099N
(blueprint: lem-fd-pullback-signed-shift-word-transport). -/
structure Transport (D : IntegralComparisonSystem.{u} l) where
  /-- Existing substitution and chi-conjugated scalar laws for this same realization. -/
  laws : WordLaws (fdCounitRealizationModels l D) ∧
    ScalarLaws (fdCounitRealizationModels l D)
  /-- Entire-system associativity, units, repeated fields and the mixed tower equations. -/
  mixed : IntegralQuotientMixedCoherence.{u, u} l
  /-- Signed shifts of all completed framework words, chosen simultaneously. -/
  shift : ∀ {a b : Location.{u} l} (w : Word l a b), w.completed.CommShift ℤ
  /-- Shifts of entire quotient-system words. -/
  systemShift : ∀ {a b : Location.{u} l} (w : Word l a b), w.system.CommShift ℤ
  /-- On system pullbacks use the canonical exact inverse-image shift. -/
  systemPullbackShift : ∀ (E : Coefficient.{u} l) {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (f : X ⟶ Y),
    systemShift (.atom (.pullback E f)) =
      inferInstanceAs
        ((integralComparisonSequencePullback l E.carrier f).mapDerivedCategory.CommShift ℤ)
  /-- Scalar system shifts are normalized by the actual universal cochain counit. -/
  systemScalarShift : ∀ (E L : Coefficient.{u} l) (ι : E.carrier →ₐ[ℚ_[l]] L.carrier)
    (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)]
    (P : CochainComplex (coefficientSequenceModules l E.carrier X) ℤ) (r : ℤ),
    (Functor.commShiftIso (integralComparisonDerivedSequenceScalar l E.carrier L.carrier ι X)
        (self := systemShift (.atom (.scalar E L ι X))) r).hom.app
          (DerivedCategory.Q.obj P) ≫
        ((integralComparisonSequenceScalarModel l E.carrier L.carrier ι X).ε.app P)⟦r⟧' =
      (integralComparisonDerivedSequenceScalar l E.carrier L.carrier ι X).map
          ((DerivedCategory.Q.commShiftIso r).inv.app P) ≫
        (integralComparisonSequenceScalarModel l E.carrier L.carrier ι X).ε.app (P⟦r⟧) ≫
        DerivedCategory.Q.map
          (((integralComparisonSequenceScalarModel l E.carrier L.carrier ι X).E
            |>.mapCochainComplexShiftIso r).hom.app P) ≫
        (DerivedCategory.Q.commShiftIso r).hom.app
          ((Functor.mapHomologicalComplex
            (integralComparisonSequenceScalarModel l E.carrier L.carrier ι X).E (.up ℤ)).obj P)
  /-- System word shifts use ordinary composition of the prescribed shifts. -/
  systemShiftComp : ∀ {a b c : Location.{u} l} (w : Word l a b) (v : Word l b c),
    systemShift (.comp w v) = @Functor.CommShift.comp _ _ _ _ _ _ w.system v.system
      ℤ _ _ _ _ (systemShift w) (systemShift v)
  /-- The empty system word has the canonical identity shift. -/
  systemShiftNil : ∀ a : Location.{u} l, systemShift (.nil a) = Functor.CommShift.id _
  /-- The framework pullback letter has exactly the prescribed coordinate/descent predicates. -/
  pullbackShift : ∀ (E : Coefficient.{u} l) {X Y : Scheme.{u}}
    [_hX : ∀ x : X, Invertible (l : X.residueField x)]
    [_hY : ∀ y : Y, Invertible (l : Y.residueField y)] (f : X ⟶ Y)
    (_hg : geometric l (.atom (.pullback E f))),
    ∃ c : (integralOperationsPullbackComplexFunctor l E.carrier f).CommShift ℤ,
      IntegralCompletedComparison.ShiftCoordinates l E.carrier f c ∧
      IntegralCompletedComparison.ShiftDescent l E.carrier f c (shift (.atom (.pullback E f)))
  /-- Scalar-letter shifts retain the signed cone model and the normalized chi square. -/
  scalarShift : ∀ (E L : Coefficient.{u} l) (ι : E.carrier →ₐ[ℚ_[l]] L.carrier)
    (X : Scheme.{u}) [_hX : ∀ x : X, Invertible (l : X.residueField x)],
    ∃ (c : (integralScalarComplexFunctor l E.carrier L.carrier ι X).CommShift ℤ)
      (d : (completedDerivedScalarExtension l E.carrier L.carrier ι X).CommShift ℤ),
      completedScalarShiftRepresentativeProperty ι X c d
        (shift (.atom (.scalar E L ι X)))
  /-- Composite shifts use composition, including the empty word. -/
  shiftComp : ∀ {a b c : Location.{u} l} (w : Word l a b) (v : Word l b c),
    shift (.comp w v) = @Functor.CommShift.comp _ _ _ _ _ _ w.completed v.completed
      ℤ _ _ _ _ (shift w) (shift v)
  /-- Empty-word shifts are the identity functor's canonical shifts. -/
  shiftNil : ∀ a : Location.{u} l, shift (.nil a) = Functor.CommShift.id _
  /-- The comparison b for an arbitrary finite word, on the stipulated full domain. -/
  word : ∀ {a b : Location.{u} l} (w : Word l a b) (_hg : geometric l w)
    (K : DerivedCategory (scalarReductionSource l a.coefficient.carrier a.scheme))
    (_hK : input l w K),
    (integralDetailedTransport b.scheme l b.coefficient.carrier).obj (w.completed.obj K) ≅
      (pbcWord l w).obj ((integralDetailedTransport a.scheme l a.coefficient.carrier).obj K)
  /-- Naturality on the common full integral constructible categories. -/
  naturality : ∀ {a b : Location.{u} l} (w : Word l a b) (hg : geometric l w)
    (K J : DerivedCategory (scalarReductionSource l a.coefficient.carrier a.scheme))
    (hK : input l w K) (hJ : input l w J) (f : K ⟶ J),
    (integralDetailedTransport b.scheme l b.coefficient.carrier).map (w.completed.map f) ≫
        (word w hg J hJ).hom = (word w hg K hK).hom ≫
      (pbcWord l w).map
        ((integralDetailedTransport a.scheme l a.coefficient.carrier).map f)
  /-- Empty word comparison is the fixed identity transport. -/
  nil : ∀ (a : Location.{u} l) (hg : geometric l (.nil a))
    (K : DerivedCategory (scalarReductionSource l a.coefficient.carrier a.scheme))
    (hK : input l (.nil a) K), word (.nil a) hg K hK = Iso.refl _
  /-- Iteration of b, with exactly the same parentheses as the word. -/
  comp : ∀ {a b c : Location.{u} l} (w : Word l a b) (v : Word l b c)
    (hg : geometric l (.comp w v))
    (K : DerivedCategory (scalarReductionSource l a.coefficient.carrier a.scheme))
    (hK : input l (.comp w v) K),
    word (.comp w v) hg K hK =
      word v hg.2 (w.completed.obj K) hK.2 ≪≫ (pbcWord l v).mapIso (word w hg.1 K hK.1)
  /-- Pullback letters are the specified normalized ambient comparisons, not arbitrary isos. -/
  pullback : ∀ (E : Coefficient.{u} l) {X Y : Scheme.{u}}
    [_hX : ∀ x : X, Invertible (l : X.residueField x)]
    [_hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [IsNoetherian X] [IsNoetherian Y]
    [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
    [Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
    [iX : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
    [iY : Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]
    (f : X ⟶ Y) [IsIso f],
    ∃ (rho : FdCompletedRoosNormalization l E.carrier X)
      (N : FdCompletedPullbackNormalization l E.carrier f iX.out iY.out rho),
      ∀ (hg : geometric l (.atom (.pullback E f)))
        (K : DerivedCategory (scalarReductionSource l E.carrier Y))
        (hK : input l (.atom (.pullback E f)) K),
        (word (.atom (.pullback E f)) hg K hK).hom = N.comparison.hom.app K
  /-- Scalar letters use the inverse of chi and the tensor-generator-normalized transport. -/
  scalar : ∀ (E L : Coefficient.{u} l) (ι : E.carrier →ₐ[ℚ_[l]] L.carrier)
    (X : Scheme.{u}) [_hX : ∀ x : X, Invertible (l : X.residueField x)],
    ∃ c : FdScalarCoefficientTransport l E.carrier L.carrier ι X,
      ∀ (hg : geometric l (.atom (.scalar E L ι X)))
        (K : DerivedCategory (scalarReductionSource l E.carrier X))
        (hK : input l (.atom (.scalar E L ι X)) K),
        ∃ hComplete : IsSfDerivedComplete l E.carrier X K,
          HEq (word (.atom (.scalar E L ι X)) hg K hK).hom
            ((integralDetailedTransport X l L.carrier).map
              (scalarCompletionIso l E.carrier L.carrier ι X K hComplete).inv ≫
                c.derivedIso.hom.app K)
  /-- Actual completed comparisons, indexed by specified entire-system comparisons. -/
  actual : ∀ {a b : Location.{u} l} {w v : Word l a b} (_t : Comparison w v)
    (_hw : geometric l w) (_hv : geometric l v)
    (K : DerivedCategory (scalarReductionSource l a.coefficient.carrier a.scheme))
    (_hK : input l w K) (_hK' : input l v K),
    (pbcWord l w).obj ((integralDetailedTransport a.scheme l a.coefficient.carrier).obj K) ≅
      (pbcWord l v).obj ((integralDetailedTransport a.scheme l a.coefficient.carrier).obj K)
  /-- Primitive scheme composition is the independently specified actual PBC compositor. -/
  actualPullbackComp : ∀ (E : Coefficient.{u} l) {X Y Z : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)] (f : X ⟶ Y) (g : Y ⟶ Z)
    (hw : geometric l (.atom (.pullback E (f ≫ g))))
    (hv : geometric l (.comp (.atom (.pullback E g)) (.atom (.pullback E f))))
    (K : DerivedCategory (scalarReductionSource l E.carrier Z))
    (hK : input l (.atom (.pullback E (f ≫ g))) K)
    (hK' : input l (.comp (.atom (.pullback E g)) (.atom (.pullback E f))) K),
    ∃ hI : PbcIsIntrinsicallyComplete Z (pbcIntegralDatum l E.carrier)
      ((integralDetailedTransport Z l E.carrier).obj K),
      HEq (actual (.pullbackComp E f g) hw hv K hK hK').hom
        ((pbcActualCompletedPullCompIso f g (pbcIntegralDatum l E.carrier)).inv.app ⟨_, hI⟩)
  /-- Primitive scheme identity is the actual completed-pullback identity. -/
  actualPullbackUnit : ∀ (E : Coefficient.{u} l) (X : Scheme.{u})
    [_hX : ∀ x : X, Invertible (l : X.residueField x)]
    (hw : geometric l (.atom (.pullback E (𝟙 X))))
    (hv : geometric l (.nil ⟨E, X, _hX⟩))
    (K : DerivedCategory (scalarReductionSource l E.carrier X))
    (hK : input l (.atom (.pullback E (𝟙 X))) K) (hK' : input l (.nil ⟨E, X, _hX⟩) K),
    ∃ hI : PbcIsIntrinsicallyComplete X (pbcIntegralDatum l E.carrier)
      ((integralDetailedTransport X l E.carrier).obj K),
      HEq (actual (.pullbackUnit E X) hw hv K hK hK').hom
        ((pbcActualCompletedPullIdIso (pbcIntegralDatum l E.carrier) X).hom.app ⟨_, hI⟩)
  /-- The mixed scalar letter is the actual ordinary-mate/completion PBC comparison. -/
  actualScalarPullback : ∀ (E L : Coefficient.{u} l)
    (ι : E.carrier →ₐ[ℚ_[l]] L.carrier) {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (f : X ⟶ Y)
    (hw : geometric l (.comp (.atom (.pullback E f)) (.atom (.scalar E L ι X))))
    (hv : geometric l (.comp (.atom (.scalar E L ι Y)) (.atom (.pullback L f))))
    (K : DerivedCategory (scalarReductionSource l E.carrier Y))
    (hK : input l (.comp (.atom (.pullback E f)) (.atom (.scalar E L ι X))) K)
    (hK' : input l (.comp (.atom (.scalar E L ι Y)) (.atom (.pullback L f))) K),
    HEq (actual (.scalarPullback E L ι f) hw hv K hK hK').hom
      ((pbcScalarCompletedPullIso l E.carrier L.carrier ι f).inv.app
        ((integralDetailedTransport Y l E.carrier).obj K))
  /-- The actual scalar associator is the ordinary derived tensor associator. -/
  actualScalarComp : ∀ (E L F : Coefficient.{u} l)
    (ι : E.carrier →ₐ[ℚ_[l]] L.carrier) (j : L.carrier →ₐ[ℚ_[l]] F.carrier)
    (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)]
    (hw : geometric l (.comp (.atom (.scalar E L ι X)) (.atom (.scalar L F j X))))
    (hv : geometric l (.atom (.scalar E F (j.comp ι) X)))
    (K : DerivedCategory (scalarReductionSource l E.carrier X))
    (hK : input l (.comp (.atom (.scalar E L ι X)) (.atom (.scalar L F j X))) K)
    (hK' : input l (.atom (.scalar E F (j.comp ι) X)) K),
    HEq (actual (.scalarComp E L F ι j X) hw hv K hK hK').hom
      ((pbcAmbientScalarComp l E.carrier L.carrier F.carrier ι j X).hom.app
        ((integralDetailedTransport X l E.carrier).obj K))
  /-- Equal fields use multiplication; chi inserts the completeness identification. -/
  actualScalarUnit : ∀ (E : Coefficient.{u} l) (X : Scheme.{u})
    [_hX : ∀ x : X, Invertible (l : X.residueField x)]
    (hw : geometric l (.atom (.scalar E E (AlgHom.id ℚ_[l] E.carrier) X)))
    (hv : geometric l (.nil ⟨E, X, _hX⟩))
    (K : DerivedCategory (scalarReductionSource l E.carrier X))
    (hK : input l (.atom (.scalar E E (AlgHom.id ℚ_[l] E.carrier) X)) K)
    (hK' : input l (.nil ⟨E, X, _hX⟩) K),
    HEq (actual (.scalarUnit E X) hw hv K hK hK').hom
      ((pbcEmbeddingAmbientUnit l E.carrier X).hom.app
        ((integralDetailedTransport X l E.carrier).obj K))
  /-- Entire-system normalization implies exactly the needed framework domain. -/
  domain : ∀ {a b : Location.{u} l} (w : Word l a b) (_hg : geometric l w)
    (C : coefficientSequenceDerived l a.coefficient.carrier a.scheme)
    (_hC : IsNormalizedCoefficientSequence l a.coefficient.carrier a.scheme C)
    (_hA : w.Allowed C),
    input l w ((coefficientSequenceLimit l a.coefficient.carrier a.scheme).obj C)
  /-- Counit-built r commutes with the signed framework and entire-system shifts. -/
  realizationShift : ∀ {a b : Location.{u} l} (w : Word l a b) (_hg : geometric l w)
    (C : coefficientSequenceDerived l a.coefficient.carrier a.scheme)
    (_hC : IsNormalizedCoefficientSequence l a.coefficient.carrier a.scheme C)
    (_hA : w.Allowed C) (r : ℤ),
    w.comparison (fdCounitRealizationModels l D) (C⟦r⟧) ≫
        (coefficientSequenceLimit l b.coefficient.carrier b.scheme).map
          ((Functor.commShiftIso w.system (self := systemShift w) r).hom.app C) ≫
        ((coefficientSequenceLimit l b.coefficient.carrier b.scheme).commShiftIso r).hom.app
          (w.system.obj C) =
      w.completed.map
          (((coefficientSequenceLimit l a.coefficient.carrier a.scheme).commShiftIso r).hom.app C) ≫
        (Functor.commShiftIso w.completed (self := shift w) r).hom.app
          ((coefficientSequenceLimit l a.coefficient.carrier a.scheme).obj C) ≫
        (w.comparison (fdCounitRealizationModels l D) C)⟦r⟧'
  /-- The wordwise b square uses the canonical coefficient/PBC shifts and the signed shift. -/
  wordShift : ∀ {a b : Location.{u} l} (w : Word l a b) (hg : geometric l w)
    (K : DerivedCategory (scalarReductionSource l a.coefficient.carrier a.scheme))
    (hK : input l w K) (r : ℤ), ∃ hKr : input l w (K⟦r⟧),
    (word w hg (K⟦r⟧) hKr).hom ≫
        (Functor.commShiftIso
          (integralDetailedTransport a.scheme l a.coefficient.carrier ⋙ pbcWord l w)
          (self := pbcInputShift l w) r).hom.app K =
      (integralDetailedTransport b.scheme l b.coefficient.carrier).map
          ((Functor.commShiftIso w.completed (self := shift w) r).hom.app K) ≫
        ((integralDetailedTransport b.scheme l b.coefficient.carrier).commShiftIso r).hom.app
          (w.completed.obj K) ≫ (word w hg K hK).hom⟦r⟧'
  /-- The displayed conjugation formula, intertwining the two actual presentations by b. -/
  substitution : ∀ {a b : Location.{u} l} {w v : Word l a b} (t : Comparison w v)
    (hw : geometric l w) (hv : geometric l v)
    (C : coefficientSequenceDerived l a.coefficient.carrier a.scheme)
    (hC : IsNormalizedCoefficientSequence l a.coefficient.carrier a.scheme C)
    (hA : w.Allowed C) (hA' : v.Allowed C),
    (word w hw _ (domain w hw C hC hA)).hom ≫
        (actual t hw hv _ (domain w hw C hC hA) (domain v hv C hC hA')).hom ≫
        (word v hv _ (domain v hv C hC hA')).inv =
      (integralDetailedTransport b.scheme l b.coefficient.carrier).map
        (w.comparison (fdCounitRealizationModels l D) C ≫
          (coefficientSequenceLimit l b.coefficient.carrier b.scheme).map (t.system.hom.app C) ≫
          (realizationIso l D laws.1 v C hC hA').inv)
  /-- Entire-diagram equalities hold for the actual integral operations, including inverses. -/
  coherence : ∀ {a b : Location.{u} l} {w v : Word l a b} (t s : Comparison w v)
    (hw : geometric l w) (hv : geometric l v)
    (C : coefficientSequenceDerived l a.coefficient.carrier a.scheme)
    (hC : IsNormalizedCoefficientSequence l a.coefficient.carrier a.scheme C)
    (hA : w.Allowed C) (hA' : v.Allowed C), t.system.hom = s.system.hom →
      actual t hw hv _ (domain w hw C hC hA) (domain v hv C hC hA') =
        actual s hw hv _ (domain w hw C hC hA) (domain v hv C hC hA')
  /-- Actual composites use composition of the actual comparison maps. -/
  actualComp : ∀ {a b : Location.{u} l} {w v z : Word l a b}
    (t : Comparison w v) (s : Comparison v z)
    (hw : geometric l w) (hv : geometric l v) (hz : geometric l z)
    (K : DerivedCategory (scalarReductionSource l a.coefficient.carrier a.scheme))
    (hK : input l w K) (hK' : input l v K) (hK'' : input l z K),
    actual (.compose t s) hw hz K hK hK'' =
      actual t hw hv K hK hK' ≪≫ actual s hv hz K hK' hK''
  /-- Inverse comparisons are the actual inverse isomorphisms. -/
  actualInverse : ∀ {a b : Location.{u} l} {w v : Word l a b} (t : Comparison w v)
    (hw : geometric l w) (hv : geometric l v)
    (K : DerivedCategory (scalarReductionSource l a.coefficient.carrier a.scheme))
    (hK : input l w K) (hK' : input l v K),
    actual (.inverse t) hv hw K hK' hK = (actual t hw hv K hK hK').symm
  /-- Left whiskering is application of the actual PBC operation. -/
  actualLeft : ∀ {a b c : Location.{u} l} {w v : Word l a b}
    (t : Comparison w v) (z : Word l b c)
    (hw : geometric l (.comp w z)) (hv : geometric l (.comp v z))
    (K : DerivedCategory (scalarReductionSource l a.coefficient.carrier a.scheme))
    (hK : input l (.comp w z) K) (hK' : input l (.comp v z) K),
    actual (.left t z) hw hv K hK hK' =
      (pbcWord l z).mapIso (actual t hw.1 hv.1 K hK.1 hK'.1)
  /-- Right whiskering inserts the already fixed word presentation identifications. -/
  actualRight : ∀ {a b c : Location.{u} l} (z : Word l a b) {w v : Word l b c}
    (t : Comparison w v)
    (hw : geometric l (.comp z w)) (hv : geometric l (.comp z v))
    (K : DerivedCategory (scalarReductionSource l a.coefficient.carrier a.scheme))
    (hK : input l (.comp z w) K) (hK' : input l (.comp z v) K),
    actual (.right z t) hw hv K hK hK' =
      (pbcWord l w).mapIso (word z hw.1 K hK.1).symm ≪≫
        actual t hw.2 hv.2 (z.completed.obj K) hK.2 hK'.2 ≪≫
          (pbcWord l v).mapIso (word z hv.1 K hK'.1)
  /-- Actual comparisons respect the prescribed PBC shifts, including scalar comparisons. -/
  actualShift : ∀ {a b : Location.{u} l} {w v : Word l a b} (t : Comparison w v)
    (hw : geometric l w) (hv : geometric l v)
    (K : DerivedCategory (scalarReductionSource l a.coefficient.carrier a.scheme))
    (hK : input l w K) (hK' : input l v K) (r : ℤ),
    ∃ (hKr : input l w (K⟦r⟧)) (hKr' : input l v (K⟦r⟧)),
      (actual t hw hv (K⟦r⟧) hKr hKr').hom ≫
          (Functor.commShiftIso
            (integralDetailedTransport a.scheme l a.coefficient.carrier ⋙ pbcWord l v)
            (self := pbcInputShift l v) r).hom.app K =
        (Functor.commShiftIso
            (integralDetailedTransport a.scheme l a.coefficient.carrier ⋙ pbcWord l w)
            (self := pbcInputShift l w) r).hom.app K ≫ (actual t hw hv K hK hK').hom⟦r⟧'
  /-- The actual word values belong to the common full integral category. -/
  constructible : ∀ {a b : Location.{u} l} (w : Word l a b) (_hw : geometric l w)
    (K : DerivedCategory (scalarReductionSource l a.coefficient.carrier a.scheme))
    (_hK : input l w K),
    PbcIsBoundedConstructibleComplete b.scheme (pbcIntegralDatum l b.coefficient.carrier)
      ((pbcWord l w).obj ((integralDetailedTransport a.scheme l a.coefficient.carrier).obj K))
  /-- Raw rationalization carries these same entire-diagram equalities to equalities.
  It adjoins no idempotents and also applies to the inverse comparison constructors. -/
  rationalCoherence : ∀ {a b : Location.{u} l} {w v : Word l a b} (t s : Comparison w v)
    (hw : geometric l w) (hv : geometric l v)
    (C : coefficientSequenceDerived l a.coefficient.carrier a.scheme)
    (hC : IsNormalizedCoefficientSequence l a.coefficient.carrier a.scheme C)
    (hA : w.Allowed C) (hA' : v.Allowed C), t.system.hom = s.system.hom →
      (pbcRationalization b.scheme (pbcIntegralDatum l b.coefficient.carrier)
          (pbcUniformizer l b.coefficient.carrier)).map
        (ObjectProperty.homMk
          (X := ⟨_, constructible w hw _ (domain w hw C hC hA)⟩)
          (Y := ⟨_, constructible v hv _ (domain v hv C hC hA')⟩)
          (actual t hw hv _ (domain w hw C hC hA) (domain v hv C hC hA')).hom) =
      (pbcRationalization b.scheme (pbcIntegralDatum l b.coefficient.carrier)
          (pbcUniformizer l b.coefficient.carrier)).map
        (ObjectProperty.homMk
          (X := ⟨_, constructible w hw _ (domain w hw C hC hA)⟩)
          (Y := ⟨_, constructible v hv _ (domain v hv C hC hA')⟩)
          (actual s hw hv _ (domain w hw C hC hA) (domain v hv C hC hA')).hom)

/-- The actual Roos functor on complexes of entire completed-coefficient towers.
Source: Stacks 0941 (blueprint: lem-fd-pullback-signed-shift-word-transport). -/
def towerRoos (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) :=
  HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
    (integralOperationsRoosFunctor (A := scalarReductionSource l E X))

/-- The normalized rho and every augmentation commute with the signed Roos shift.
The two projection equations specify the sign, not just an unspecified shift structure.
Naturality includes every degree-zero strict scalar map on both cone coordinates.
Source: Stacks 014E, 0941; extracted whole-tower argument steps 1--5
(blueprint: lem-fd-pullback-signed-shift-word-transport).

Proof: use exact pro-etale countable products and the canonical product shift.
The signed cocone shift is unchanged on the unshifted product and multiplies the
shifted product by (-1)^r. The differential calculation of strictRoosShiftLocalization
gives its naturality, zero/addition laws and inverse. An inclusion (0,z) has shifted
coordinate zero, so it commutes with this sign and the ordinary termwise limit shift.
For q:Q to I, shift q and its injective-term K-injective target. Naturality gives
H(q)[r] c_Q = c_I H(q[r]); the inclusion square gives the analogous equation for iota.
Substitute into rho=[iota]^-1[H(q)] and cancel. Resolution independence in
strictRoosComparison identifies this with the fixed model rho. The canonical right
derived shift is computed on the same shifted resolution. Finally strict maps are
diagonal on cone coordinates, hence commute with the sign; no component is inverted. -/
theorem roosShift (D : IntegralComparisonSystem.{u} l)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) :
    ∃ c : (towerRoos l E X).CommShift ℤ,
      (∀ (C : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E X) ℤ)
        (r q : ℤ) (n : ℕ),
        (((Functor.commShiftIso (towerRoos l E X) (self := c) r).hom.app C).f q ≫
            (CochainComplex.shiftFunctorObjXIso ((towerRoos l E X).obj C)
              r q (q + r) rfl).hom ≫
            (CochainComplex.mappingCocone.fst (scalarRoosBoundary C.asFunctor)).f (q + r) ≫
            (Pi.π (fun m : ℕ ↦ C.asFunctor.obj (op m)) n).f (q + r) =
          (CochainComplex.mappingCocone.fst
            (scalarRoosBoundary (C⟦r⟧).asFunctor)).f q ≫
            (Pi.π (fun m : ℕ ↦ (C⟦r⟧).asFunctor.obj (op m)) n).f q ≫
            ((CochainComplex.shiftFunctorObjXIso C r q (q + r) rfl).hom).app (op n)) ∧
        (((Functor.commShiftIso (towerRoos l E X) (self := c) r).hom.app C).f q ≫
            (CochainComplex.shiftFunctorObjXIso ((towerRoos l E X).obj C)
              r q (q + r) rfl).hom ≫
            (CochainComplex.mappingCocone.snd (scalarRoosBoundary C.asFunctor)).v
              (q + r) ((q - 1) + r) (by omega) ≫
            (Pi.π (fun m : ℕ ↦ C.asFunctor.obj (op m)) n).f ((q - 1) + r) =
          r.negOnePow • ((CochainComplex.mappingCocone.snd
            (scalarRoosBoundary (C⟦r⟧).asFunctor)).v q (q - 1) (by omega) ≫
            (Pi.π (fun m : ℕ ↦ (C⟦r⟧).asFunctor.obj (op m)) n).f (q - 1) ≫
            ((CochainComplex.shiftFunctorObjXIso C r (q - 1) ((q - 1) + r) rfl).hom).app
              (op n)))) ∧
      (∀ (C : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E X) ℤ) (r : ℤ),
        integralComparisonLimitToRoos l E X (C⟦r⟧) ≫
            (Functor.commShiftIso (towerRoos l E X) (self := c) r).hom.app C =
          ((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E X) ⥤
            scalarReductionSource l E X).mapCochainComplexShiftIso r).hom.app C ≫
              (integralComparisonLimitToRoos l E X C)⟦r⟧') ∧
      (∀ (C : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E X) ℤ) (r : ℤ),
        ((D.coefficient E).roos X).comparison.inv.app (C⟦r⟧) ≫
            (coefficientConstantTowerLimit l E X).map
              ((DerivedCategory.Q.commShiftIso r).hom.app C) ≫
            ((coefficientConstantTowerLimit l E X).commShiftIso r).hom.app
              (DerivedCategory.Q.obj C) =
          DerivedCategory.Q.map
              ((Functor.commShiftIso (towerRoos l E X) (self := c) r).hom.app C) ≫
            (DerivedCategory.Q.commShiftIso r).hom.app ((towerRoos l E X).obj C) ≫
            (((D.coefficient E).roos X).comparison.inv.app C)⟦r⟧') := by
  sorry

/-- Signed shifts and normalized finite-word transport exist for the fixed entire-system
models, with the actual PBC units, compositors, mixed scalar maps and tensor associators.
Source: trace-definition extracted whole-tower argument, step 11; Stacks 014E and 0941
(blueprint: lem-fd-pullback-signed-shift-word-transport).

Proof (the node's nine steps):
1. Finite inverse image, reduction and scalar restriction commute with cochain shifts.
Their quotient transitions commute as well, giving precisely productShift.
2. The strict Roos shift sends (y,x) to ((-1)^r y,x). Its differential equation,
naturality, inverse, zero and addition laws follow from the signed cocone calculation.
It fixes each (0,z), and commutes with every degree-zero diagonal strict map.
3. Shift an injective-term K-injective resolution q. Naturality of H(q) and the
zero-coordinate inclusion shows that rho=[iota]^-1[H(q)] commutes with this shift.
The normalized comparison is independent of q (strictRoosComparison).
4. Good K-flat representatives stay good after shifts. Resolving-class descent gives
ShiftCoordinates and ShiftDescent with their actual comparison factors. The finite
strict-tower comparison computes the canonical PBC shift, giving pullbackShift.
The full integral categories are closed under shifts by stratified-perfect characterization.
5. A strict scalar map acts diagonally, so commutes with the sign without inverting
any individual finite map. Scalar realization identification and normalized completion
comparison identify these maps with the actual mixed maps and chi; conjugate their squares.
6. Use the simultaneous models with the entire-system counits retained by augmentation/
counit matching. Completed compositor normalization and scalar realization identification
pin all primitive maps. Counit-realization substitution gives r_O=L(O(e))b_O and its
word recursion. Cancellation of adjacent r and r inverse gives the formula for composites,
inverses and both whiskerings, and induction gives every finite word and comparison.
7. Mixed coherence gives the whole-system equations. Conjugate by the same r to obtain
the actual integral equations, including arbitrary parentheses, scheme-map equalities,
units, repeated fields and successive extensions. ScalarLaws identifies the associator
as ordinary tensor conjugated by chi and the equal-field unit as multiplication/completeness.
8. Shift the entire counit: on its K-injective formula the ordinary limit projections
and q commute with reindexing. Its change-of-rings adjunct has degree zero. Therefore
every primitive r commutes with the signed shifts, and the recursion proves the word
square. Combine this with wordwise b and the transport formula for actualShift.
9. Raw scalar localization sends each map to its tensor with 1 and preserves composition,
inverses and equality. Apply it to the full integral comparisons to get rationalCoherence.
Multiplying each shift square by inverse comparisons gives the inverse squares. No finite
Tor-amplitude condition on quotient complexes and no flatness of quotient maps enters. -/
theorem fdPullbackSignedShiftWordTransport (D : IntegralComparisonSystem.{u} l) :
    Nonempty (Transport l D) := by
  sorry

end FdSignedWord
end WeilConjectures
