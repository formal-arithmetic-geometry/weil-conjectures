/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.Paper.IntegralComparisonRealizationModels
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.QuotientSystemMixedCoherence
public import Sheaf.Paper.CompletedLineTensorCoherence
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.NormalizedDVRTower
import Sheaf.Paper.EffectiveComparisonRealizationModels
import Sheaf.Paper.NormalizedDVREffectivity
import Sheaf.Paper.IntegralDerivedOperationsOnSlices
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Paper.QuotientScalarComparisonDescent
import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
import Sheaf.TraceFormula.IntegralConeCounitRealization

/-! # Whole-counit substitution in integral realization

Source: Stacks Project, Tag 0941, lemma-derived-limit-is-ok; Bhatt--Scholze,
Definition 3.4.10, Proposition 3.5.1 and Lemma 3.5.7; blueprint main-20261015,
prop-trf-karoubi-independence, final common-stage transport sentence
(blueprint: lem-trf-counit-realization-substitution).

Words retain their parentheses, and all their maps are maps of entire derived
quotient systems. Inverses are supplied only by the asserted invertibility laws.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures.CounitRealization

/-- Bundling the finite extensions already defined by the coefficient dependency.
Source: blueprint coefficient conventions; Stacks 0941
(blueprint: lem-trf-counit-realization-substitution). -/
structure Coefficient (l : ℕ) [Fact l.Prime] where
  /-- A finite extension of the specified p-adic field. -/
  carrier : Type u
  /-- Its field structure. -/
  field : Field carrier
  /-- Its specified p-adic algebra structure. -/
  algebra : Algebra ℚ_[l] carrier
  /-- Finiteness over the p-adic field. -/
  finite : FiniteDimensional ℚ_[l] carrier

attribute [instance] Coefficient.field Coefficient.algebra Coefficient.finite

variable (l : ℕ) [Fact l.Prime]

/-- A coefficient field and an allowed scheme, used only to index composable words.
Source: the standing scheme hypothesis in Stacks 0941 and the blueprint transport
(blueprint: lem-trf-counit-realization-substitution). -/
structure Location where
  /-- The coefficient extension. -/
  coefficient : Coefficient.{u} l
  /-- The small pro-etale site's scheme. -/
  scheme : Scheme.{u}
  /-- The standing invertibility condition. -/
  invertible : ∀ x : scheme, Invertible (l : scheme.residueField x)

attribute [instance] Location.invertible

/-- The two primitive operations, with their actual source and target.
Source: Stacks 0941, 06YY, 0D6D
(blueprint: lem-trf-counit-realization-substitution). -/
inductive Primitive : Location.{u} l → Location.{u} l → Type (u + 1)
  | pullback (E : Coefficient.{u} l) {X Y : Scheme.{u}}
      [hX : ∀ x : X, Invertible (l : X.residueField x)]
      [hY : ∀ y : Y, Invertible (l : Y.residueField y)] (f : X ⟶ Y) :
      Primitive ⟨E, Y, hY⟩ ⟨E, X, hX⟩
  | scalar (E L : Coefficient.{u} l) (ι : E.carrier →ₐ[ℚ_[l]] L.carrier)
      (X : Scheme.{u}) [hX : ∀ x : X, Invertible (l : X.residueField x)] :
      Primitive ⟨E, X, hX⟩ ⟨L, X, hX⟩

/-- A finite composable word, including the empty word and arbitrary parentheses.
Source: Stacks 0941, substitution expansion
(blueprint: lem-trf-counit-realization-substitution). -/
inductive Word : Location.{u} l → Location.{u} l → Type (u + 1)
  | nil (a : Location.{u} l) : Word a a
  | atom {a b : Location.{u} l} : Primitive l a b → Word a b
  | comp {a b c : Location.{u} l} : Word a b → Word b c → Word a c

/-- The supplied normalized models, without any invertibility or coherence conclusions.
Source: Stacks 0941 and the prescribed realization-model dependency
(blueprint: lem-trf-counit-realization-substitution). -/
structure Models where
  /-- The whole-system adjunction, with its fixed reduction and realization. -/
  system : ∀ a : Location.{u} l,
    CoefficientDerivedSystemCalculus l a.coefficient.carrier a.scheme
  /-- The natural total-limit/Roos comparison with its K-injective normalization. -/
  roos : ∀ a : Location.{u} l,
    IntegralComparisonRoosModel l a.coefficient.carrier a.scheme
  /-- Each primitive pullback has its prescribed representative normalization. -/
  pullback : ∀ (E : Coefficient.{u} l) {X Y : Scheme.{u}}
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] (f : X ⟶ Y),
    IntegralComparisonPullbackModel l E.carrier f (system ⟨E, Y, hY⟩) (roos ⟨E, X, hX⟩)
  /-- Each scalar primitive has its quotient/zero-shifted-product normalization. -/
  scalar : ∀ (E L : Coefficient.{u} l) (ι : E.carrier →ₐ[ℚ_[l]] L.carrier)
    (X : Scheme.{u}) [hX : ∀ x : X, Invertible (l : X.residueField x)],
    IntegralComparisonScalarModel l E.carrier L.carrier ι X
      (system ⟨E, X, hX⟩) (roos ⟨L, X, hX⟩)

variable {l}

/-- Primitive evaluation in the category of entire derived quotient systems.
Source: Stacks 0941, 06YY (blueprint: lem-trf-counit-realization-substitution). -/
def Primitive.system {a b : Location.{u} l} (O : Primitive l a b) :
    coefficientSequenceDerived l a.coefficient.carrier a.scheme ⥤
      coefficientSequenceDerived l b.coefficient.carrier b.scheme :=
  match O with
  | @Primitive.pullback _ _ E X Y hX hY f => integralComparisonDerivedSequencePullback l E.carrier f
  | @Primitive.scalar _ _ E L ι X hX =>
      integralComparisonDerivedSequenceScalar l E.carrier L.carrier ι X

/-- Primitive evaluation by the recorded completed operations.
Source: Stacks 0941, 06YY (blueprint: lem-trf-counit-realization-substitution). -/
def Primitive.completed {a b : Location.{u} l} (O : Primitive l a b) :
    DerivedCategory (scalarReductionSource l a.coefficient.carrier a.scheme) ⥤
      DerivedCategory (scalarReductionSource l b.coefficient.carrier b.scheme) :=
  match O with
  | @Primitive.pullback _ _ E X Y hX hY f => integralDerivedPullback l E.carrier f
  | @Primitive.scalar _ _ E L ι X hX => integralScalarExtensionOfUniverses l E.carrier L.carrier ι X

/-- The prescribed primitive model isomorphism b, with no further choice.
Source: Stacks 0941 (blueprint: lem-trf-counit-realization-substitution). -/
def Primitive.model (M : Models.{u} l) {a b : Location.{u} l} (O : Primitive l a b) :
    O.completed ≅ (M.system a).reduction ⋙ O.system ⋙
      coefficientSequenceLimit l b.coefficient.carrier b.scheme :=
  match O with
  | @Primitive.pullback _ _ E X Y hX hY f => (M.pullback E f).realization
  | @Primitive.scalar _ _ E L ι X hX => (M.scalar E L ι X).realization

/-- The primitive map r is exactly b followed by L(O(e_C)).
Source: Stacks 0941 (blueprint: lem-trf-counit-realization-substitution). -/
def Primitive.comparison (M : Models.{u} l) {a b : Location.{u} l} (O : Primitive l a b)
    (C : coefficientSequenceDerived l a.coefficient.carrier a.scheme) :
    O.completed.obj ((coefficientSequenceLimit l a.coefficient.carrier a.scheme).obj C) ⟶
      (coefficientSequenceLimit l b.coefficient.carrier b.scheme).obj (O.system.obj C) :=
  (O.model M).hom.app _ ≫
    (coefficientSequenceLimit l b.coefficient.carrier b.scheme).map
      (O.system.map ((M.system a).adjunction.counit.app C))

/-- Evaluation of a parenthesized word on entire systems.
Source: Stacks 0941 (blueprint: lem-trf-counit-realization-substitution). -/
def Word.system {a b : Location.{u} l} (w : Word l a b) :
    coefficientSequenceDerived l a.coefficient.carrier a.scheme ⥤
      coefficientSequenceDerived l b.coefficient.carrier b.scheme :=
  match w with
  | .nil _ => 𝟭 _
  | .atom O => O.system
  | .comp w v => w.system ⋙ v.system

/-- The corresponding completed word with identical parentheses.
Source: Stacks 0941 (blueprint: lem-trf-counit-realization-substitution). -/
def Word.completed {a b : Location.{u} l} (w : Word l a b) :
    DerivedCategory (scalarReductionSource l a.coefficient.carrier a.scheme) ⥤
      DerivedCategory (scalarReductionSource l b.coefficient.carrier b.scheme) :=
  match w with
  | .nil _ => 𝟭 _
  | .atom O => O.completed
  | .comp w v => w.completed ⋙ v.completed

/-- Iterating precisely the primitive counit maps: r_vw = v-hat(r_w) followed by r_v.
Source: Stacks 0941, word substitution
(blueprint: lem-trf-counit-realization-substitution). -/
def Word.comparison (M : Models.{u} l) {a b : Location.{u} l} (w : Word l a b)
    (C : coefficientSequenceDerived l a.coefficient.carrier a.scheme) :
    w.completed.obj ((coefficientSequenceLimit l a.coefficient.carrier a.scheme).obj C) ⟶
      (coefficientSequenceLimit l b.coefficient.carrier b.scheme).obj (w.system.obj C) :=
  match w with
  | .nil _ => 𝟙 _
  | .atom O => O.comparison M C
  | .comp w v => v.completed.map (w.comparison M C) ≫ v.comparison M (w.system.obj C)

/-- The domain restriction requires constructible-complete intermediate realizations.
Normalization of the intermediate systems is a conclusion, not an added assumption.
Source: Stacks 0941, effective-model domain
(blueprint: lem-trf-counit-realization-substitution). -/
def Word.Allowed {a b : Location.{u} l} (w : Word l a b)
    (C : coefficientSequenceDerived l a.coefficient.carrier a.scheme) : Prop :=
  match w with
  | .nil a => sfIntegralConstructible l a.coefficient.carrier a.scheme
      ((coefficientSequenceLimit l a.coefficient.carrier a.scheme).obj C)
  | .atom O =>
      sfIntegralConstructible l a.coefficient.carrier a.scheme
          ((coefficientSequenceLimit l a.coefficient.carrier a.scheme).obj C) ∧
        sfIntegralConstructible l b.coefficient.carrier b.scheme
          ((coefficientSequenceLimit l b.coefficient.carrier b.scheme).obj (O.system.obj C))
  | .comp w v => w.Allowed C ∧ v.Allowed (w.system.obj C)

/-- Transport of an entire-system comparison by the iterated counit maps.
The explicit invertibility argument is the conclusion of the theorem below.
Source: Stacks 0941 (blueprint: lem-trf-counit-realization-substitution). -/
def Word.transport (M : Models.{u} l) {a b : Location.{u} l} (w v : Word l a b)
    (t : w.system ⟶ v.system)
    (C : coefficientSequenceDerived l a.coefficient.carrier a.scheme)
    [IsIso (v.comparison M C)] :
    w.completed.obj ((coefficientSequenceLimit l a.coefficient.carrier a.scheme).obj C) ⟶
      v.completed.obj ((coefficientSequenceLimit l a.coefficient.carrier a.scheme).obj C) :=
  w.comparison M C ≫ (coefficientSequenceLimit l b.coefficient.carrier b.scheme).map
    (t.app C) ≫ inv (v.comparison M C)


/-- All specified comparison generators, closed under inverse, composition, and both
whiskerings. The constraints are the recorded generator-normalized system maps.
Source: Stacks 0941, 06YY, 0D6D
(blueprint: lem-trf-counit-realization-substitution). -/
inductive Comparison : {a b : Location.{u} l} → Word l a b → Word l a b → Type (u + 1)
  | pullbackComp (E : Coefficient.{u} l) {X Y Z : Scheme.{u}}
      [∀ x : X, Invertible (l : X.residueField x)]
      [∀ y : Y, Invertible (l : Y.residueField y)]
      [∀ z : Z, Invertible (l : Z.residueField z)] (f : X ⟶ Y) (g : Y ⟶ Z) :
      Comparison (.atom (.pullback E (f ≫ g)))
        (.comp (.atom (.pullback E g)) (.atom (.pullback E f)))
  | pullbackUnit (E : Coefficient.{u} l) (X : Scheme.{u})
      [hX : ∀ x : X, Invertible (l : X.residueField x)] :
      Comparison (.atom (.pullback E (𝟙 X))) (.nil ⟨E, X, hX⟩)
  | scalarPullback (E L : Coefficient.{u} l) (ι : E.carrier →ₐ[ℚ_[l]] L.carrier)
      {X Y : Scheme.{u}} [∀ x : X, Invertible (l : X.residueField x)]
      [∀ y : Y, Invertible (l : Y.residueField y)] (f : X ⟶ Y) :
      Comparison (.comp (.atom (.pullback E f)) (.atom (.scalar E L ι X)))
        (.comp (.atom (.scalar E L ι Y)) (.atom (.pullback L f)))
  | scalarComp (E L F : Coefficient.{u} l)
      (ι : E.carrier →ₐ[ℚ_[l]] L.carrier) (j : L.carrier →ₐ[ℚ_[l]] F.carrier)
      (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)] :
      Comparison (.comp (.atom (.scalar E L ι X)) (.atom (.scalar L F j X)))
        (.atom (.scalar E F (j.comp ι) X))
  | scalarUnit (E : Coefficient.{u} l) (X : Scheme.{u})
      [hX : ∀ x : X, Invertible (l : X.residueField x)] :
      Comparison (.atom (.scalar E E (AlgHom.id ℚ_[l] E.carrier) X)) (.nil ⟨E, X, hX⟩)
  | associator {a b c d : Location.{u} l}
      (w : Word l a b) (v : Word l b c) (z : Word l c d) :
      Comparison (.comp (.comp w v) z) (.comp w (.comp v z))
  | unitSource {a b : Location.{u} l} (w : Word l a b) :
      Comparison (.comp (.nil a) w) w
  | unitTarget {a b : Location.{u} l} (w : Word l a b) :
      Comparison (.comp w (.nil b)) w
  | identity {a b : Location.{u} l} (w : Word l a b) : Comparison w w
  | inverse {a b : Location.{u} l} {w v : Word l a b} : Comparison w v → Comparison v w
  | compose {a b : Location.{u} l} {w v z : Word l a b} :
      Comparison w v → Comparison v z → Comparison w z
  | left {a b c : Location.{u} l} {w v : Word l a b} :
      Comparison w v → (z : Word l b c) → Comparison (.comp w z) (.comp v z)
  | right {a b c : Location.{u} l} (z : Word l a b) {w v : Word l b c} :
      Comparison w v → Comparison (.comp z w) (.comp z v)

/-- Evaluation of the named constraints as isomorphisms of whole-system functors.
Source: Stacks 0941, 06YY, 0D6D
(blueprint: lem-trf-counit-realization-substitution). -/
def Comparison.system {a b : Location.{u} l} {w v : Word l a b}
    (t : Comparison w v) : w.system ≅ v.system :=
  match t with
  | @Comparison.pullbackComp _ _ E X Y Z hX hY hZ f g =>
      integralComparisonSystemComposition l E.carrier f g
  | @Comparison.pullbackUnit _ _ E X hX => integralComparisonSystemUnit l E.carrier X
  | @Comparison.scalarPullback _ _ E L ι X Y hX hY f =>
      integralComparisonSystemScalarPullback l E.carrier L.carrier ι f
  | @Comparison.scalarComp _ _ E L F ι j X hX =>
      integralComparisonSystemScalarComposition l E.carrier L.carrier F.carrier ι j X
  | @Comparison.scalarUnit _ _ E X hX => integralComparisonSystemScalarUnit l E.carrier X
  | .associator w v z => Functor.associator w.system v.system z.system
  | .unitSource w => Functor.leftUnitor w.system
  | .unitTarget w => Functor.rightUnitor w.system
  | .identity _ => Iso.refl _
  | .inverse t => t.system.symm
  | .compose t s => t.system ≪≫ s.system
  | .left t z => Functor.isoWhiskerRight t.system z.system
  | .right z t => Functor.isoWhiskerLeft z.system t.system

/-- The coherent reduction of the recursive comparison, still an entire-system map.
Source: Stacks 0941 (blueprint: lem-trf-counit-realization-substitution). -/
def Word.reductionComparison (M : Models.{u} l) {a b : Location.{u} l} (w : Word l a b)
    (C : coefficientSequenceDerived l a.coefficient.carrier a.scheme) :=
  (M.system b).reduction.map (w.comparison M C) ≫
    (M.system b).adjunction.counit.app (w.system.obj C)

/-- Primitive whole-counit insertion at an arbitrary completed input.
Source: Stacks 0941 (blueprint: lem-trf-counit-realization-substitution). -/
def Primitive.reductionComparison (M : Models.{u} l) {a b : Location.{u} l}
    (O : Primitive l a b)
    (K : DerivedCategory (scalarReductionSource l a.coefficient.carrier a.scheme)) :=
  (M.system b).reduction.map ((O.model M).hom.app K) ≫
    (M.system b).adjunction.counit.app (O.system.obj ((M.system a).reduction.obj K))

/-- The word assertions, separated from the scalar formulas only to keep elaboration small.
Every hypothesis is the stated normalized constructible-complete domain restriction.
Source: Stacks 0941, whole-counit substitution
(blueprint: lem-trf-counit-realization-substitution). -/
structure WordLaws (M : Models.{u} l) : Prop where
  /-- Effectivity concerns the actual canonical counit in the derived system category. -/
  counit : ∀ (a : Location.{u} l)
    (C : coefficientSequenceDerived l a.coefficient.carrier a.scheme),
    IsNormalizedCoefficientSequence l a.coefficient.carrier a.scheme C →
      IsIso ((M.system a).adjunction.counit.app C)
  /-- All word maps are isomorphisms; normalization propagates to intermediate systems. -/
  invertible : ∀ {a b : Location.{u} l} (w : Word l a b)
    (C : coefficientSequenceDerived l a.coefficient.carrier a.scheme),
    IsNormalizedCoefficientSequence l a.coefficient.carrier a.scheme C → w.Allowed C →
      IsIso (w.comparison M C) ∧
        IsNormalizedCoefficientSequence l b.coefficient.carrier b.scheme (w.system.obj C)
  /-- Naturality is for arbitrary morphisms of entire derived systems. -/
  naturality : ∀ {a b : Location.{u} l} (w : Word l a b)
    (C D : coefficientSequenceDerived l a.coefficient.carrier a.scheme)
    (_hC : IsNormalizedCoefficientSequence l a.coefficient.carrier a.scheme C)
    (_hD : IsNormalizedCoefficientSequence l a.coefficient.carrier a.scheme D)
    (_hAC : w.Allowed C) (_hAD : w.Allowed D) (φ : C ⟶ D),
    w.completed.map ((coefficientSequenceLimit l a.coefficient.carrier a.scheme).map φ) ≫
        w.comparison M D = w.comparison M C ≫
      (coefficientSequenceLimit l b.coefficient.carrier b.scheme).map (w.system.map φ)
  /-- The displayed cut formula, including empty blocks. -/
  cut : ∀ {a b c : Location.{u} l} (w : Word l a b) (v : Word l b c)
    (C : coefficientSequenceDerived l a.coefficient.carrier a.scheme),
    (Word.comp w v).comparison M C =
      v.completed.map (w.comparison M C) ≫ v.comparison M (w.system.obj C)
  /-- No parentheses change the iterated whole-counit map. -/
  parenthesization : ∀ {a b c d : Location.{u} l}
    (w : Word l a b) (v : Word l b c) (z : Word l c d)
    (C : coefficientSequenceDerived l a.coefficient.carrier a.scheme),
    (Word.comp (Word.comp w v) z).comparison M C =
      (Word.comp w (Word.comp v z)).comparison M C
  /-- Inserting the entire counit before the next primitive gives the same map. -/
  wholeCounit : ∀ {a b : Location.{u} l} (O : Primitive l a b)
    (C : coefficientSequenceDerived l a.coefficient.carrier a.scheme),
    (Word.atom O).reductionComparison M C =
      O.reductionComparison M
          ((coefficientSequenceLimit l a.coefficient.carrier a.scheme).obj C) ≫
        O.system.map ((M.system a).adjunction.counit.app C)
  /-- Transport is the unique completed arrow with the prescribed realization square. -/
  comparison : ∀ {a b : Location.{u} l} {w v : Word l a b} (t : Comparison w v)
    (C : coefficientSequenceDerived l a.coefficient.carrier a.scheme)
    (_hC : IsNormalizedCoefficientSequence l a.coefficient.carrier a.scheme C)
    (_hw : w.Allowed C) (_hv : v.Allowed C),
    ∃! q : w.completed.obj
        ((coefficientSequenceLimit l a.coefficient.carrier a.scheme).obj C) ≅
        v.completed.obj ((coefficientSequenceLimit l a.coefficient.carrier a.scheme).obj C),
      q.hom ≫ v.comparison M C = w.comparison M C ≫
        (coefficientSequenceLimit l b.coefficient.carrier b.scheme).map (t.system.hom.app C)
  /-- Composing comparisons cancels the middle word identification. -/
  composition : ∀ {a b : Location.{u} l} (w v z : Word l a b)
    (t : Comparison w v) (s : Comparison v z)
    (C : coefficientSequenceDerived l a.coefficient.carrier a.scheme)
    [IsIso (v.comparison M C)] [IsIso (z.comparison M C)],
    w.transport M v t.system.hom C ≫ v.transport M z s.system.hom C =
      w.transport M z (t.system.hom ≫ s.system.hom) C
  /-- Inverting a comparison gives the inverse completed arrow. -/
  inverse : ∀ {a b : Location.{u} l} (w v : Word l a b) (t : Comparison w v)
    (C : coefficientSequenceDerived l a.coefficient.carrier a.scheme)
    [IsIso (w.comparison M C)] [IsIso (v.comparison M C)],
    w.transport M v t.system.hom C ≫ v.transport M w t.system.inv C = 𝟙 _
  /-- The formula persists after every further completed operation on the left. -/
  leftWhisker : ∀ {a b c : Location.{u} l} (w v : Word l a b)
    (t : Comparison w v) (z : Word l b c)
    (C : coefficientSequenceDerived l a.coefficient.carrier a.scheme)
    [IsIso (v.comparison M C)] [IsIso ((Word.comp v z).comparison M C)],
    (Word.comp w z).transport M (Word.comp v z) (t.left z).system.hom C =
      z.completed.map (w.transport M v t.system.hom C)
  /-- Right whiskering uses the canonical comparison for the inserted input word. -/
  rightWhisker : ∀ {a b c : Location.{u} l} (z : Word l a b) (w v : Word l b c)
    (t : Comparison w v)
    (C : coefficientSequenceDerived l a.coefficient.carrier a.scheme)
    [IsIso (v.comparison M (z.system.obj C))]
    [IsIso ((Word.comp z v).comparison M C)],
    (Word.comp z w).transport M (Word.comp z v) (t.right z).system.hom C ≫
        v.completed.map (z.comparison M C) =
      w.completed.map (z.comparison M C) ≫
        w.transport M v t.system.hom (z.system.obj C)


/-- The scalar letter, using the already defined whole-system and completed scalar changes.
Source: Stacks 06YY (blueprint: lem-trf-counit-realization-substitution). -/
def scalarWord (E L : Coefficient.{u} l) (ι : E.carrier →ₐ[ℚ_[l]] L.carrier)
    (X : Scheme.{u}) [hX : ∀ x : X, Invertible (l : X.residueField x)] :
    Word l ⟨E, X, hX⟩ ⟨L, X, hX⟩ := .atom (.scalar E L ι X)

/-- Scalar normalization means the realized system associator is the ordinary tensor
associator conjugated by the actual quotient-normalized completion maps chi.
The published associator and unit definitions expand to exactly that formula.
Source: Bhatt--Scholze, Definition 3.4.10, Proposition 3.5.1 and Lemma 3.5.7
(blueprint: lem-trf-counit-realization-substitution). -/
structure ScalarLaws (M : Models.{u} l) : Prop where
  /-- The entire-system associator is the chi-conjugated ordinary derived associator. -/
  associator : ∀ (E L F : Coefficient.{u} l)
    (ι : E.carrier →ₐ[ℚ_[l]] L.carrier) (j : L.carrier →ₐ[ℚ_[l]] F.carrier)
    (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)]
    (C : coefficientSequenceDerived l E.carrier X)
    (_hN : IsNormalizedCoefficientSequence l E.carrier X C)
    (hC : sfIntegralConstructible l E.carrier X
      ((coefficientSequenceLimit l E.carrier X).obj C))
    (_hA : (Word.comp (scalarWord E L ι X) (scalarWord L F j X)).Allowed C)
    (_hDirect : (scalarWord E F (j.comp ι) X).Allowed C),
    (Word.comp (scalarWord E L ι X) (scalarWord L F j X)).comparison M C ≫
        (coefficientSequenceLimit l F.carrier X).map
          ((integralComparisonSystemScalarComposition l E.carrier L.carrier F.carrier
            ι j X).hom.app C) =
      (CompletedLineTensor.associator l E.carrier X L.carrier ι F.carrier j
        ((coefficientSequenceLimit l E.carrier X).obj C)
        (CompletedLineTensor.intrinsic_complete l E.carrier X ⟨_, hC⟩)).hom ≫
          (scalarWord E F (j.comp ι) X).comparison M C
  /-- Identity scalar change realizes to multiplication and completeness, including E=L. -/
  unit : ∀ (E : Coefficient.{u} l) (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)]
    (C : coefficientSequenceDerived l E.carrier X)
    (_hN : IsNormalizedCoefficientSequence l E.carrier X C)
    (hC : sfIntegralConstructible l E.carrier X
      ((coefficientSequenceLimit l E.carrier X).obj C))
    (_hA : (scalarWord E E (AlgHom.id ℚ_[l] E.carrier) X).Allowed C),
    (scalarWord E E (AlgHom.id ℚ_[l] E.carrier) X).comparison M C ≫
        (coefficientSequenceLimit l E.carrier X).map
          ((integralComparisonSystemScalarUnit l E.carrier X).hom.app C) =
      (CompletedLineTensor.unit l E.carrier X
        ((coefficientSequenceLimit l E.carrier X).obj C)
        (CompletedLineTensor.intrinsic_complete l E.carrier X ⟨_, hC⟩)).hom

/-- Whole-counit substitution and scalar normalization for realized operations.
Source: Stacks 0941, lemma-derived-limit-is-ok; Bhatt--Scholze, Definition 3.4.10,
Proposition 3.5.1 and Lemma 3.5.7; blueprint main-20261015,
prop-trf-karoubi-independence, final common-stage transport sentence
(blueprint: lem-trf-counit-realization-substitution).

Proof plan, following the eleven steps of the DAG node:
1. coefficientDerivedSystemEvaluationCalculus supplies the actual adjunction counit.
NormalizedDVREffectivity identifies its evaluations with coherent canonical
isomorphisms. Joint conservativity makes the entire counit invertible, without bounds.
integralComparisonReductionCounit_formula identifies it with coefficient change of
the K-injective-normalized ordinary-limit-cone counit.
2. A primitive comparison is its prescribed model followed by L(O(e_C)), hence is
invertible. effectiveComparisonRealizationModels makes O(R(K)) normalized on the
constructible-complete domain. Transport normalization along O(e_C); iterate.
3. Apply naturality of the primitive model and of the whole-system counit to an
arbitrary derived-system morphism. This proves primitive comparison naturality,
including inverse arrows, before any separate finite evaluation.
4. Induct on finite words. The empty comparison is identity. Composition is the
stated cut formula. Expanding three consecutive blocks proves parenthesization
independence by associativity and functoriality; repeat for every cut.
5. For two letters move the first model past the image of the second counit by
naturality. Counit naturality then identifies insertion at the intermediate object
with substitution before the next primitive. The triangle identities cancel an
inserted unit. This gives the coherent reductionComparison equation.
6. For each named entire-system comparison, conjugate its realization by the two
word comparisons. Invertibility gives uniqueness. Composition cancels the middle
comparison and its inverse; inversion reverses all factors.
7. Naturality applied to t_C gives left whiskering; evaluating at zC and using the
word cut formula gives right whiskering. Induct to arbitrary further words.
8. For scalar normalization use finiteFreeCompletedScalarComparison: chi and the
ordinary scalar extensions preserve completeness. Resolve K by a flat-term K-flat
complex using lem-pc-kflat-resolution. lem-pur-kflat-change-of-rings computes both
successive extensions. lem-pur-quotient-scalar-comparison-descent fixes the quotient
coordinates of chi and its zero shifted-product component on every representative.
9. integralConeCounitRealization turns these quotient lifts into the original
compatible strict families under the adjunction counit. Both scalar associativity
routes on ((x tensor a) tensor b) tensor c give x tensor (a-bar b-bar c).
Balancing extends this to all tensors; quotient maps and restrictions preserve
multiplication, and degree-zero scalars commute with the differential.
10. Localize that strict equality retaining the normalized cochain comparisons.
The adjunction Hom bijection identifies the entire-system adjuncts. Naturality
transports the equation through e_C. Inverting the two chi factors gives exactly
CompletedLineTensor.associator, whose definition is the displayed chi conjugation.
11. At identity coefficients the same computation is multiplication s tensor x to sx.
The identity normalization of chi identifies it with the completeness unit after
ordinary multiplication, giving exactly CompletedLineTensor.unit. This includes
all equalities among the coefficient fields. No faithfulness of separate finite
reductions, finite Tor-amplitude, or additional boundedness is used. -/
theorem counitRealizationSubstitution (l : ℕ) [Fact l.Prime] (M : Models.{u} l) :
    WordLaws M ∧ ScalarLaws M := by
  sorry

end WeilConjectures.CounitRealization
