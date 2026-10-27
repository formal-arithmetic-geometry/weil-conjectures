/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Sheaf.Paper.FieldExtensionTowers
public import Sheaf.Paper.QcqsCompactSupportRealization
public import Sheaf.Paper.ScalarCompletionAssociator
public import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.SixFunctors.Etale.Derived.IntegralExceptionalAdjoint
import Sheaf.CategoryTheory.CompactSupportRoosCofinality
import Sheaf.Paper.IntegralAdjunctionBijection
import Sheaf.Paper.IntegralDirectImageTower
import Sheaf.Paper.FiniteFreeCompletedScalarComparison
import Sheaf.Paper.SfScalarExtensionComposition
import Sheaf.Paper.SfRationalizationKaroubi

/-! # Completed coefficient comparison and exceptional-adjoint model transport

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-field-extension,
sole proof paragraph; the extracted DAG proof, steps 1--9
(blueprint: lem-pur-integral-coefficient-model-comparison).

The ordinary tensor functor and chi are restrictions of the published constructions.
The completed comparisons retain the specified strict-tower limits, transported to
recorded compact support by its projection-normalized realization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard
universe u a v
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace CategoryTheory

/-- The two displayed unit and counit equations, allowing a noninvertible right arrow.
Source: extracted proof steps 2--3
(blueprint: lem-pur-integral-coefficient-model-comparison). -/
def IntegralModelSquare
    {A B C D : Type a} [Category.{v} A] [Category.{v} B]
    [Category.{v} C] [Category.{v} D]
    {P : A ⥤ B} {J : B ⥤ A} {P' : C ⥤ D} {J' : D ⥤ C}
    (adj : P ⊣ J) (adj' : P' ⊣ J') (SX : A ⥤ C) (SY : B ⥤ D)
    (b : P ⋙ SY ⟶ SX ⋙ P') (c : J ⋙ SX ⟶ SY ⋙ J') : Prop :=
  (∀ M : A, SX.map (adj.unit.app M) ≫ c.app (P.obj M) ≫
    J'.map (b.app M) = adj'.unit.app (SX.obj M)) ∧
  (∀ K : B, b.app (J.obj K) ≫ P'.map (c.app K) ≫
    adj'.counit.app (SY.obj K) = SY.map (adj.counit.app K))

/-- Conjugating a comparison by chi; the component is chi inverse, b, then P(chi).
Source: extracted proof step 1
(blueprint: lem-pur-integral-coefficient-model-comparison). -/
def integralModelConjugate
    {A B C D : Type a} [Category.{v} A] [Category.{v} B]
    [Category.{v} C] [Category.{v} D]
    (P : A ⥤ B) (Q : C ⥤ D) {TX CX : A ⥤ C} {TY CY : B ⥤ D}
    (x : TX ≅ CX) (y : TY ≅ CY) (b : P ⋙ TY ≅ TX ⋙ Q) :
    P ⋙ CY ≅ CX ⋙ Q :=
  Functor.isoWhiskerLeft P y.symm ≪≫ b ≪≫ Functor.isoWhiskerRight x Q

/-- The same conjugation for a supplied right comparison, with no isomorphism assumption.
Source: extracted proof steps 3--5
(blueprint: lem-pur-integral-coefficient-model-comparison). -/
def integralModelConjugateMap
    {A B C D : Type a} [Category.{v} A] [Category.{v} B]
    [Category.{v} C] [Category.{v} D]
    (P : A ⥤ B) (Q : C ⥤ D) {TX CX : A ⥤ C} {TY CY : B ⥤ D}
    (x : TX ≅ CX) (y : TY ≅ CY) (b : P ⋙ TY ⟶ TX ⋙ Q) :
    P ⋙ CY ⟶ CX ⋙ Q :=
  Functor.whiskerLeft P y.inv ≫ b ≫ Functor.whiskerRight x.hom Q

/-- Change a right-adjoint model by the unique counit-preserving isomorphisms.
Source: extracted proof steps 4--5
(blueprint: lem-pur-integral-coefficient-model-comparison). -/
def integralModelRightTransport
    {A B C D : Type a} [Category.{v} A] [Category.{v} B]
    [Category.{v} C] [Category.{v} D]
    {P : A ⥤ B} {J G : B ⥤ A} {P' : C ⥤ D} {J' G' : D ⥤ C}
    (adj : P ⊣ J) (adjG : P ⊣ G) (adj' : P' ⊣ J') (adjG' : P' ⊣ G')
    (SX : A ⥤ C) (SY : B ⥤ D) (c : G ⋙ SX ⟶ SY ⋙ G') :
    J ⋙ SX ⟶ SY ⋙ J' :=
  Functor.whiskerRight (adj.rightAdjointUniq adjG).hom SX ≫ c ≫
    Functor.whiskerLeft SY (adj'.rightAdjointUniq adjG').inv

/-- The coefficient cocycle for maps, including comparisons that are not isomorphisms.
Source: extracted proof steps 7--8
(blueprint: lem-pur-integral-coefficient-model-comparison). -/
def IntegralModelCocycle
    {A B C A' B' C' : Type a}
    [Category.{v} A] [Category.{v} B] [Category.{v} C]
    [Category.{v} A'] [Category.{v} B'] [Category.{v} C']
    (F : A ⥤ A') (G : B ⥤ B') (H : C ⥤ C')
    (S₁ : A ⥤ B) (S₂ : B ⥤ C) (S₃ : A ⥤ C)
    (T₁ : A' ⥤ B') (T₂ : B' ⥤ C') (T₃ : A' ⥤ C')
    (s : S₁ ⋙ S₂ ≅ S₃) (t : T₁ ⋙ T₂ ≅ T₃)
    (i : F ⋙ T₁ ⟶ S₁ ⋙ G) (j : G ⋙ T₂ ⟶ S₂ ⋙ H)
    (k : F ⋙ T₃ ⟶ S₃ ⋙ H) : Prop :=
  ∀ M : A, T₂.map (i.app M) ≫ j.app (S₁.obj M) ≫ H.map (s.hom.app M) =
    t.hom.app (F.obj M) ≫ k.app M

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.IntegralCoefficientModelComparison
open FieldExtensionTowers
variable (P : PurityFiniteSetting.{u}) (D : FieldShriekSystem.Models P)
  {X Z Y : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]
  [IsSeparated (Y ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
  [(j ≫ p).IsOver (Spec (.of P.field.k))] (d : ℕ)
  [CompactSpace X] [QuasiSeparatedSpace Y]
  (R : Result P D j p d)

/-- Ordinary derived extension on the stated integral constructible category.
Source: extracted proof step 1; tower theorem clause (1)
(blueprint: lem-pur-integral-coefficient-model-comparison). -/
def tensor {E F : FieldShriekSystem.Index P} (h : E ≤ F) (W : Scheme.{u}) :
    Integral P E W ⥤ Integral P F W :=
  ObjectProperty.lift _ ((sfIntegralConstructible P.coefficients.l E.val W).ι ⋙
    completedDerivedScalarExtension P.coefficients.l E.val F.val
      (IntermediateField.inclusion h) W) (R.ordinaryClosed E F h W)

/-- The actual completion map, restricted by full-subcategory faithfulness.
Source: extracted proof step 1; finite-free completed-scalar comparison
(blueprint: lem-pur-integral-coefficient-model-comparison). -/
def chi {E F : FieldShriekSystem.Index P} (h : E ≤ F) (W : Scheme.{u}) :
    tensor P D j p d R h W ≅ scalar P h W :=
  NatIso.ofComponents
    (fun M ↦ ObjectProperty.isoMk (sfIntegralConstructible P.coefficients.l F.val W)
      (@asIso _ _ _ _
      ((completedScalarComparison P.coefficients.l E.val F.val
        (IntermediateField.inclusion h) W).app M.obj) (R.ordinaryCompleted E F h W M)))
    (fun v ↦ ObjectProperty.hom_ext (sfIntegralConstructible P.coefficients.l F.val W)
      ((completedScalarComparison P.coefficients.l E.val F.val
        (IntermediateField.inclusion h) W).naturality v.hom))

/-- The recorded compact-support functor, with the same fixed compactification.
Source: extracted proof step 1, omega transport
(blueprint: lem-pur-integral-coefficient-model-comparison). -/
def support (E : FieldShriekSystem.Index P) : Integral P E X ⥤ Integral P E Y :=
  sfCompactSupportFiniteIntegralFunctor P.coefficients.l P.field.k
    (PurCompactSupport.coefficientPrimeUnit P.coefficients.l P.field P.coefficients.different)
    (SpTowerGamma.factorization j p) E.val

/-- The projection-normalized identification of tower support with recorded support.
Source: extracted proof step 1 and canonical compact-support realization
(blueprint: lem-pur-integral-coefficient-model-comparison). -/
def omega (E : FieldShriekSystem.Index P) :
    FieldExtensionTowers.support P D j p d (R.model E) ≅ support P j p E :=
  Functor.fullyFaithfulCancelRight (sfIntegralConstructible P.coefficients.l E.val Y).ι
    (sfQcqsCompactSupportRealization P.coefficients.l E.val P.field.k
      (PurCompactSupport.coefficientPrimeUnit P.coefficients.l P.field P.coefficients.different)
      (SpTowerGamma.factorization j p))

/-- The tower adjunction transported to this same recorded compact-support functor.
Source: extracted proof step 1, eta = J(omega) eta-tower
(blueprint: lem-pur-integral-coefficient-model-comparison). -/
def adjunction (E : FieldShriekSystem.Index P) :
    support P j p E ⊣ exceptional P D j p d (R.model E) :=
  (R.model E).realization.adjunction.ofNatIsoLeft (omega P D j p d R E)

/-- The completed left comparison, retaining the actual tower-limit comparison.
Source: extracted proof step 1
(blueprint: lem-pur-integral-coefficient-model-comparison). -/
def left {E F : FieldShriekSystem.Index P} (h : E ≤ F) :
    support P j p E ⋙ scalar P h Y ≅ scalar P h X ⋙ support P j p F :=
  Functor.isoWhiskerRight (omega P D j p d R E).symm (scalar P h Y) ≪≫
    (R.integral E F h).comparison.left ≪≫
      Functor.isoWhiskerLeft (scalar P h X) (omega P D j p d R F)

/-- The completed exceptional comparison is the specified reconstructed tower limit.
Source: extracted proof step 1; LimitEquations.right fixes its actual morphism
(blueprint: lem-pur-integral-coefficient-model-comparison). -/
def right {E F : FieldShriekSystem.Index P} (h : E ≤ F) :=
  (R.integral E F h).comparison.right

/-- The ordinary tensor comparison obtained by expressing the same tower limit
in ordinary tensor coordinates, using the canonical chi at both endpoints.
Source: extracted proof step 1
(blueprint: lem-pur-integral-coefficient-model-comparison). -/
def tensorLeft {E F : FieldShriekSystem.Index P} (h : E ≤ F) :
    support P j p E ⋙ tensor P D j p d R h Y ≅
      tensor P D j p d R h X ⋙ support P j p F :=
  integralModelConjugate (support P j p E) (support P j p F)
    (chi P D j p d R h X).symm (chi P D j p d R h Y).symm (left P D j p d R h)

/-- The same ordinary-coordinate expression for the exceptional tower limit.
Source: extracted proof step 1
(blueprint: lem-pur-integral-coefficient-model-comparison). -/
def tensorRight {E F : FieldShriekSystem.Index P} (h : E ≤ F) :
    exceptional P D j p d (R.model E) ⋙ tensor P D j p d R h X ≅
      tensor P D j p d R h Y ⋙ exceptional P D j p d (R.model F) :=
  integralModelConjugate (exceptional P D j p d (R.model E))
    (exceptional P D j p d (R.model F)) (chi P D j p d R h Y).symm
    (chi P D j p d R h X).symm (right P D j p d R h)

/-- Tensor associativity on the constructible full subcategories, with its published
K-flat balanced-multiplication normalization. Source: extracted proof step 6
(blueprint: lem-pur-integral-coefficient-model-comparison). -/
def tensorAssoc
    (S : ∀ W : Scheme.{u}, ScalarCompletionAssociatorData.{u, u} P.coefficients.l W)
    {E F L : FieldShriekSystem.Index P} (h : E ≤ F) (k : F ≤ L) (W : Scheme.{u}) :
    tensor P D j p d R h W ⋙ tensor P D j p d R k W ≅
      tensor P D j p d R (h.trans k) W :=
  Functor.fullyFaithfulCancelRight (sfIntegralConstructible P.coefficients.l L.val W).ι
    (Functor.isoWhiskerLeft (sfIntegralConstructible P.coefficients.l E.val W).ι
      ((S W).ordinary E.val F.val L.val
        (IntermediateField.inclusion h) (IntermediateField.inclusion k)))

/-- Ordinary coefficient identity, fixed by multiplication on K-flat representatives.
Source: extracted proof step 9
(blueprint: lem-pur-integral-coefficient-model-comparison). -/
def tensorUnit
    (S : ∀ W : Scheme.{u}, ScalarCompletionAssociatorData.{u, u} P.coefficients.l W)
    (E : FieldShriekSystem.Index P) (W : Scheme.{u}) :
    tensor P D j p d R (le_refl E) W ≅ 𝟭 (Integral P E W) :=
  Functor.fullyFaithfulCancelRight (sfIntegralConstructible P.coefficients.l E.val W).ι
    (Functor.isoWhiskerLeft (sfIntegralConstructible P.coefficients.l E.val W).ι
      ((S W).ordinaryUnit E.val))

/-- Completed comparison for any specified right-adjoint model, including a supplied
comparison which is not assumed invertible. Source: extracted proof steps 3--5
(blueprint: lem-pur-integral-coefficient-model-comparison). -/
def alternativeRight
    (G : ∀ E : FieldShriekSystem.Index P, Integral P E Y ⥤ Integral P E X)
    (aG : ∀ E, support P j p E ⊣ G E)
    {E F : FieldShriekSystem.Index P} (h : E ≤ F)
    (c : G E ⋙ tensor P D j p d R h X ⟶ tensor P D j p d R h Y ⋙ G F) :
    exceptional P D j p d (R.model E) ⋙ scalar P h X ⟶
      scalar P h Y ⋙ exceptional P D j p d (R.model F) :=
  integralModelRightTransport (adjunction P D j p d R E) (aG E)
    (adjunction P D j p d R F) (aG F) (scalar P h X) (scalar P h Y)
    (integralModelConjugateMap (G E) (G F)
      (chi P D j p d R h Y) (chi P D j p d R h X) c)

attribute [local irreducible] tensor chi support omega adjunction left right
  tensorLeft tensorRight tensorAssoc tensorUnit alternativeRight

/-- Every assertion of the completed-coefficient and exceptional-model comparison.
The arrows are defined above, rather than existentially chosen from their reductions.
Source: latest blueprint field-extension proof; extracted DAG proof steps 1--9
(blueprint: lem-pur-integral-coefficient-model-comparison). -/
def Laws
    (S : ∀ W : Scheme.{u}, ScalarCompletionAssociatorData.{u, u} P.coefficients.l W) :
    Prop :=
  -- left_formula
  (∀ (E F : FieldShriekSystem.Index P) (h : E ≤ F),
    left P D j p d R h = integralModelConjugate (support P j p E) (support P j p F)
      (chi P D j p d R h X) (chi P D j p d R h Y) (tensorLeft P D j p d R h)) ∧
  -- right_formula
  (∀ (E F : FieldShriekSystem.Index P) (h : E ≤ F),
    right P D j p d R h = integralModelConjugate
      (exceptional P D j p d (R.model E)) (exceptional P D j p d (R.model F))
      (chi P D j p d R h Y) (chi P D j p d R h X) (tensorRight P D j p d R h)) ∧
  -- completed_square
  (∀ (E F : FieldShriekSystem.Index P) (h : E ≤ F),
    IntegralModelSquare (adjunction P D j p d R E) (adjunction P D j p d R F)
      (scalar P h X) (scalar P h Y)
      (left P D j p d R h).hom (right P D j p d R h).hom) ∧
  -- tensor_square
  (∀ (E F : FieldShriekSystem.Index P) (h : E ≤ F),
    IntegralModelSquare (adjunction P D j p d R E) (adjunction P D j p d R F)
      (tensor P D j p d R h X) (tensor P D j p d R h Y)
      (tensorLeft P D j p d R h).hom (tensorRight P D j p d R h).hom) ∧
  -- theta
  (∀ (E : FieldShriekSystem.Index P) (G : Integral P E Y ⥤ Integral P E X)
    (aG : support P j p E ⊣ G),
    (∀ K : Integral P E Y,
      (support P j p E).map
          (((adjunction P D j p d R E).rightAdjointUniq aG).hom.app K) ≫
        aG.counit.app K = (adjunction P D j p d R E).counit.app K) ∧
    (∀ M : Integral P E X, (adjunction P D j p d R E).unit.app M ≫
      ((adjunction P D j p d R E).rightAdjointUniq aG).hom.app
        ((support P j p E).obj M) = aG.unit.app M)) ∧
  -- theta_unique
  (∀ (E : FieldShriekSystem.Index P)
    (G : Integral P E Y ⥤ Integral P E X) (aG : support P j p E ⊣ G)
    (t : exceptional P D j p d (R.model E) ⟶ G),
    (∀ K : Integral P E Y, (support P j p E).map (t.app K) ≫ aG.counit.app K =
      (adjunction P D j p d R E).counit.app K) →
    t = ((adjunction P D j p d R E).rightAdjointUniq aG).hom) ∧
  -- alternative
  (∀
    (G : ∀ E : FieldShriekSystem.Index P, Integral P E Y ⥤ Integral P E X)
    (aG : ∀ E, support P j p E ⊣ G E)
    (E F : FieldShriekSystem.Index P) (h : E ≤ F)
    (c : G E ⋙ tensor P D j p d R h X ⟶ tensor P D j p d R h Y ⋙ G F),
    IntegralModelSquare (aG E) (aG F)
      (tensor P D j p d R h X) (tensor P D j p d R h Y)
      (tensorLeft P D j p d R h).hom c →
    IntegralModelSquare (adjunction P D j p d R E) (adjunction P D j p d R F)
      (scalar P h X) (scalar P h Y)
      (left P D j p d R h).hom (alternativeRight P D j p d R G aG h c)) ∧
  -- same_model
  (∀ (E F : FieldShriekSystem.Index P) (h : E ≤ F),
    integralModelRightTransport (adjunction P D j p d R E) (adjunction P D j p d R E)
      (adjunction P D j p d R F) (adjunction P D j p d R F)
      (scalar P h X) (scalar P h Y)
      (integralModelConjugateMap (exceptional P D j p d (R.model E))
        (exceptional P D j p d (R.model F))
        (chi P D j p d R h Y) (chi P D j p d R h X)
        (tensorRight P D j p d R h).hom) = (right P D j p d R h).hom) ∧
  -- associator
  (∀ (E F L : FieldShriekSystem.Index P) (h : E ≤ F) (k : F ≤ L)
    (W : Scheme.{u}) (M : Integral P E W),
    (chi P D j p d R k W).inv.app ((scalar P h W).obj M) ≫
      (tensor P D j p d R k W).map ((chi P D j p d R h W).inv.app M) ≫
      (tensorAssoc P D j p d R S h k W).hom.app M ≫
      (chi P D j p d R (h.trans k) W).hom.app M = (scalarAssoc P h k W).hom.app M) ∧
  -- rational_associator
  (∀ (E F L : FieldShriekSystem.Index P) (h : E ≤ F) (k : F ≤ L)
    (W : Scheme.{u}) (M : Rational P E W),
    HEq ((rationalScalarAssoc P h k W).hom.app M)
      ((sfRationalConstructibleLocalization P.coefficients.l L.val W).map
        ((scalarAssoc P h k W).hom.app M.obj))) ∧
  -- left_cocycle
  (∀ (E F L : FieldShriekSystem.Index P) (h : E ≤ F) (k : F ≤ L),
    IntegralModelCocycle (support P j p E) (support P j p F) (support P j p L)
      (scalar P h X) (scalar P k X) (scalar P (h.trans k) X)
      (scalar P h Y) (scalar P k Y) (scalar P (h.trans k) Y)
      (scalarAssoc P h k X) (scalarAssoc P h k Y)
      (left P D j p d R h).hom (left P D j p d R k).hom
      (left P D j p d R (h.trans k)).hom) ∧
  -- right_cocycle
  (∀ (E F L : FieldShriekSystem.Index P) (h : E ≤ F) (k : F ≤ L),
    IntegralModelCocycle
      (exceptional P D j p d (R.model E)) (exceptional P D j p d (R.model F))
      (exceptional P D j p d (R.model L))
      (scalar P h Y) (scalar P k Y) (scalar P (h.trans k) Y)
      (scalar P h X) (scalar P k X) (scalar P (h.trans k) X)
      (scalarAssoc P h k Y) (scalarAssoc P h k X)
      (right P D j p d R h).hom (right P D j p d R k).hom
      (right P D j p d R (h.trans k)).hom) ∧
  -- alternative_cocycle
  (∀
    (G : ∀ E : FieldShriekSystem.Index P, Integral P E Y ⥤ Integral P E X)
    (aG : ∀ E, support P j p E ⊣ G E)
    (c : ∀ (E F : FieldShriekSystem.Index P) (h : E ≤ F),
      G E ⋙ tensor P D j p d R h X ⟶ tensor P D j p d R h Y ⋙ G F)
    (E F L : FieldShriekSystem.Index P) (h : E ≤ F) (k : F ≤ L),
    IntegralModelCocycle (G E) (G F) (G L)
      (tensor P D j p d R h Y) (tensor P D j p d R k Y)
      (tensor P D j p d R (h.trans k) Y)
      (tensor P D j p d R h X) (tensor P D j p d R k X)
      (tensor P D j p d R (h.trans k) X)
      (tensorAssoc P D j p d R S h k Y) (tensorAssoc P D j p d R S h k X)
      (c E F h) (c F L k) (c E L (h.trans k)) →
    IntegralModelCocycle
      (exceptional P D j p d (R.model E)) (exceptional P D j p d (R.model F))
      (exceptional P D j p d (R.model L))
      (scalar P h Y) (scalar P k Y) (scalar P (h.trans k) Y)
      (scalar P h X) (scalar P k X) (scalar P (h.trans k) X)
      (scalarAssoc P h k Y) (scalarAssoc P h k X)
      (alternativeRight P D j p d R G aG h (c E F h))
      (alternativeRight P D j p d R G aG k (c F L k))
      (alternativeRight P D j p d R G aG (h.trans k) (c E L (h.trans k)))) ∧
  -- unit_formula
  (∀ (E : FieldShriekSystem.Index P) (W : Scheme.{u})
    (M : Integral P E W),
    (chi P D j p d R (le_refl E) W).inv.app M ≫
      (tensorUnit P D j p d R S E W).hom.app M =
      (sfIntegralScalarUnit P.coefficients.l E.val W P.field.p
        P.coefficients.different).hom.app M) ∧
  -- alternative_identity
  (∀
    (G : ∀ E : FieldShriekSystem.Index P, Integral P E Y ⥤ Integral P E X)
    (aG : ∀ E, support P j p E ⊣ G E) (E : FieldShriekSystem.Index P)
    (c : G E ⋙ tensor P D j p d R (le_refl E) X ⟶
      tensor P D j p d R (le_refl E) Y ⋙ G E),
    IntegralModelSquare (aG E) (aG E)
      (tensor P D j p d R (le_refl E) X) (tensor P D j p d R (le_refl E) Y)
      (tensorLeft P D j p d R (le_refl E)).hom c →
    ∀ K : Integral P E Y,
      (alternativeRight P D j p d R G aG (le_refl E) c).app K ≫
        (exceptional P D j p d (R.model E)).map
          ((sfIntegralScalarUnit P.coefficients.l E.val Y
            P.field.p P.coefficients.different).hom.app K) =
        (sfIntegralScalarUnit P.coefficients.l E.val X P.field.p
          P.coefficients.different).hom.app ((exceptional P D j p d (R.model E)).obj K)) ∧
  -- left_identity
  (∀ (E : FieldShriekSystem.Index P) (M : Integral P E X),
    (left P D j p d R (le_refl E)).hom.app M ≫
      (support P j p E).map ((sfIntegralScalarUnit P.coefficients.l E.val X
        P.field.p P.coefficients.different).hom.app M) =
      (sfIntegralScalarUnit P.coefficients.l E.val Y P.field.p
        P.coefficients.different).hom.app ((support P j p E).obj M)) ∧
  -- right_identity
  (∀ (E : FieldShriekSystem.Index P) (K : Integral P E Y),
    (right P D j p d R (le_refl E)).hom.app K ≫
      (exceptional P D j p d (R.model E)).map
        ((sfIntegralScalarUnit P.coefficients.l E.val Y
          P.field.p P.coefficients.different).hom.app K) =
      (sfIntegralScalarUnit P.coefficients.l E.val X P.field.p
        P.coefficients.different).hom.app ((exceptional P D j p d (R.model E)).obj K))

/-- Completion and counit-preserving change of exceptional models preserve the
specified adjunction comparisons, associators, cocycles and identity comparisons.
Source: latest blueprint, sk-lem-sp-field-extension, sole proof paragraph;
extracted DAG proof steps 1--9
(blueprint: lem-pur-integral-coefficient-model-comparison).

Proof:
1. Use finite-free completed scalar comparison on the derived-complete integral
   categories. Identify separately derived compact support with the recorded
   uniformizer tower using its projection-normalized realization; cofinal ell powers
   give the same comparison by lem-pur-compact-support-roos-cofinality. Transport the
   tower adjunction, unit, counit and actual comparison maps along omega. The fields
   R.limits retain their strict-tower normalizations; no finite-reduction detection of
   equality of integral maps is used.
2. Substitute the conjugation formulas. Cancel the neighboring chi inverses and
   use naturality of chi to move it across the old unit. The tensor unit equation
   reduces the result to naturality of the new unit.
3. For the counit, cancel the source chi pair and move the target chi across the
   counit. Apply the tensor counit identity and naturality of chi. The calculation
   uses no invertibility of a supplied alternative right comparison.
4. Apply det-sp-unique-right-adjoint: rightAdjointUniq is counit preserving, and
   transposing its unit composite gives the identity, hence the new unit.
5. Conjugate an alternative right comparison by these unique isomorphisms. Their
   counit equations and naturality give both J identities. For the same adjunction
   the unique isomorphism is the identity, recovering c0. This includes any specified
   constructible exceptional adjoint of prop-coef-integral-exceptional-adjoint.
6. Write z = chi2 at C1 followed by T2(chi1). The completed associator is
   chi3 alpha-t z inverse. The quotient-cocone normalization of
   lem-fix-scalar-completion-associator identifies it with scalarAssoc; localization
   is precisely sfRationalScalarComp on unchanged integral representatives.
7. Expand both b0 factors, precompose with z, and use naturality to cancel adjacent
   chi pairs. The actual tensor cocycle, supplied by det-sp-field-extension-towers,
   gives the direct comparison; cancel z. Omega conjugation cancels in the same way.
8. The identical calculation for c0 uses the tensor right cocycle. For alternative
   models the two middle theta factors cancel by naturality, leaving that cocycle.
9. For repeated fields, conjugate b-t by the multiplication unitors to an
   endomorphism beta of P. The cocycle and naturality of the unitor give
   beta at T(M) composed with b-t at M equals b-t at M. Cancel the invertible
   b-t, then use naturality across the unitor T(M) isomorphic to M to obtain
   beta at M equals the identity. The same argument applies to c-t and J.
   Substitute b0,c0 and cancel chi pairs; the completeness-unit normalization
   identifies the completed unitors with the displayed canonical ones. For a
   noninvertible supplied G comparison, its counit equation after these unitors
   says its adjunction transpose equals that of the identity of G. Injectivity
   of the adjunction Hom equivalence gives the identity comparison; transporting
   it by theta gives theta inverse composed with theta, hence the J identity.
-/
theorem integral_coefficient_model_comparison
    [SmoothOfRelativeDimension d (j ≫ p)]
    (S : ∀ W : Scheme.{u}, ScalarCompletionAssociatorData.{u, u} P.coefficients.l W) :
    Laws P D j p d R S := by
  sorry

end AlgebraicGeometry.ProEtale.IntegralCoefficientModelComparison
