/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q97
-/
module

public import Sheaf.Paper.CompletedCoefficientAdjunctionTransportModels
public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import Sheaf.Paper.CompletedCoefficientPushforwardComparison
public import Sheaf.Paper.CompletedOperationTowerSubstitution
public import Sheaf.CategoryTheory.RingedCoefficientRestrictionCounit
public import Sheaf.CategoryTheory.ReflectorAdjunctionUnitFormulas
public import Sheaf.Paper.WeilCompletedTensorReflector
public import Sheaf.Algebra.Homology.PrincipalQuotientCompletionModel
public import Sheaf.Paper.PrincipalKoszulStrictReplacement
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-!
# Normalized monoidal and adjunction transport for completed coefficients

Source: Stacks Project, algebraization.tex, Tags 099I and 099K; main-20261015,
lem-fix-operation-reduction.proof.md, final paragraph. The combined assertion and
its representative normalizations are taken from the dispatched transport item's proof
(blueprint: def-pur-completed-coefficient-family-transport-models).

The records below present canonical constructions, including their localization,
completion-unit and sectionwise normalizations. Their existence is a conclusion;
no tensor comparison, adjunction or preservation assertion is an extra hypothesis.
Sites have object universe t+1 and morphism universe t, independently of E.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genCtorIdx false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u a v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open WeilConjectures
namespace WeilConjectures.CompletedCoefficientTransport

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Completion unit on ordinary R-pullback, viewed in the complete-subcategory diagram.
Source: Stacks 099K
(blueprint: def-pur-completed-coefficient-family-transport-models). -/
def Arrow.leftRUnit {X Y : Scheme.{t}} {SX : Site l E X} {SY : Site l E Y} {f : X ⟶ Y}
    (F : Arrow l E SX SY f) :
    (completeR l E Y).ι ⋙ F.r.left ⟶ F.leftR l E ⋙ (completeR l E X).ι where
  app H := (IntegralOnSlice.completionUnit l E X none).app (F.r.left.obj H.obj)
  naturality _H _K h :=
    (IntegralOnSlice.completionUnit l E X none).naturality (F.r.left.map h.hom)

/-- Completion unit on ordinary constant-coefficient pullback.
Source: Stacks 099K
(blueprint: def-pur-completed-coefficient-family-transport-models). -/
def Arrow.leftAUnit {X Y : Scheme.{t}} {SX : Site l E X} {SY : Site l E Y} {f : X ⟶ Y}
    (F : Arrow l E SX SY f) :
    (SY.completeA l E).ι ⋙ F.a.left ⟶ F.leftA l E ⋙ (SX.completeA l E).ι where
  app H := SX.completion.unit.app (F.a.left.obj H.obj)
  naturality _H _K h := SX.completion.unit.naturality (F.a.left.map h.hom)

/-- Tensor/pullback compatibility for the actual completed comparisons. The ordinary
pullback tensorators are fixed on representatives by PullTensor, and completion
induces the completed tensorators by the monoidality of the *actual* units.
Source: node proof step 7
(blueprint: def-pur-completed-coefficient-family-transport-models). -/
structure PullTensorTransport {X Y : Scheme.{t}} {SX : Site l E X} {SY : Site l E Y}
    (TX : TensorTransport l E SX) (TY : TensorTransport l E SY) {f : X ⟶ Y}
    (F : Arrow l E SX SY f) (A : AdjunctionTransport l E F) where
  ordinaryR : letI := F.ordinaryRAdditive; letI := F.image.completedAdditive
    PullTensor.{t, u} f (completed l E X) (completed l E Y) F.image.structureMap
    F.ordinaryR F.adjR F.r (IntegralOnSlice.duality l E X none)
      (IntegralOnSlice.duality l E Y none)
  ordinaryA : letI := F.ordinaryAAdditive
    PullTensor.{t, u} f (constant l E X) (constant l E Y)
    (CompletedCoefficientPushforward.constantStructure l E f) F.ordinaryA F.adjA F.a
      SX.closed SY.closed
  r : letI := SY.r_tensor.monoidal; letI := SX.r_tensor.monoidal
    (F.leftR l E).Monoidal
  a : letI := SY.a_tensor.monoidal; letI := SX.a_tensor.monoidal
    (F.leftA l E).Monoidal
  r_unit : letI := F.ordinaryRAdditive; letI := F.image.completedAdditive
    letI : MonoidalCategory (DR l E Y) :=
      (IntegralOnSlice.duality l E Y none).closed.monoidal
    letI : MonoidalCategory (DR l E X) :=
      (IntegralOnSlice.duality l E X none).closed.monoidal
    letI : MonoidalCategory (DerivedCategory (CompletedCoefficientPushforward.Mod Y
        (completedIntegralCoefficientSheafUnrestricted l E Y))) :=
      (IntegralOnSlice.duality l E Y none).closed.monoidal
    letI : MonoidalCategory (DerivedCategory (CompletedCoefficientPushforward.Mod X
        (completedIntegralCoefficientSheafUnrestricted l E X))) :=
      (IntegralOnSlice.duality l E X none).closed.monoidal
    letI := SY.r_tensor.monoidal; letI := SX.r_tensor.monoidal
    letI : (completeR l E Y).ι.LaxMonoidal := SY.r_tensor.inclusion.toLaxMonoidal
    letI : (completeR l E X).ι.LaxMonoidal := SX.r_tensor.inclusion.toLaxMonoidal
    letI : F.r.left.Monoidal := ordinaryR.monoidal
    letI := r
    NatTrans.IsMonoidal (F.leftRUnit l E)
  a_unit : letI := F.ordinaryAAdditive
    letI := SY.closed.closed.monoidal; letI := SX.closed.closed.monoidal
    letI := SY.a_tensor.monoidal; letI := SX.a_tensor.monoidal
    letI : (SY.completeA l E).ι.LaxMonoidal := SY.a_tensor.inclusion.toLaxMonoidal
    letI : (SX.completeA l E).ι.LaxMonoidal := SX.a_tensor.inclusion.toLaxMonoidal
    letI := ordinaryA.monoidal; letI := a
    NatTrans.IsMonoidal (F.leftAUnit l E)
  b : letI := SY.r_tensor.monoidal; letI := SX.r_tensor.monoidal
    letI := SY.a_tensor.monoidal; letI := SX.a_tensor.monoidal
    letI := TX.monoidal; letI := TY.monoidal; letI := r; letI := a
    NatTrans.IsMonoidal A.b.hom

/-- The map on actual quotient pullbacks associated to a complete-subcategory
composition constraint. The two pullback comparisons are representative-normalized.
Source: node proof step 7
(blueprint: def-pur-completed-coefficient-family-transport-models). -/
def compositionMap {X Y Z : Scheme.{t}} {SX : Site l E X} {SY : Site l E Y}
    {SZ : Site l E Z} {f : X ⟶ Y} {g : Z ⟶ X}
    (F : Arrow l E SX SY f) (G : Arrow l E SZ SX g) (GF : Arrow l E SZ SY (g ≫ f))
    (c : GF.leftR l E ≅ F.leftR l E ⋙ G.leftR l E)
    (H : (completeR l E Y).FullSubcategory) :
    (integralDerivedPullback l E (g ≫ f)).obj H.obj ⟶
      (integralDerivedPullback l E g).obj ((integralDerivedPullback l E f).obj H.obj) :=
  GF.pullback.inv.app H.obj ≫ (c.hom.app H).hom ≫
    G.pullback.hom.app ((F.leftR l E).obj H).obj ≫
      (integralDerivedPullback l E g).map (F.pullback.hom.app H.obj)

universe s i j

/-- Simultaneous normalized transport data. Composition on R is the total limit of
the canonical system composition; the displayed b square fixes the constant-side
composition. Tensor and pullback comparisons therefore iterate using precisely the
coherent system substitution comparisons, with their associators, unitors and symmetry.
All fields are conclusions of the theorem below, not assumptions about coefficients.
Source: node proof steps 1--11; Stacks 099I and 099K
(blueprint: def-pur-completed-coefficient-family-transport-models). -/
structure Transport {S : Type s} (W : S → Scheme.{t}) where
  site : ∀ a : S, Site l E (W a)
  tensor : ∀ a : S, TensorTransport l E (site a)
  tensor_unit : ∀ a : S, (tensor a).UnitNormalization l E
  arrow : ∀ {a b : S} (f : W a ⟶ W b), Arrow l E (site a) (site b) f
  pullback_normalization : ∀ {a b : S} (f : W a ⟶ W b),
    (arrow f).PullbackNormalization l E
  scalar_normalization : ∀ {a b : S} (f : W a ⟶ W b), (arrow f).TauNormalization l E
  adjunction : ∀ {a b : S} (f : W a ⟶ W b), AdjunctionTransport l E (arrow f)
  pull_tensor : ∀ {a b : S} (f : W a ⟶ W b),
    PullTensorTransport l E (tensor a) (tensor b) (arrow f) (adjunction f)
  systems : CompletedOperations.Models l E W
  system_unit : ∀ a : S,
    (IntegralOnSlice.completion l E (W a) none).obj
        (IntegralOnSlice.duality l E (W a) none).closed.monoidal.tensorUnit ≅
      (coefficientSequenceLimit l E (W a)).obj
        (CompletedOperations.unit l E (W := W) a)
  system_complete : ∀ (a : S) (N : coefficientSequenceDerived l E (W a)),
    IsNormalizedCoefficientSequence l E (W a) N →
      completeR l E (W a) ((coefficientSequenceLimit l E (W a)).obj N)
  system_comparison : CompletedOperations.ComparisonLaws.{t, u, s, i} l E systems
  substitution : CompletedOperations.SubstitutionLaw.{t, u, s, i, j} l E systems
  structural : CompletedOperations.StructuralLaw.{t, u, s, i} l E systems
  compositionR : ∀ {a b c : S} (f : W a ⟶ W b) (g : W c ⟶ W a),
    (arrow (g ≫ f)).leftR l E ≅ (arrow f).leftR l E ⋙ (arrow g).leftR l E
  compositionA : ∀ {a b c : S} (f : W a ⟶ W b) (g : W c ⟶ W a),
    (arrow (g ≫ f)).leftA l E ≅ (arrow f).leftA l E ⋙ (arrow g).leftA l E
  b_composition : ∀ {a b c : S} (f : W a ⟶ W b) (g : W c ⟶ W a)
    (H : (completeR l E (W b)).FullSubcategory),
    (adjunction (g ≫ f)).b.hom.app H ≫
        ((site c).restriction l E).map ((compositionR f g).hom.app H) =
      (compositionA f g).hom.app (((site b).restriction l E).obj H) ≫
        ((arrow g).leftA l E).map ((adjunction f).b.hom.app H) ≫
          (adjunction g).b.hom.app (((arrow f).leftR l E).obj H)
  composition_system : ∀ {a b c : S} (f : W a ⟶ W b) (g : W c ⟶ W a)
    (N : coefficientSequenceDerived l E (W b)),
    IsNormalizedCoefficientSequence l E (W b) N →
    ∀ h : completeR l E (W b) ((coefficientSequenceLimit l E (W b)).obj N),
      compositionMap l E (arrow f) (arrow g) (arrow (g ≫ f)) (compositionR f g)
          ⟨(coefficientSequenceLimit l E (W b)).obj N, h⟩ ≫
          CompletedOperations.comparison.{t, u, s, 0} l E systems
            (CompletedOperations.Expression.pullback g
              (.pullback f (.input (PUnit.unit : PUnit.{1})))) (fun _ ↦ N) =
        CompletedOperations.comparison.{t, u, s, 0} l E systems
            (CompletedOperations.Expression.pullback (g ≫ f) (.input (PUnit.unit : PUnit.{1})))
            (fun _ ↦ N) ≫
          (coefficientSequenceLimit l E (W c)).map
            (CompletedOperations.structuralValue.{t, u, s, 0} l E systems
              (CompletedOperations.StructuralMap.composition g f (.input (PUnit.unit : PUnit.{1})))
              (fun _ ↦ N)).hom


end WeilConjectures.CompletedCoefficientTransport
