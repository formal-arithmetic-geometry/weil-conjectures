module

public import Sheaf.CategoryTheory.SystemLevelLeftExtension
public import Sheaf.CategoryTheory.SystemSingletonScalarExtension
public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.CategoryTheory.StrictTowerArithmeticRestrictionDefs
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus
import Sheaf.CategoryTheory.StrictTowerArithmeticRestriction

/-! # Normalized arithmetic interpolation

Source: current Weil blueprint, sec-smooth-purity, sk-lem-sp-tower-equivalence,
Counit paragraph (blueprint: lem-sp-normalized-arithmetic-interpolation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry SheafOfModules
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- The existing strict-system and ringed-sequence presentations, with identical sections.
Source: Zheng 4.1; current blueprint Counit paragraph
(blueprint: lem-sp-normalized-arithmetic-interpolation). -/
abbrev spInterpolationSequenceEquivalence :
    StrictRingSystem.{t + 1, t, max u (t + 1)} (coefficientSequenceCommRingSystem l E W) ≌
      coefficientSequenceModules l E W :=
  strictSystemSequenceEquivalence.{t + 1, t, max u (t + 1)}
    (coefficientSequenceCommRingSystem l E W)

/-- Additivity of the sectionwise equivalence, inherited from the recorded construction.
Source: Zheng 4.1 (blueprint: lem-sp-normalized-arithmetic-interpolation). -/
instance spInterpolationSequenceAdditive :
    (spInterpolationSequenceEquivalence l E W).functor.Additive :=
  singletonSequenceFunctorAdditive (coefficientSequenceCommRingSystem l E W)

/-- Its inverse is additive by the same componentwise construction.
Source: Zheng 4.1 (blueprint: lem-sp-normalized-arithmetic-interpolation). -/
instance spInterpolationSequenceInverseAdditive :
    (spInterpolationSequenceEquivalence l E W).inverse.Additive :=
  singletonSequenceInverseAdditive (coefficientSequenceCommRingSystem l E W)

/-- Positivity makes the arithmetic subsequence strictly increasing.
Source: current blueprint Counit paragraph
(blueprint: lem-sp-normalized-arithmetic-interpolation).
Proof: multiply n+1<m+1 by positive e; both products are positive, so subtracting
one preserves their strict inequality. -/
theorem spInterpolationIndex_strictMono (e : ℕ) (he : 1 ≤ e) :
    StrictMono (fun n : ℕ ↦ e * (n + 1) - 1) := by
  sorry

/-- Arithmetic positive exponents, encoded by their predecessors.
Source: current blueprint Counit paragraph
(blueprint: lem-sp-normalized-arithmetic-interpolation). -/
def spInterpolationIndex (e : ℕ) (he : 1 ≤ e) : ℕ ↪o ℕ :=
  OrderEmbedding.ofStrictMono (fun n ↦ e * (n + 1) - 1)
    (spInterpolationIndex_strictMono e he)

/-- The actual coefficient system, retaining the existing quotient maps.
Source: Stacks 0941; current blueprint Counit paragraph
(blueprint: lem-sp-normalized-arithmetic-interpolation). -/
abbrev spInterpolationRings := coefficientSequenceCommRingSystem l E W

/-- Strict systems at selected positive exponents.
Source: Zheng 4.1 (blueprint: lem-sp-normalized-arithmetic-interpolation). -/
abbrev spInterpolationSystems (r : ℕ ↪o ℕ) :=
  StrictRingSystem.{t + 1, t, max u (t + 1)}
    (selectedSystemRings (spInterpolationRings l E W) r)

/-- Canonical termwise scalar forgetting, characterized on levels and all transitions.
The equality of evaluation functors fixes both objects and morphisms, and the last
field fixes all horizontal arrows to the original semilinear transitions.
Source: current blueprint Counit paragraph; Stacks 0941
(blueprint: lem-sp-normalized-arithmetic-interpolation). -/
structure SpInterpolationForgetting (r : ℕ ↪o ℕ) where
  ordinary : spInterpolationSystems l E W r ⥤ (ℕᵒᵖ ⥤ scalarReductionSource l E W)
  [additive : ordinary.Additive]
  [limits : PreservesFiniteLimits ordinary]
  [colimits : PreservesFiniteColimits ordinary]
  evaluation : ∀ n : ℕ,
    ordinary ⋙ (evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op n) =
      systemEvaluation.{t + 1, t, max u (t + 1)}
        (selectedSystemRings (spInterpolationRings l E W) r) n ⋙
          scalarReductionRestriction l E W (r n)
  transition : ∀ (N : spInterpolationSystems l E W r) {m n : ℕ} (h : n ≤ m)
    (V : W.ProEtᵒᵖ),
    HEq (fun x ↦ (((ordinary.obj N).map (homOfLE h).op).val.app V) x)
      (fun x ↦ ((N.transition h).val.app V) x)

attribute [instance] SpInterpolationForgetting.additive SpInterpolationForgetting.limits
  SpInterpolationForgetting.colimits

/-- Exact scalar restriction preserves kernels at each selected level.
Source: Stacks 03DA (blueprint: lem-sp-normalized-arithmetic-interpolation). -/
instance spInterpolationRestrictionLimits (n : ℕ) :
    PreservesFiniteLimits (scalarReductionRestriction l E W n) :=
  (scalarReductionRestriction_exact l E W n).1

/-- Exact scalar restriction preserves cokernels at each selected level.
Source: Stacks 03DA (blueprint: lem-sp-normalized-arithmetic-interpolation). -/
instance spInterpolationRestrictionColimits (n : ℕ) :
    PreservesFiniteColimits (scalarReductionRestriction l E W n) :=
  (scalarReductionRestriction_exact l E W n).2

/-- Derived evaluation still takes values in the recorded finite coefficient category.
Source: Zheng 4.1 (blueprint: lem-sp-normalized-arithmetic-interpolation). -/
abbrev spInterpolationEvaluation (r : ℕ ↪o ℕ) (n : ℕ) :
    DerivedCategory (spInterpolationSystems l E W r) ⥤ normalizedDVRDerived l E W (r n) :=
  derivedSystemEvaluation.{t + 1, t, max u (t + 1)}
    (selectedSystemRings (spInterpolationRings l E W) r) n

/-- The exact-localization comparison between forgetting/evaluation and scalar restriction.
Source: Stacks 015F, 0941 (blueprint: lem-sp-normalized-arithmetic-interpolation). -/
def spInterpolationForgetEvaluation (r : ℕ ↪o ℕ)
    (H : SpInterpolationForgetting l E W r) (n : ℕ) :
    H.ordinary.mapDerivedCategory ⋙ coefficientConstantTowerEvaluation l E W n ≅
      spInterpolationEvaluation l E W r n ⋙ coefficientFiniteDerivedRestriction l E W (r n) :=
  (Functor.mapDerivedCategoryCompIso H.ordinary
    ((evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op n))).symm ≪≫
    Functor.mapDerivedCategoryNatIso (eqToIso (H.evaluation n)) ≪≫
    Functor.mapDerivedCategoryCompIso
      (systemEvaluation.{t + 1, t, max u (t + 1)}
        (selectedSystemRings (spInterpolationRings l E W) r) n)
      (scalarReductionRestriction l E W (r n))

/-- Total derived inverse limit after the specified termwise scalar forgetting.
Source: Stacks 0941 (blueprint: lem-sp-normalized-arithmetic-interpolation). -/
abbrev spInterpolationLimit (r : ℕ ↪o ℕ) (H : SpInterpolationForgetting l E W r) :=
  H.ordinary.mapDerivedCategory ⋙ coefficientConstantTowerLimit l E W

/-- The canonical projection of that total limit, with exact evaluation comparison.
Source: Stacks 0941 (blueprint: lem-sp-normalized-arithmetic-interpolation). -/
def spInterpolationProjection (r : ℕ ↪o ℕ) (H : SpInterpolationForgetting l E W r)
    (n : ℕ) :
    spInterpolationLimit l E W r H ⟶ spInterpolationEvaluation l E W r n ⋙
      coefficientFiniteDerivedRestriction l E W (r n) :=
  Functor.whiskerLeft H.ordinary.mapDerivedCategory
    (coefficientConstantTowerProjection l E W n) ≫
      (spInterpolationForgetEvaluation l E W r H n).hom

/-- Normalization of the actual strict-system transitions, including all nonadjacent pairs.
Source: current blueprint Counit paragraph; Zheng 4.1
(blueprint: lem-sp-normalized-arithmetic-interpolation). -/
def SpInterpolationNormalized
    (L : SystemLevelLeftExtensionTheory.{t + 1, t, max u (t + 1)}
      (J := Scheme.ProEt.topology W)) (r : ℕ ↪o ℕ)
    (N : DerivedCategory (spInterpolationSystems l E W r)) : Prop :=
  ∀ {m n : ℕ} (h : n ≤ m),
    IsIso (((systemDerivedTensorAdj L.scalar
      (selectedSystemRings (spInterpolationRings l E W) r) h).homEquiv _ _).symm
        ((L.transition (selectedSystemRings (spInterpolationRings l E W) r) h).app N))

/-- The actual full strict-system presentation of the existing reduction calculus.
Source: Zheng 4.1; Stacks 0941
(blueprint: lem-sp-normalized-arithmetic-interpolation). -/
abbrev spInterpolationDerivedEquivalence :=
  (spInterpolationSequenceEquivalence l E W).mapDerivedCategory

/-- The evaluation comparison is uniquely determined by its identity action on sections.
Source: Zheng 4.1; Stacks 0941
(blueprint: lem-sp-normalized-arithmetic-interpolation).
Proof: both evaluations retain the same section modules. Identity linear maps commute
with restrictions by the strict system identity law. They and their inverses define
a natural isomorphism. Faithfulness of sections proves uniqueness. -/
theorem spInterpolationOrdinaryEvaluation_exists (n : ℕ) :
    ∃! ι : (spInterpolationSequenceEquivalence l E W).functor ⋙
        coefficientSequenceEvaluation l E W n ≅
      systemEvaluation.{t + 1, t, max u (t + 1)} (spInterpolationRings l E W) n,
      ∀ (M : StrictRingSystem.{t + 1, t, max u (t + 1)} (spInterpolationRings l E W))
        (V : W.ProEtᵒᵖ) (x : M.level n |>.val.obj V),
        HEq (((ι.hom.app M).val.app V) x) x := by
  sorry

/-- The uniquely specified identity-on-sections comparison.
Source: Zheng 4.1 (blueprint: lem-sp-normalized-arithmetic-interpolation). -/
def spInterpolationOrdinaryEvaluation (n : ℕ) :=
  (spInterpolationOrdinaryEvaluation_exists l E W n).exists.choose

/-- Additivity of full finite-level evaluation, from the recorded strict construction.
Source: Zheng 4.1 (blueprint: lem-sp-normalized-arithmetic-interpolation). -/
instance spInterpolationEvaluationAdditive (n : ℕ) :
    (systemEvaluation.{t + 1, t, max u (t + 1)} (spInterpolationRings l E W) n).Additive :=
  inferInstance

/-- The natural derived evaluation comparison induced by the identity on sections.
Source: Stacks 015F (blueprint: lem-sp-normalized-arithmetic-interpolation). -/
def spInterpolationFullEvaluation (n : ℕ) :
    (spInterpolationDerivedEquivalence l E W).functor ⋙
        coefficientSequenceDerivedEvaluation l E W n ≅
      derivedSystemEvaluation.{t + 1, t, max u (t + 1)} (spInterpolationRings l E W) n :=
  letI := spInterpolationEvaluationAdditive l E W n
  letI := systemEvaluationLimits.{t + 1, t, max u (t + 1)}
    (spInterpolationRings l E W) n
  letI := systemEvaluationColimits.{t + 1, t, max u (t + 1)}
    (spInterpolationRings l E W) n
  (Functor.mapDerivedCategoryCompIso (spInterpolationSequenceEquivalence l E W).functor
    (coefficientSequenceEvaluation l E W n)).symm ≪≫
      Functor.mapDerivedCategoryNatIso
        (F := (spInterpolationSequenceEquivalence l E W).functor ⋙
          coefficientSequenceEvaluation l E W n)
        (G := systemEvaluation.{t + 1, t, max u (t + 1)} (spInterpolationRings l E W) n)
        (spInterpolationOrdinaryEvaluation l E W n)

/-- Selected evaluation identified by the actual inverse unit, as a system map.
Source: Zheng 4.1; current blueprint Counit paragraph
(blueprint: lem-sp-normalized-arithmetic-interpolation). -/
def spInterpolationSelectedEvaluation
    (L : SystemLevelLeftExtensionTheory.{t + 1, t, max u (t + 1)}
      (J := Scheme.ProEt.topology W)) (e : ℕ) (he : 1 ≤ e)
    (N : DerivedCategory (spInterpolationSystems l E W (spInterpolationIndex e he)))
    (hu : IsIso ((L.selected (spInterpolationRings l E W)
      (spInterpolationIndex e he)).adjunction.unit.app N)) (n : ℕ) :
    (coefficientSequenceDerivedEvaluation l E W (spInterpolationIndex e he n)).obj
        ((spInterpolationDerivedEquivalence l E W).functor.obj
          ((L.selected (spInterpolationRings l E W) (spInterpolationIndex e he)).derived.obj N)) ≅
      (spInterpolationEvaluation l E W (spInterpolationIndex e he) n).obj N :=
  letI := hu
  (spInterpolationFullEvaluation l E W (spInterpolationIndex e he n)).app
      ((L.selected (spInterpolationRings l E W) (spInterpolationIndex e he)).derived.obj N) ≪≫
    ((L.selectedEvaluation (spInterpolationRings l E W) (spInterpolationIndex e he) n).app
      ((L.selected (spInterpolationRings l E W) (spInterpolationIndex e he)).derived.obj N)).symm ≪≫
    (spInterpolationEvaluation l E W (spInterpolationIndex e he) n).mapIso
      (asIso ((L.selected (spInterpolationRings l E W)
        (spInterpolationIndex e he)).adjunction.unit.app N)).symm

/-- The selected reduction system evaluates by the specified finite scalar extension.
Source: Stacks 0941; evaluation calculus
(blueprint: lem-sp-normalized-arithmetic-interpolation). -/
def spInterpolationReductionEvaluation
    (L : SystemLevelLeftExtensionTheory.{t + 1, t, max u (t + 1)}
      (J := Scheme.ProEt.topology W))
    (S : CoefficientDerivedSystemCalculus l E W) (e : ℕ) (he : 1 ≤ e)
    (M : DerivedCategory (scalarReductionSource l E W)) (n : ℕ) :
    (spInterpolationEvaluation l E W (spInterpolationIndex e he) n).obj
        ((derivedSystemSubsequence.{t + 1, t, max u (t + 1)}
          (spInterpolationRings l E W) (spInterpolationIndex e he)).obj
            ((spInterpolationDerivedEquivalence l E W).inverse.obj (S.reduction.obj M))) ≅
      (coefficientFiniteDerivedExtension l E W (spInterpolationIndex e he n)).obj M :=
  (L.selectedEvaluation (spInterpolationRings l E W) (spInterpolationIndex e he) n).app
      ((spInterpolationDerivedEquivalence l E W).inverse.obj (S.reduction.obj M)) ≪≫
    ((spInterpolationFullEvaluation l E W (spInterpolationIndex e he n)).app
      ((spInterpolationDerivedEquivalence l E W).inverse.obj (S.reduction.obj M))).symm ≪≫
    (coefficientSequenceDerivedEvaluation l E W (spInterpolationIndex e he n)).mapIso
      ((spInterpolationDerivedEquivalence l E W).counitIso.app (S.reduction.obj M)) ≪≫
    (S.reductionEvaluation (spInterpolationIndex e he n)).app M

/-- The reduction-to-selected-system comparison is formed from the actual counit.
Source: current blueprint Counit paragraph, reconstruction step
(blueprint: lem-sp-normalized-arithmetic-interpolation). -/
def spInterpolationCounit
    (L : SystemLevelLeftExtensionTheory.{t + 1, t, max u (t + 1)}
      (J := Scheme.ProEt.topology W))
    (S : CoefficientDerivedSystemCalculus l E W) (e : ℕ) (he : 1 ≤ e)
    (N : DerivedCategory (spInterpolationSystems l E W (spInterpolationIndex e he)))
    (M : DerivedCategory (scalarReductionSource l E W))
    (hu : IsIso ((L.selected (spInterpolationRings l E W)
      (spInterpolationIndex e he)).adjunction.unit.app N))
    (ρ : (coefficientSequenceLimit l E W).obj
        ((spInterpolationDerivedEquivalence l E W).functor.obj
          ((L.selected (spInterpolationRings l E W) (spInterpolationIndex e he)).derived.obj N)) ≅
      M) :
    (derivedSystemSubsequence.{t + 1, t, max u (t + 1)}
      (spInterpolationRings l E W) (spInterpolationIndex e he)).obj
        ((spInterpolationDerivedEquivalence l E W).inverse.obj (S.reduction.obj M)) ⟶ N :=
  letI := hu
  (derivedSystemSubsequence.{t + 1, t, max u (t + 1)}
    (spInterpolationRings l E W) (spInterpolationIndex e he)).map
    ((spInterpolationDerivedEquivalence l E W).inverse.map
      (S.reduction.map ρ.inv ≫ S.adjunction.counit.app
        ((spInterpolationDerivedEquivalence l E W).functor.obj
          ((L.selected (spInterpolationRings l E W)
            (spInterpolationIndex e he)).derived.obj N))) ≫
      (spInterpolationDerivedEquivalence l E W).unitIso.inv.app
        ((L.selected (spInterpolationRings l E W) (spInterpolationIndex e he)).derived.obj N)) ≫
    inv ((L.selected (spInterpolationRings l E W)
      (spInterpolationIndex e he)).adjunction.unit.app N)

/-- The canonical derived square obtained by localizing the ordinary scalar-forgetting
square; no comparison is selected after evaluating derived objects.
Source: Stacks 015F, 0941 (blueprint: lem-sp-normalized-arithmetic-interpolation). -/
def spInterpolationRestrictionSquare (e : ℕ) (he : 1 ≤ e)
    (H : SpInterpolationForgetting l E W (spInterpolationIndex e he))
    (ι : (spInterpolationSequenceEquivalence l E W).functor ⋙
        coefficientSequenceRestriction l E W ⋙
          StrictTowerArithmetic.restriction (scalarReductionSource l E W) e ≅
      systemSubsequence.{t + 1, t, max u (t + 1)} (spInterpolationRings l E W)
        (spInterpolationIndex e he) ⋙ H.ordinary) :
    (spInterpolationDerivedEquivalence l E W).functor ⋙
        coefficientSequenceDerivedRestriction l E W ⋙
          StrictTowerArithmetic.derivedRestriction (scalarReductionSource l E W) e ≅
      derivedSystemSubsequence.{t + 1, t, max u (t + 1)} (spInterpolationRings l E W)
        (spInterpolationIndex e he) ⋙ H.ordinary.mapDerivedCategory :=
  Functor.isoWhiskerRight
      (Functor.mapDerivedCategoryCompIso (spInterpolationSequenceEquivalence l E W).functor
        (coefficientSequenceRestriction l E W)).symm
      (StrictTowerArithmetic.derivedRestriction (scalarReductionSource l E W) e) ≪≫
    (Functor.mapDerivedCategoryCompIso
      ((spInterpolationSequenceEquivalence l E W).functor ⋙ coefficientSequenceRestriction l E W)
      (StrictTowerArithmetic.restriction (scalarReductionSource l E W) e)).symm ≪≫
    Functor.mapDerivedCategoryNatIso ι ≪≫
    Functor.mapDerivedCategoryCompIso
      (systemSubsequence.{t + 1, t, max u (t + 1)} (spInterpolationRings l E W)
        (spInterpolationIndex e he)) H.ordinary

/-- Arithmetic interpolation, with the actual maps and coherent finite counit comparisons.
All fields concern the fixed derived left extension, not an arbitrary interpolating object.
Natural number k means positive exponent k+1 throughout.
Source: current blueprint, sk-lem-sp-tower-equivalence, Counit paragraph
(blueprint: lem-sp-normalized-arithmetic-interpolation). -/
structure SpNormalizedArithmeticInterpolation
    (L : SystemLevelLeftExtensionTheory.{t + 1, t, max u (t + 1)}
      (J := Scheme.ProEt.topology W))
    (S : CoefficientDerivedSystemCalculus l E W) (e : ℕ) (he : 1 ≤ e)
    (N : DerivedCategory (spInterpolationSystems l E W (spInterpolationIndex e he))) where
  /-- The least selected positive index above k+1 is ceil((k+1)/e). -/
  ceiling : ∀ k : ℕ,
    systemNextSelected (spInterpolationIndex e he) k = k / e
  /-- The evaluation formula is the natural formula of the specified left extension. -/
  evaluation : ∀ k : ℕ,
    (derivedSystemEvaluation.{t + 1, t, max u (t + 1)} (spInterpolationRings l E W) k).obj
        ((L.selected (spInterpolationRings l E W) (spInterpolationIndex e he)).derived.obj N) ≅
      (systemDerivedTensor L.scalar (spInterpolationRings l E W)
        (systemNextSelected_spec (spInterpolationIndex e he) k).1).obj
          ((spInterpolationEvaluation l E W (spInterpolationIndex e he)
            (systemNextSelected (spInterpolationIndex e he) k)).obj N)
  /-- The chosen evaluations are the existing canonical natural identifications. -/
  evaluation_eq : ∀ k : ℕ, evaluation k =
    (L.selectedDerivedBelow (spInterpolationRings l E W) (spInterpolationIndex e he) k).app N
  /-- The actual adjacent transition is induced by the selected transition adjunct,
  with precisely the canonical associators, including repeated selected indices. -/
  adjacent : ∀ k : ℕ,
    ((systemDerivedTensorAdj L.scalar (spInterpolationRings l E W)
      (Nat.le_succ k)).homEquiv _ _).symm
      ((L.transition (spInterpolationRings l E W) (Nat.le_succ k)).app
        ((L.selected (spInterpolationRings l E W) (spInterpolationIndex e he)).derived.obj N)) =
    (systemDerivedTensor L.scalar (spInterpolationRings l E W) (Nat.le_succ k)).map
      ((L.selectedDerivedBelow (spInterpolationRings l E W)
        (spInterpolationIndex e he) (k + 1)).hom.app N) ≫
    (L.tensor.derivedAssoc (spInterpolationRings l E W) (Nat.le_succ k)
      (systemNextSelected_spec (spInterpolationIndex e he) (k + 1)).1).hom.app
      ((spInterpolationEvaluation l E W (spInterpolationIndex e he)
        (systemNextSelected (spInterpolationIndex e he) (k + 1))).obj N) ≫
    (L.tensor.derivedAssoc (spInterpolationRings l E W)
      (systemNextSelected_spec (spInterpolationIndex e he) k).1
      ((spInterpolationIndex e he).monotone
        (systemNextSelected_mono (spInterpolationIndex e he) k))).inv.app
      ((spInterpolationEvaluation l E W (spInterpolationIndex e he)
        (systemNextSelected (spInterpolationIndex e he) (k + 1))).obj N) ≫
    (systemDerivedTensor L.scalar (spInterpolationRings l E W)
      (systemNextSelected_spec (spInterpolationIndex e he) k).1).map
      (((systemDerivedTensorAdj L.scalar
        (selectedSystemRings (spInterpolationRings l E W) (spInterpolationIndex e he))
        (systemNextSelected_mono (spInterpolationIndex e he) k)).homEquiv _ _).symm
          ((L.transition
            (selectedSystemRings (spInterpolationRings l E W) (spInterpolationIndex e he))
            (systemNextSelected_mono (spInterpolationIndex e he) k)).app N)) ≫
    (L.selectedDerivedBelow (spInterpolationRings l E W)
      (spInterpolationIndex e he) k).inv.app N
  /-- The actual unit supplies UF ≅ C, hence identifies its selected transitions. -/
  unit_isIso : IsIso ((L.selected (spInterpolationRings l E W)
    (spInterpolationIndex e he)).adjunction.unit.app N)
  /-- Every transition adjoint, including composites and identities, is invertible. -/
  normalized : ∀ {m n : ℕ} (h : n ≤ m),
    IsIso (((systemDerivedTensorAdj L.scalar (spInterpolationRings l E W) h).homEquiv
      _ _).symm ((L.transition (spInterpolationRings l E W) h).app
        ((L.selected (spInterpolationRings l E W) (spInterpolationIndex e he)).derived.obj N)))
  /-- Normalization in the ringed-sequence presentation used by reconstruction. -/
  sequence_normalized : IsNormalizedCoefficientSequence l E W
    ((spInterpolationDerivedEquivalence l E W).functor.obj
      ((L.selected (spInterpolationRings l E W) (spInterpolationIndex e he)).derived.obj N))
  /-- The canonical scalar forgetting at the selected exponents. -/
  forgetting : SpInterpolationForgetting l E W (spInterpolationIndex e he)
  /-- Scalar forgetting commutes with selecting levels, by the ordinary section identity. -/
  restrictionSquare : (spInterpolationSequenceEquivalence l E W).functor ⋙
      coefficientSequenceRestriction l E W ⋙
        StrictTowerArithmetic.restriction (scalarReductionSource l E W) e ≅
    systemSubsequence.{t + 1, t, max u (t + 1)} (spInterpolationRings l E W)
      (spInterpolationIndex e he) ⋙ forgetting.ordinary
  /-- The square keeps each underlying section and hence its canonical scalar action. -/
  restrictionSquare_sections : ∀
    (P : StrictRingSystem.{t + 1, t, max u (t + 1)} (spInterpolationRings l E W))
    (n : ℕ) (V : W.ProEtᵒᵖ)
    (x : (((spInterpolationSequenceEquivalence l E W).functor ⋙
      coefficientSequenceRestriction l E W ⋙
        StrictTowerArithmetic.restriction (scalarReductionSource l E W) e).obj P).obj
          (op n) |>.val.obj V),
      HEq ((((restrictionSquare.hom.app P).app (op n)).val.app V) x) x
  /-- Canonical arithmetic comparison of total derived inverse limits. -/
  arithmetic : coefficientConstantTowerLimit l E W ≅
    StrictTowerArithmetic.derivedRestriction (scalarReductionSource l E W) e ⋙
      coefficientConstantTowerLimit l E W
  /-- On simultaneous resolutions arithmetic comparison is the actual limit restriction. -/
  arithmetic_rep : ∀
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) [I.IsKInjective]
    [CochainComplex.IsKInjective
      ((StrictTowerArithmetic.complexRestriction (scalarReductionSource l E W) e).obj I)],
    arithmetic.hom.app (DerivedCategory.Q.obj I) ≫
      (coefficientConstantTowerLimit l E W).map
        ((StrictTowerArithmetic.restriction (scalarReductionSource l E W)
          e).mapDerivedCategoryFactors.hom.app I) ≫
      ((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
        scalarReductionSource l E W).rightDerivedFunctorObjQIso
          ((StrictTowerArithmetic.complexRestriction (scalarReductionSource l E W) e).obj I)).hom =
    ((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
      scalarReductionSource l E W).rightDerivedFunctorObjQIso I).hom ≫
      DerivedCategory.Q.map (StrictTowerArithmetic.limitMap e I)
  /-- Total derived limit, with no assumption of exact sheaf products. -/
  limitIso : (coefficientSequenceLimit l E W).obj
      ((spInterpolationDerivedEquivalence l E W).functor.obj
        ((L.selected (spInterpolationRings l E W) (spInterpolationIndex e he)).derived.obj N)) ≅
    (spInterpolationLimit l E W (spInterpolationIndex e he) forgetting).obj N
  /-- The limit isomorphism is arithmetic restriction followed by total limit
  of scalar forgetting of the actual inverse arithmetic unit. -/
  limitIso_eq : limitIso.hom =
    arithmetic.hom.app ((coefficientSequenceDerivedRestriction l E W).obj
      ((spInterpolationDerivedEquivalence l E W).functor.obj
        ((L.selected (spInterpolationRings l E W) (spInterpolationIndex e he)).derived.obj N))) ≫
    (coefficientConstantTowerLimit l E W).map
      ((spInterpolationRestrictionSquare l E W e he forgetting restrictionSquare).hom.app
        ((L.selected (spInterpolationRings l E W) (spInterpolationIndex e he)).derived.obj N) ≫
        forgetting.ordinary.mapDerivedCategory.map
          (@inv _ _ _ _ ((L.selected (spInterpolationRings l E W)
            (spInterpolationIndex e he)).adjunction.unit.app N) unit_isIso))
  /-- The selected evaluation of F, identified with C by the actual inverse unit. -/
  selectedEvaluation : ∀ n : ℕ,
    (coefficientSequenceDerivedEvaluation l E W (spInterpolationIndex e he n)).obj
        ((spInterpolationDerivedEquivalence l E W).functor.obj
          ((L.selected (spInterpolationRings l E W) (spInterpolationIndex e he)).derived.obj N)) ≅
      (spInterpolationEvaluation l E W (spInterpolationIndex e he) n).obj N
  /-- This identification is fixed by the actual unit and the identity on sections. -/
  selectedEvaluation_eq : ∀ n : ℕ, selectedEvaluation n =
    spInterpolationSelectedEvaluation l E W L e he N unit_isIso n
  /-- The arithmetic limit comparison identifies the actual selected projections. -/
  projection : ∀ n : ℕ,
    limitIso.hom ≫ (spInterpolationProjection l E W (spInterpolationIndex e he)
      forgetting n).app N =
    (coefficientSequenceProjection l E W (spInterpolationIndex e he n)).app
      ((spInterpolationDerivedEquivalence l E W).functor.obj
        ((L.selected (spInterpolationRings l E W) (spInterpolationIndex e he)).derived.obj N)) ≫
      (coefficientFiniteDerivedRestriction l E W (spInterpolationIndex e he n)).map
        (selectedEvaluation n).hom
  /-- The actual counit gives a single coherent isomorphism of selected derived systems. -/
  counit_isIso : IsIso (spInterpolationCounit l E W L S e he N
    ((spInterpolationLimit l E W (spInterpolationIndex e he) forgetting).obj N) unit_isIso limitIso)
  /-- The one system counit evaluates to the actual projection adjuncts. -/
  counit_evaluation : ∀ n : ℕ,
    (spInterpolationReductionEvaluation l E W L S e he
      ((spInterpolationLimit l E W (spInterpolationIndex e he) forgetting).obj N) n).inv ≫
      (spInterpolationEvaluation l E W (spInterpolationIndex e he) n).map
        (spInterpolationCounit l E W L S e he N
          ((spInterpolationLimit l E W (spInterpolationIndex e he) forgetting).obj N)
            unit_isIso limitIso) =
    ((coefficientFiniteAdjunction l E W (spInterpolationIndex e he n)).homEquiv _ _).symm
      ((spInterpolationProjection l E W (spInterpolationIndex e he) forgetting n).app N)
  /-- Its finite comparisons are exactly the scalar adjuncts of the total-limit projections. -/
  finite_isIso : ∀ n : ℕ,
    IsIso (((coefficientFiniteAdjunction l E W (spInterpolationIndex e he n)).homEquiv
      _ _).symm ((spInterpolationProjection l E W (spInterpolationIndex e he)
        forgetting n).app N))

/-- Normalized systems on arithmetic uniformizer exponents interpolate and reconstruct.
Source: current blueprint, sk-lem-sp-tower-equivalence, Counit paragraph;
Bhatt--Scholze, Definitions 3.5.2--3.5.3 and Lemma 3.5.7, pp. 24--26
(blueprint: lem-sp-normalized-arithmetic-interpolation).

Proof:
1. Apply lem-pur-system-level-left-extension to r(n)=e(n+1)-1. Its least selected
index is k/e. The recorded natural evaluation and transition formulas give the displayed
interpolation; equal successive selected indices use the tensor unit. Evaluating the
actual adjunction unit gives the tensor identity at each selected level. Joint detection
of isomorphisms makes this unit invertible as a map of derived strict systems.
2. For any two levels, iterate the adjacent formula and its canonical tensor associators.
The resulting transition adjunct is base change of the actual selected transition
adjunct. The normalization hypothesis makes it invertible; this also covers equal
indices and every nonadjacent pair. Exact scalar forgetting retains strict composition,
so its derived tower is the coherent normalized DVR tower of def-coef-normalized-dvr-tower.
3. Apply lem-sp-strict-tower-arithmetic-restriction to the scalar-forgotten tower. Compose
its canonical arithmetic comparison with total limit of the scalar-forgotten inverse
unit. Naturality of the Roos projections in lem-weil-pbc-ringed-strict-tower-homotopy-limit
identifies the projection at e(n+1) with the projection to C_(n+1).
4. Apply lem-pur-normalized-actual-reconstruction-maps to F with the specified calculus
of lem-coef-derived-system-evaluation-calculus. Restrict its actual counit, precompose
with reduction of the inverse limit comparison, and postcompose with the inverse
arithmetic unit. These are system isomorphisms. On one K-flat representative the source
is the selected reduction system. The counit_projection identity identifies every
component with the scalar-extension adjunct of the corresponding projection. Thus these
are coherent actual counit comparisons, with no bounds or constructibility assumptions.
-/
theorem spNormalizedArithmeticInterpolation
    (_hl : IsUnit (l : Γ(W, ⊤)))
    (L : SystemLevelLeftExtensionTheory.{t + 1, t, max u (t + 1)}
      (J := Scheme.ProEt.topology W))
    (S : CoefficientDerivedSystemCalculus l E W) (e : ℕ) (he : 1 ≤ e)
    (N : DerivedCategory (spInterpolationSystems l E W (spInterpolationIndex e he)))
    (_hN : SpInterpolationNormalized l E W L (spInterpolationIndex e he) N) :
    Nonempty (SpNormalizedArithmeticInterpolation l E W L S e he N) := by
  sorry

end WeilConjectures
