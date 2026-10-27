/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q64
-/
module

public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.SfDerivedDirectImage
public import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
public import Sheaf.Paper.SfIntegralReductionTower
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Sheaf.AlgebraicGeometry.SfFiniteExceptionalInverseImage
public import Sheaf.Paper.FiniteTorAmplitudeProEtaleModule
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison
public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.SfWeilSheafComplex
public import Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.KrullDimension
public import Sheaf.AlgebraicGeometry.FiniteOpenClosedRecollement

/-! # Data for supported localization at every coefficient stage

Source: Weil blueprint, sec-smooth-purity/sk-prop-sf-localization,
proposition prop-sf-localization-all-stages
(blueprint: prop-sf-localization-all-stages).

The records below only package the clauses of the proposition. They do not assume
existence of any of its adjoints or connecting arrows.

The records and the integral inverse-limit formula are shared by the separate
coefficient-stage construction lemmas.
(blueprint: def-sf-localization-stage-data).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option genInjectivity false
set_option genSizeOfSpec false

universe u v c h a b

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- The supported triangle with its prescribed adjunction maps, in an ambient
triangulated category. The category C can be a full constructible subcategory;
its inclusion V records where distinguishedness and shifts are tested.
Source: blueprint supported localization, clauses (2)--(4)
(blueprint: prop-sf-localization-all-stages). -/
structure SfSupportedLocalization
    {C Z U : Type c} [Category.{h} C] [Category.{h} Z] [Category.{h} U]
    {A : Type a} [Category.{b} A] [Preadditive A] [HasZeroObject A]
    [HasShift A ℤ] [∀ n : ℤ, (shiftFunctor A n).Additive] [Pretriangulated A]
    {B D : Type a} [Category.{b} B] [Category.{b} D]
    [HasZeroMorphisms B]
    (V : C ⥤ A) (W : Z ⥤ B) (_T : U ⥤ D) where
  iPull : C ⥤ Z
  jPull : C ⥤ U
  iPush : Z ⥤ C
  jPush : U ⥤ C
  exceptional : C ⥤ Z
  closedAdjunction : iPull ⊣ iPush
  openAdjunction : jPull ⊣ jPush
  exceptionalAdjunction : iPush ⊣ exceptional
  boundary : jPull ⋙ jPush ⋙ V ⟶ exceptional ⋙ iPush ⋙ V ⋙ shiftFunctor A (1 : ℤ)
  distinguished (K : C) :
    Triangle.mk (V.map (exceptionalAdjunction.counit.app K))
      (V.map (openAdjunction.unit.app K)) (boundary.app K) ∈ distTriang A
  unique_boundary (K : C)
      (δ : V.obj (jPush.obj (jPull.obj K)) ⟶
        (V.obj (iPush.obj (exceptional.obj K)))⟦(1 : ℤ)⟧) :
    Triangle.mk (V.map (exceptionalAdjunction.counit.app K))
      (V.map (openAdjunction.unit.app K)) δ ∈ distTriang A → δ = boundary.app K
  orthogonal (K : C) (m : ℤ) :
    Subsingleton ((V.obj (iPush.obj (exceptional.obj K)))⟦m⟧ ⟶
      V.obj (jPush.obj (jPull.obj K)))
  exceptional_open_zero (G : U) : IsZero (W.obj (exceptional.obj (jPush.obj G)))
  exceptional_unit (Q : Z) : IsIso (exceptionalAdjunction.unit.app Q)

/-- The finite-Tor clauses, including the specified quantitative bounds. The
interval predicates use the actual all-module Tor tests of the coefficient stage.
Source: blueprint supported localization, clauses (1')--(4')
(blueprint: prop-sf-localization-all-stages). -/
structure SfSupportedLocalizationTor
    {C Z U : Type c} [Category.{h} C] [Category.{h} Z] [Category.{h} U]
    {A : Type a} [Category.{b} A] [Preadditive A] [HasZeroObject A]
    [HasShift A ℤ] [∀ n : ℤ, (shiftFunctor A n).Additive] [Pretriangulated A]
    {B D : Type a} [Category.{b} B] [Category.{b} D] [HasZeroMorphisms B]
    {V : C ⥤ A} {W : Z ⥤ B} {T : U ⥤ D}
    (S : SfSupportedLocalization V W T)
    (PX : C → Prop) (PZ : Z → Prop) (PU : U → Prop)
    (IX : C → ℤ → ℤ → Prop) (IZ : Z → ℤ → ℤ → Prop)
    (IU : U → ℤ → ℤ → Prop) (N : ℤ) : Prop where
  open_preserves (G : U) : PU G → PX (S.jPush.obj G)
  exceptional_preserves (K : C) : PX K → PZ (S.exceptional.obj K)
  closed_preserves (Q : Z) : PZ Q → PX (S.iPush.obj Q)
  closed_pull_preserves (K : C) : PX K → PZ (S.iPull.obj K)
  open_pull_preserves (K : C) : PX K → PU (S.jPull.obj K)
  open_interval (G : U) (r s : ℤ) : IU G r s → IX (S.jPush.obj G) r (s + N)
  exceptional_interval (K : C) (r s : ℤ) : IX K r s →
    IZ (S.exceptional.obj K) r (s + N + 1)
  closed_interval (Q : Z) (r s : ℤ) : IZ Q r s → IX (S.iPush.obj Q) r s
  closed_pull_interval (K : C) (r s : ℤ) : IX K r s → IZ (S.iPull.obj K) r s
  open_pull_interval (K : C) (r s : ℤ) : IX K r s → IU (S.jPull.obj K) r s

/-- The intrinsic finite constructible category, using the recorded predicate.
Source: blueprint supported localization, finite stage
(blueprint: prop-sf-localization-all-stages). -/
abbrev SfLocalizationFiniteCategory (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (n : ℕ) (X : Scheme.{u}) :=
  (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) X).FullSubcategory

/-- Compatibility of a restricted adjunction unit with the specified ambient unit.
This is the commuting equation for its two comparison isomorphisms.
Source: blueprint supported localization, canonical maps in (1)--(2)
(blueprint: prop-sf-localization-all-stages). -/
def SfLocalizationUnitCompatibility
    {C₀ D₀ : Type c} [Category.{h} C₀] [Category.{h} D₀]
    {C D : Type a} [Category.{b} C] [Category.{b} D]
    (V : C₀ ⥤ C) (W : D₀ ⥤ D) {L : C₀ ⥤ D₀} {R : D₀ ⥤ C₀}
    {F : C ⥤ D} {G : D ⥤ C} (restricted : L ⊣ R) (ambient : F ⊣ G)
    (leftComparison : L ⋙ W ≅ V ⋙ F) (rightComparison : R ⋙ V ≅ W ⋙ G) : Prop :=
  ∀ K : C₀, V.map (restricted.unit.app K) ≫
    rightComparison.hom.app (L.obj K) ≫ G.map (leftComparison.hom.app K) =
      ambient.unit.app (V.obj K)

/-- The unit equation for two adjunctions under specified functor comparisons.
This is the literal commuting equation, with no invertibility or coherence added.
Source: blueprint supported localization, coefficient-passage unit normalization
(blueprint: prop-sf-localization-all-stages). -/
def SfLocalizationScalarUnitCompatibility
    {C₀ D₀ : Type c} [Category.{h} C₀] [Category.{h} D₀]
    {C₁ D₁ : Type a} [Category.{b} C₁] [Category.{b} D₁]
    (FX : C₀ ⥤ C₁) (FZ : D₀ ⥤ D₁)
    {L₀ : C₀ ⥤ D₀} {R₀ : D₀ ⥤ C₀} {L₁ : C₁ ⥤ D₁} {R₁ : D₁ ⥤ C₁}
    (adj₀ : L₀ ⊣ R₀) (adj₁ : L₁ ⊣ R₁)
    (left : FX ⋙ L₁ ≅ L₀ ⋙ FZ) (right : FZ ⋙ R₁ ≅ R₀ ⋙ FX) : Prop :=
  ∀ K : C₀, adj₁.unit.app (FX.obj K) ≫ R₁.map (left.hom.app K) ≫
    right.hom.app (L₀.obj K) = FX.map (adj₀.unit.app K)

/-- The counit equation for the same specified scalar comparisons of adjunctions.
This names its exact equation so elaboration shares the categorical calculation.
Source: blueprint supported localization, coefficient-passage counit normalization
(blueprint: prop-sf-localization-all-stages). -/
def SfLocalizationScalarCounitCompatibility
    {C₀ D₀ : Type c} [Category.{h} C₀] [Category.{h} D₀]
    {C₁ D₁ : Type a} [Category.{b} C₁] [Category.{b} D₁]
    (FX : C₀ ⥤ C₁) (FZ : D₀ ⥤ D₁)
    {L₀ : C₀ ⥤ D₀} {R₀ : D₀ ⥤ C₀} {L₁ : C₁ ⥤ D₁} {R₁ : D₁ ⥤ C₁}
    (adj₀ : L₀ ⊣ R₀) (adj₁ : L₁ ⊣ R₁)
    (left : FX ⋙ L₁ ≅ L₀ ⋙ FZ) (right : FZ ⋙ R₁ ≅ R₀ ⋙ FX) : Prop :=
  ∀ Q : D₀, L₁.map (right.hom.app Q) ≫ left.hom.app (R₀.obj Q) ≫
    FZ.map (adj₀.counit.app Q) = adj₁.counit.app (FZ.obj Q)

/-- Actual finite-stage operations and their constructible adjunctions. The
normalizations identify every functor with the recorded intrinsic operation.
Source: blueprint supported localization, clauses (1)--(4), finite stage
(blueprint: prop-sf-localization-all-stages). -/
structure SfFiniteLocalization
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (n : ℕ) (k : Type u) [Field k]
    {X Z U : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] where
  supported : SfSupportedLocalization
    (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) X).ι
    (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) Z).ι
    (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) U).ι
  closed_pull : supported.iPull ⋙
      (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) Z).ι ≅
    (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) X).ι ⋙
      finiteDerivedPullback l E n i
  open_pull : supported.jPull ⋙
      (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) U).ι ≅
    (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) X).ι ⋙
      finiteDerivedPullback l E n j
  closed_push : supported.iPush ⋙
      (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) X).ι ≅
    (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) Z).ι ⋙
      proEtaleConstantDerivedDirectImage i (Padic.coefficientExtensionRing l E (n + 1))
  open_push : supported.jPush ⋙
      (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) X).ι ≅
    (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) U).ι ⋙
      proEtaleConstantDerivedDirectImage j (Padic.coefficientExtensionRing l E (n + 1))
  open_unit : SfLocalizationUnitCompatibility
    (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) X).ι
    (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) U).ι
    supported.openAdjunction
    (finiteRecollementDerivedAdjunction j
      (Padic.coefficientExtensionRing l E (n + 1))) open_pull open_push
  closed_unit : SfLocalizationUnitCompatibility
    (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) X).ι
    (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) Z).ι
    supported.closedAdjunction
    (finiteRecollementDerivedAdjunction i
      (Padic.coefficientExtensionRing l E (n + 1))) closed_pull closed_push
  exceptional_comparison : supported.exceptional ⋙
      (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) Z).ι ≅
    (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) X).ι ⋙
      ProEtale.sfFiniteExceptional (Padic.coefficientExtensionRing l E (n + 1))
        (Compactification.ofIsProper i)
  tor (d c : ℕ) :
    ((IsEmpty U ∧ d = 0) ∨ (Nonempty U ∧
      topologicalKrullDim U = (d : WithBot ℕ∞))) →
    HasTorsionEtaleCohomologicalDimensionLE (Spec (.of k)) c →
    SfSupportedLocalizationTor supported
      (fun K ↦ finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X K.obj)
      (fun K ↦ finiteTorConstructible l E (n + 1) (Nat.succ_pos n) Z K.obj)
      (fun K ↦ finiteTorConstructible l E (n + 1) (Nat.succ_pos n) U K.obj)
      (fun K ↦ HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1)) K.obj)
      (fun K ↦ HasProEtaleTorAmplitude Z (Padic.coefficientExtensionRing l E (n + 1)) K.obj)
      (fun K ↦ HasProEtaleTorAmplitude U (Padic.coefficientExtensionRing l E (n + 1)) K.obj)
      (2 * (d : ℤ) + (c : ℤ))

/-- The canonical field map into a residue field, through global sections.
Source: blueprint supported localization, field-base hypothesis
(blueprint: prop-sf-localization-all-stages). -/
def sfLocalizationResidueMap (k : Type u) [Field k]
    (X : Scheme.{u}) (t : X ⟶ Spec (.of k)) (x : X) :
    CommRingCat.of k ⟶ X.residueField x :=
  (Scheme.ΓSpecIso (.of k)).inv ≫ t.appTop ≫ X.Γevaluation x

/-- The inherited invertibility instance used in the recorded pullbacks.
This is the image of the given unit under the canonical residue-field map.
Source: blueprint supported localization, coefficient hypothesis
(blueprint: prop-sf-localization-all-stages). -/
@[instance_reducible]
def sfLocalizationPrimeInvertible (k : Type u) [Field k] (l : ℕ)
    (hl : IsUnit (l : k)) (X : Scheme.{u}) (t : X ⟶ Spec (.of k)) (x : X) :
    Invertible (l : X.residueField x) :=
  (Eq.mp (congrArg IsUnit (map_natCast (sfLocalizationResidueMap k X t x).hom l))
    (hl.map (sfLocalizationResidueMap k X t x).hom)).invertible

/-- An integral Tor interval means the same interval at every positive reduction.
Source: blueprint supported localization, clauses (1')--(3'), integral stage
(blueprint: prop-sf-localization-all-stages). -/
def SfLocalizationIntegralInterval (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) (K : sfIntegralConstructibleCategory l E X) (r s : ℤ) : Prop :=
  r ≤ s ∧ ∀ n : ℕ, HasProEtaleTorAmplitude X
    (Padic.coefficientExtensionRing l E (n + 1))
    ((scalarReductionDerivedExtension.{u, u} l E X n).obj K.obj) r s

/-- Derived reduction restricted to the exact recorded constructible categories.
Its proof is the constructibility clause of the integral object's membership proof.
Source: blueprint supported localization, integral reduction paragraph
(blueprint: prop-sf-localization-all-stages). -/
def sfLocalizationConstructibleReduction (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) (n : ℕ) :
    sfIntegralConstructibleCategory l E X ⥤ SfLocalizationFiniteCategory l E n X :=
  (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) X).lift
    ((sfIntegralConstructible l E X).ι ⋙ scalarReductionDerivedExtension.{u, u} l E X n)
    (fun K ↦ (K.property.2.choose_spec.choose_spec.2 n).1)

/-- Integral supported localization, with its ordinary completed direct images,
actual completed pullbacks, and exceptional reductions. The natural reduction
isomorphisms, together with completeness of their source, express the inverse-limit
formula: the tower transitions are the transported canonical quotient transitions.
Source: blueprint supported localization, integral clauses (1)--(4), (1')--(4')
(blueprint: prop-sf-localization-all-stages). -/
structure SfIntegralLocalization
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (k : Type u) [Field k] (hl : IsUnit (l : k))
    {X Z U : Scheme.{u}} (t : X ⟶ Spec (.of k))
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] where
  supported : SfSupportedLocalization
    (sfIntegralConstructible l E X).ι (sfIntegralConstructible l E Z).ι
    (sfIntegralConstructible l E U).ι
  closed_pull : supported.iPull ≅
    @constructibleIntegralPullback l _ E _ _ _ Z X i
      (sfLocalizationPrimeInvertible k l hl Z (i ≫ t))
      (sfLocalizationPrimeInvertible k l hl X t)
  open_pull : supported.jPull ≅
    @constructibleIntegralPullback l _ E _ _ _ U X j
      (sfLocalizationPrimeInvertible k l hl U (j ≫ t))
      (sfLocalizationPrimeInvertible k l hl X t)
  closed_push : supported.iPush ⋙ (sfIntegralConstructible l E X).ι ≅
    (sfIntegralConstructible l E Z).ι ⋙ sfCompletedDerivedDirectImage l E i
  open_push : supported.jPush ⋙ (sfIntegralConstructible l E X).ι ≅
    (sfIntegralConstructible l E U).ι ⋙ sfCompletedDerivedDirectImage l E j
  closed_limit (Q : sfIntegralConstructibleCategory l E Z) :
    ∃ hp : HasProduct (sfDirectImageTerm l E i Q.obj),
      ∃ L : @SfIntegralDirectImage l _ E _ _ _ Z X i Q.obj hp,
        Nonempty (L.obj ≅ (supported.iPush.obj Q).obj) ∧
          ∀ n : ℕ, IsIso (@sfDirectImageReductionComparison l _ E _ _ _ Z X i Q.obj hp L n)
  open_limit (G : sfIntegralConstructibleCategory l E U) :
    ∃ hp : HasProduct (sfDirectImageTerm l E j G.obj),
      ∃ L : @SfIntegralDirectImage l _ E _ _ _ U X j G.obj hp,
        Nonempty (L.obj ≅ (supported.jPush.obj G).obj) ∧
          ∀ n : ℕ, IsIso (@sfDirectImageReductionComparison l _ E _ _ _ U X j G.obj hp L n)
  finiteStages (n : ℕ) : SfFiniteLocalization l E n k i j
  closed_reduction (n : ℕ) :
    supported.iPush ⋙ sfLocalizationConstructibleReduction l E X n ≅
      sfLocalizationConstructibleReduction l E Z n ⋙ (finiteStages n).supported.iPush
  open_reduction (n : ℕ) :
    supported.jPush ⋙ sfLocalizationConstructibleReduction l E X n ≅
      sfLocalizationConstructibleReduction l E U n ⋙ (finiteStages n).supported.jPush
  open_pull_reduction (n : ℕ) :
    supported.jPull ⋙ sfLocalizationConstructibleReduction l E U n ≅
      sfLocalizationConstructibleReduction l E X n ⋙ (finiteStages n).supported.jPull
  exceptional_reduction (n : ℕ) :
    supported.exceptional ⋙ sfLocalizationConstructibleReduction l E Z n ≅
      sfLocalizationConstructibleReduction l E X n ⋙ (finiteStages n).supported.exceptional
  exceptional_counit_reduction (n : ℕ) (K : sfIntegralConstructibleCategory l E X) :
    (sfLocalizationConstructibleReduction l E X n).map
        (supported.exceptionalAdjunction.counit.app K) =
      (closed_reduction n).hom.app (supported.exceptional.obj K) ≫
        (finiteStages n).supported.iPush.map ((exceptional_reduction n).hom.app K) ≫
        (finiteStages n).supported.exceptionalAdjunction.counit.app
          ((sfLocalizationConstructibleReduction l E X n).obj K)
  open_unit_reduction (n : ℕ) (K : sfIntegralConstructibleCategory l E X) :
    (sfLocalizationConstructibleReduction l E X n).map
        (supported.openAdjunction.unit.app K) ≫
      (open_reduction n).hom.app (supported.jPull.obj K) ≫
        (finiteStages n).supported.jPush.map ((open_pull_reduction n).hom.app K) =
      (finiteStages n).supported.openAdjunction.unit.app
        ((sfLocalizationConstructibleReduction l E X n).obj K)
  tor (d c : ℕ) :
    ((IsEmpty U ∧ d = 0) ∨ (Nonempty U ∧
      topologicalKrullDim U = (d : WithBot ℕ∞))) →
    HasTorsionEtaleCohomologicalDimensionLE (Spec (.of k)) c →
    SfSupportedLocalizationTor supported
      (fun K ↦ finiteTorConstructibleIntegral l E X K.obj)
      (fun K ↦ finiteTorConstructibleIntegral l E Z K.obj)
      (fun K ↦ finiteTorConstructibleIntegral l E U K.obj)
      (SfLocalizationIntegralInterval l E X)
      (SfLocalizationIntegralInterval l E Z)
      (SfLocalizationIntegralInterval l E U) (2 * (d : ℤ) + (c : ℤ))

section IntegralLimit

variable {l : ℕ} [Fact l.Prime]
  {E : Type u} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {k : Type u} [Field k] {hl : IsUnit (l : k)}
  {X Z U : Scheme.{u}} {t : X ⟶ Spec (.of k)}
  {i : Z ⟶ X} {j : U ⟶ X} [IsClosedImmersion i] [IsOpenImmersion j]
  (S : SfIntegralLocalization l E k hl t i j)
  (K : sfIntegralConstructibleCategory l E X)

/-- The n-th term of the integral exceptional-image formula, with its finite
coefficient action retained until restriction. Source: blueprint localization (2)
(blueprint: prop-sf-localization-all-stages). -/
abbrev sfLocalizationExceptionalTerm (n : ℕ) :=
  (scalarReductionDerivedRestriction.{u, u} l E Z n).obj
    ((S.finiteStages n).supported.exceptional.obj
      ((sfLocalizationConstructibleReduction l E X n).obj K)).obj

/-- The reduction comparison fixed by the exceptional counit normalization.
Source: blueprint localization (2), integral reduction comparison
(blueprint: prop-sf-localization-all-stages). -/
def sfLocalizationExceptionalComparison (n : ℕ) :=
  (scalarReductionDerivedRestriction.{u, u} l E Z n).mapIso
    ((intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) Z).ι.mapIso
      ((S.exceptional_reduction n).app K))

/-- The quotient transition of the exceptional-image tower, transported through
the counit-normalized finite reductions. Thus it retains the quotient coherence
of the actual derived reduction tower. Source: blueprint localization (2)
(blueprint: prop-sf-localization-all-stages). -/
def sfLocalizationExceptionalTransition (n : ℕ) :
    sfLocalizationExceptionalTerm S K (n + 1) ⟶ sfLocalizationExceptionalTerm S K n :=
  (sfLocalizationExceptionalComparison S K (n + 1)).inv ≫
    (sfDerivedReductionTransition l E Z n).app (S.supported.exceptional.obj K).obj ≫
    (sfLocalizationExceptionalComparison S K n).hom

set_option linter.unusedVariables false in
/-- The displayed Rlim formula with its actual reduction projections, not just
an isomorphism to an unspecified limit object. Source: blueprint localization (2)
(blueprint: prop-sf-localization-all-stages).
Proof: the exceptional value is an object of sfIntegralConstructibleCategory,
so its defining completeness is the Roos triangle of its canonical reductions.
Whisker each counit-normalized exceptional reduction by exact scalar restriction.
The resulting isomorphisms identify that reduction tower with the displayed
finite-exceptional tower. The definition of the transition conjugates the actual
quotient transitions, so every square commutes. Transport the product and the
Roos triangle through these isomorphisms. Its n-th first-map component is exactly
the canonical reduction unit followed by the specified comparison. This proves
existence of the product, the displayed projection, and distinguishedness. -/
theorem sfLocalizationExceptionalLimit :
    ∃ hp : HasProduct (sfLocalizationExceptionalTerm S K),
      (fun [hprod : HasProduct (sfLocalizationExceptionalTerm S K)] ↦
        ∃ δ : (∏ᶜ (sfLocalizationExceptionalTerm S K)) ⟶
            (S.supported.exceptional.obj K).obj⟦(1 : ℤ)⟧,
          IsDerivedLimitTriangle (sfLocalizationExceptionalTransition S K)
            (S.supported.exceptional.obj K).obj
            (Pi.lift (fun n ↦ (sfDerivedReductionUnit l E Z n).app
              (S.supported.exceptional.obj K).obj ≫
                (sfLocalizationExceptionalComparison S K n).hom)) δ) (hprod := hp) := by
  -- Completeness supplies the canonical Roos triangle, including its reduction projections.
  obtain ⟨hp, δ, hδ⟩ := (S.supported.exceptional.obj K).property.1
  let := hp
  let e := sfLocalizationExceptionalComparison S K
  have hp' : HasProduct (sfLocalizationExceptionalTerm S K) :=
    hasProduct_of_equiv_of_iso
      (fun n ↦ (sfDerivedReductionRestricted l E Z n).obj
        (S.supported.exceptional.obj K).obj)
      (sfLocalizationExceptionalTerm S K) (Equiv.refl ℕ) (fun n ↦ (e n).symm)
  refine ⟨hp', ?_⟩
  let := hp'
  let a : (∏ᶜ fun n ↦ (sfDerivedReductionRestricted l E Z n).obj
      (S.supported.exceptional.obj K).obj) ≅ ∏ᶜ (sfLocalizationExceptionalTerm S K) :=
    { hom := Limits.Pi.map (fun n ↦ (e n).hom)
      inv := Limits.Pi.map (fun n ↦ (e n).inv)
      hom_inv_id := by
        rw [Limits.Pi.map_comp_map]
        simp only [Iso.hom_inv_id, Limits.Pi.map_id]
      inv_hom_id := by
        rw [Limits.Pi.map_comp_map]
        simp only [Iso.inv_hom_id, Limits.Pi.map_id] }
  -- The prescribed quotient transitions are conjugate through the reduction comparisons.
  have ha : a.hom ≫ towerTransitionEndomorphism (sfLocalizationExceptionalTransition S K) =
      towerTransitionEndomorphism
        (fun n ↦ (sfDerivedReductionTransition l E Z n).app
          (S.supported.exceptional.obj K).obj) ≫ a.hom := by
    dsimp only [a]
    apply towerTransitionEndomorphism_natural_backward
      (fun n ↦ (sfDerivedReductionTransition l E Z n).app
        (S.supported.exceptional.obj K).obj)
      (sfLocalizationExceptionalTransition S K) (fun n ↦ (e n).hom)
    intro n
    change (e (n + 1)).hom ≫
        ((e (n + 1)).inv ≫ _ ≫ (e n).hom) = _
    simp only [Iso.hom_inv_id_assoc]
  -- Transport all three arrows; in particular, retain the specified first-map components.
  refine ⟨a.inv ≫ δ, ?_⟩
  apply Pretriangulated.isomorphic_distinguished _ hδ
  refine Triangle.isoMk _ _ (Iso.refl _) a.symm a.symm ?_ ?_ ?_
  · change (Pi.lift (fun n ↦ (sfDerivedReductionUnit l E Z n).app
        (S.supported.exceptional.obj K).obj ≫ (e n).hom)) ≫ a.inv =
      𝟙 _ ≫ Pi.lift (fun n ↦ (sfDerivedReductionUnit l E Z n).app
        (S.supported.exceptional.obj K).obj)
    apply Pi.hom_ext
    intro n
    simp [a, Category.assoc]
  · change towerTransitionEndomorphism (sfLocalizationExceptionalTransition S K) ≫
        a.inv = a.inv ≫ towerTransitionEndomorphism _
    apply (cancel_mono a.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← ha, Iso.inv_hom_id_assoc]
  · change (a.inv ≫ δ) ≫ (shiftFunctor _ (1 : ℤ)).map (𝟙 _) = a.inv ≫ δ
    rw [CategoryTheory.Functor.map_id, Category.comp_id]

end IntegralLimit

/-- Rational supported localization in the raw scalar localization. Its three
right adjoints are identified with rationalizations of the integral operations.
In particular the exceptional operation is the specified one, rather than an
unspecified extra right adjoint. At field coefficients every object is finite Tor.
Source: blueprint supported localization, rational clauses (1)--(4)
(blueprint: prop-sf-localization-all-stages). -/
structure SfRationalLocalization
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (k : Type u) [Field k] (hl : IsUnit (l : k))
    {X Z U : Scheme.{u}} (t : X ⟶ Spec (.of k))
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] where
  integral : SfIntegralLocalization l E k hl t i j
  supported : SfSupportedLocalization
    (𝟭 (sfRationalConstructibleCategory l E X))
    (𝟭 (sfRationalConstructibleCategory l E Z))
    (𝟭 (sfRationalConstructibleCategory l E U))
  closed_pull : supported.iPull =
    @rationalDerivedPullback l _ E _ _ _ Z X i
      (sfLocalizationPrimeInvertible k l hl Z (i ≫ t))
      (sfLocalizationPrimeInvertible k l hl X t)
  open_pull : supported.jPull =
    @rationalDerivedPullback l _ E _ _ _ U X j
      (sfLocalizationPrimeInvertible k l hl U (j ≫ t))
      (sfLocalizationPrimeInvertible k l hl X t)
  closed_push : sfRationalConstructibleLocalization l E Z ⋙ supported.iPush ≅
    integral.supported.iPush ⋙ sfRationalConstructibleLocalization l E X
  open_push : sfRationalConstructibleLocalization l E U ⋙ supported.jPush ≅
    integral.supported.jPush ⋙ sfRationalConstructibleLocalization l E X
  exceptional : sfRationalConstructibleLocalization l E X ⋙ supported.exceptional ≅
    integral.supported.exceptional ⋙ sfRationalConstructibleLocalization l E Z
  open_pull_localization : sfRationalConstructibleLocalization l E X ⋙ supported.jPull ≅
    integral.supported.jPull ⋙ sfRationalConstructibleLocalization l E U
  counit_localization : SfLocalizationScalarCounitCompatibility
    (sfRationalConstructibleLocalization l E Z) (sfRationalConstructibleLocalization l E X)
    integral.supported.exceptionalAdjunction supported.exceptionalAdjunction
    closed_push exceptional
  open_unit_localization : SfLocalizationScalarUnitCompatibility
    (sfRationalConstructibleLocalization l E X) (sfRationalConstructibleLocalization l E U)
    integral.supported.openAdjunction supported.openAdjunction open_pull_localization open_push
  unit_localization : SfLocalizationScalarUnitCompatibility
    (sfRationalConstructibleLocalization l E Z) (sfRationalConstructibleLocalization l E X)
    integral.supported.exceptionalAdjunction supported.exceptionalAdjunction
    closed_push exceptional


/-- The finite-stage comparison equations for supported localization, stated once
in categorical variables so their elaboration does not repeatedly unfold the
p-adic field structures. These are the closed/open image and exceptional comparisons,
with their actual counit, open unit and exceptional unit normalizations.
Source: blueprint supported localization, algebraically closed coefficient passage
(blueprint: prop-sf-localization-all-stages). -/
structure SfLocalizationStageComparison
    {C₀ Z₀ U₀ : Type c} [Category.{h} C₀] [Category.{h} Z₀] [Category.{h} U₀]
    [Preadditive C₀] [HasZeroObject C₀] [HasShift C₀ ℤ]
    [∀ n : ℤ, (shiftFunctor C₀ n).Additive] [Pretriangulated C₀]
    [HasZeroMorphisms Z₀]
    {C₁ Z₁ U₁ : Type a} [Category.{b} C₁] [Category.{b} Z₁] [Category.{b} U₁]
    [Preadditive C₁] [HasZeroObject C₁] [HasShift C₁ ℤ]
    [∀ n : ℤ, (shiftFunctor C₁ n).Additive] [Pretriangulated C₁]
    [HasZeroMorphisms Z₁]
    (S₀ : SfSupportedLocalization (𝟭 C₀) (𝟭 Z₀) (𝟭 U₀))
    (S₁ : SfSupportedLocalization (𝟭 C₁) (𝟭 Z₁) (𝟭 U₁))
    (FX : C₀ ⥤ C₁) (FZ : Z₀ ⥤ Z₁) (FU : U₀ ⥤ U₁) where
  closed_push : FZ ⋙ S₁.iPush ≅ S₀.iPush ⋙ FX
  open_push : FU ⋙ S₁.jPush ≅ S₀.jPush ⋙ FX
  exceptional : FX ⋙ S₁.exceptional ≅ S₀.exceptional ⋙ FZ
  open_pull : FX ⋙ S₁.jPull ≅ S₀.jPull ⋙ FU
  counit : SfLocalizationScalarCounitCompatibility FZ FX
    S₀.exceptionalAdjunction S₁.exceptionalAdjunction closed_push exceptional
  open_unit : SfLocalizationScalarUnitCompatibility FX FU
    S₀.openAdjunction S₁.openAdjunction open_pull open_push
  unit : SfLocalizationScalarUnitCompatibility FZ FX
    S₀.exceptionalAdjunction S₁.exceptionalAdjunction closed_push exceptional


/-- Supported localization on the actual common-stage category. The finite-stage
comparisons are natural isomorphisms of functors, including their Hom actions.
The adjunction to the recorded common-stage pullback determines direct image;
the next adjunction determines the exceptional functor uniquely up to the
compatible adjoint isomorphism. No arbitrary map or arbitrary equivalence is used.
Source: blueprint supported localization, algebraically closed clauses (1)--(4)
(blueprint: prop-sf-localization-all-stages). -/
structure SfAlgebraicallyClosedLocalization
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (k : Type u) [Field k] (hl : IsUnit (l : k))
    {X Z U : Scheme.{u}} (t : X ⟶ Spec (.of k))
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] where
  stages (L : AlgebraicallyClosedCoefficients.Index l Ω) :
    SfRationalLocalization l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
      k hl t i j
  supported : SfSupportedLocalization
    (𝟭 (generalAlgebraicallyClosedConstructibleCategory l Ω X))
    (𝟭 (generalAlgebraicallyClosedConstructibleCategory l Ω Z))
    (𝟭 (generalAlgebraicallyClosedConstructibleCategory l Ω U))
  closed_pull : supported.iPull =
    @commonStageDerivedPullback l _ Ω _ _ _ Z X i
      (sfLocalizationPrimeInvertible k l hl Z (i ≫ t))
      (sfLocalizationPrimeInvertible k l hl X t)
  open_pull : supported.jPull =
    @commonStageDerivedPullback l _ Ω _ _ _ U X j
      (sfLocalizationPrimeInvertible k l hl U (j ≫ t))
      (sfLocalizationPrimeInvertible k l hl X t)
  comparison (L : AlgebraicallyClosedCoefficients.Index l Ω) :
    SfLocalizationStageComparison (stages L).supported supported
      (GeneralAlgebraicallyClosedCoefficients.inclusion (Y := X) L)
      (GeneralAlgebraicallyClosedCoefficients.inclusion (Y := Z) L)
      (GeneralAlgebraicallyClosedCoefficients.inclusion (Y := U) L)

/-- Weil lifts of the supported adjunctions and all three triangle arrows.
Underlying functors and maps are specified, so this asserts equivariance of the
actual triangle; it does not place a triangulation on the category of Weil pairs.
Source: blueprint supported localization, final Weil clause
(blueprint: prop-sf-localization-all-stages). -/
structure SfWeilLocalization
    {C Z U : Type c} [Category.{h} C] [Category.{h} Z] [Category.{h} U]
    [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [HasZeroMorphisms Z]
    (S : SfSupportedLocalization (𝟭 C) (𝟭 Z) (𝟭 U))
    (ΦX : C ⥤ C) (ΦZ : Z ⥤ Z) (ΦU : U ⥤ U) where
  exceptionalLift : Endofunctor.IsoAlgebra ΦX ⥤ Endofunctor.IsoAlgebra ΦZ
  closedLift : Endofunctor.IsoAlgebra ΦZ ⥤ Endofunctor.IsoAlgebra ΦX
  openPullLift : Endofunctor.IsoAlgebra ΦX ⥤ Endofunctor.IsoAlgebra ΦU
  openPushLift : Endofunctor.IsoAlgebra ΦU ⥤ Endofunctor.IsoAlgebra ΦX
  shiftLift : Endofunctor.IsoAlgebra ΦX ⥤ Endofunctor.IsoAlgebra ΦX
  exceptional_underlying : exceptionalLift ⋙ Endofunctor.IsoAlgebra.forget ΦZ =
    Endofunctor.IsoAlgebra.forget ΦX ⋙ S.exceptional
  closed_underlying : closedLift ⋙ Endofunctor.IsoAlgebra.forget ΦX =
    Endofunctor.IsoAlgebra.forget ΦZ ⋙ S.iPush
  open_pull_underlying : openPullLift ⋙ Endofunctor.IsoAlgebra.forget ΦU =
    Endofunctor.IsoAlgebra.forget ΦX ⋙ S.jPull
  open_push_underlying : openPushLift ⋙ Endofunctor.IsoAlgebra.forget ΦX =
    Endofunctor.IsoAlgebra.forget ΦU ⋙ S.jPush
  shift_underlying : shiftLift ⋙ Endofunctor.IsoAlgebra.forget ΦX =
    Endofunctor.IsoAlgebra.forget ΦX ⋙ shiftFunctor C (1 : ℤ)
  closedAdjunction : closedLift ⊣ exceptionalLift
  openAdjunction : openPullLift ⊣ openPushLift
  counit_underlying (K : Endofunctor.IsoAlgebra ΦX) :
    HEq ((Endofunctor.IsoAlgebra.forget ΦX).map (closedAdjunction.counit.app K))
      (S.exceptionalAdjunction.counit.app K.carrier)
  open_unit_underlying (K : Endofunctor.IsoAlgebra ΦX) :
    HEq ((Endofunctor.IsoAlgebra.forget ΦX).map (openAdjunction.unit.app K))
      (S.openAdjunction.unit.app K.carrier)
  closed_unit_underlying (Q : Endofunctor.IsoAlgebra ΦZ) :
    HEq ((Endofunctor.IsoAlgebra.forget ΦZ).map (closedAdjunction.unit.app Q))
      (S.exceptionalAdjunction.unit.app Q.carrier)
  boundaryLift : openPullLift ⋙ openPushLift ⟶ exceptionalLift ⋙ closedLift ⋙ shiftLift
  boundary_underlying (K : Endofunctor.IsoAlgebra ΦX) :
    HEq ((Endofunctor.IsoAlgebra.forget ΦX).map (boundaryLift.app K))
      (S.boundary.app K.carrier)

/-- The actual geometric-fibre morphism induced by a morphism over the finite field.
Source: blueprint supported localization, Weil descent condition
(blueprint: prop-sf-localization-all-stages). -/
def sfLocalizationFiberMap (D : FiniteFieldDatum.{u})
    {Y₀ X₀ : Over (Spec (.of D.k₀))} (f : Y₀ ⟶ X₀) :
    ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).obj Y₀).left ⟶
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).obj X₀).left :=
  ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f).left

end WeilConjectures
