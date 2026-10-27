/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q83
-/
module

public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.SfConstructibleHeart
public import Sheaf.Paper.InverseImagePullbackComparisonDerived
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.Paper.SfScalarExtensionComposition
public import Sheaf.Paper.PbcScalarExtension
public import Sheaf.Paper.IsomorphismCoefficientInclusions

import Sheaf.Paper.SpecifiedPullbackComparisonAlpha
import Sheaf.Paper.IsomorphismPullbackRawStage
import Sheaf.Paper.IsomorphismPullbackScalarShift
import Sheaf.Paper.IsomorphismPullbackUnitLaws
import Sheaf.Paper.IsomorphismPullbackTowerLaws

/-! # Isomorphism pullback, standard halves and coherent rational coefficients

Source: blueprint main-20261015, sec-poincare-duality/sk-lem-finite,
prop-constructible-truncations.proof.md, final automorphism sentence
(blueprint: lem-pod-isomorphism-pullback-texact-coefficients).

The standard halves below are the existing intrinsic classes, rather than the
etale-origin category in the older `pbcIntegralTStructure` interface. Preservation
of both classes in every degree is exactly t-exactness for the stated standard
structures. No new t-structure, pullback, localization or scalar transition is chosen.

## Main declarations

- `IsomorphismPullbackCoefficientStage` packages the integral and rational clauses.
- `IsomorphismPullbackScalarComparison` and the shift predicates retain the prescribed maps.
- `IsomorphismPullbackCoefficientCoherence` gives their unit and tower equations.
- `isomorphismPullback_tExact_coefficients` states the complete coefficient family.
-/

@[expose] public noncomputable section
set_option autoImplicit false
-- This module already has public declarations; avoid a redundant final style scan.
set_option linter.privateModule false
-- These clause packages do not need generated constructor injectivity or size lemmas.
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.Scheme
namespace WeilConjectures
set_option allowUnsafeReducibility true in
attribute [local irreducible] constructibleIntegralPullback rationalDerivedPullback
  integralDerivedPullback sfRationalTriangulationDatum sfRationalScalarExtension
  rationalPullbackScalarComparison completedIntegralCoefficientSheafUnrestricted
  sfIntegralScalarComp sfIntegralScalarUnit
  GeneralAlgebraicallyClosedCoefficients.unitor GeneralAlgebraicallyClosedCoefficients.associator
  AlgebraicallyClosedCoefficients.coefficientInclusion
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.Stage
  GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.stageShift
  GeneralAlgebraicallyClosedCoefficients.transition
open AlgebraicallyClosedCoefficients
  (Index Coefficient coefficientInclusion coefficientInclusion_laws)

/-- The shift square for four specified functors and their specified shift structures.
This only packages Mathlib's `NatTrans.CommShift` with the two composite instances explicit.
Source: blueprint scalar/shift paragraph
(blueprint: lem-pod-isomorphism-pullback-texact-coefficients). -/
def isomorphismPullbackShiftSquare
    {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type u₄}
    [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃] [Category.{v₄} C₄]
    [HasShift C₁ ℤ] [HasShift C₂ ℤ] [HasShift C₃ ℤ] [HasShift C₄ ℤ]
    (F : C₁ ⥤ C₂) (T : C₂ ⥤ C₄) (U : C₁ ⥤ C₃) (G : C₃ ⥤ C₄)
    (sF : F.CommShift ℤ) (sT : T.CommShift ℤ)
    (sU : U.CommShift ℤ) (sG : G.CommShift ℤ) (a : F ⋙ T ≅ U ⋙ G) : Prop :=
  @NatTrans.CommShift _ _ _ _ _ _ a.hom ℤ _ _ _
    (@Functor.CommShift.comp _ _ _ _ _ _ F T ℤ _ _ _ _ sF sT)
    (@Functor.CommShift.comp _ _ _ _ _ _ U G ℤ _ _ _ _ sU sG)

/-- The clauses at one finite coefficient field. The comparison is fixed on every
component by the actual inverse-image-to-completed-pullback map. Its shift equation
transports the termwise inverse-image shift, and the rational shift is its localization.
Source: blueprint final automorphism sentence, integral and rational clauses
(blueprint: lem-pod-isomorphism-pullback-texact-coefficients). -/
structure IsomorphismPullbackCoefficientStage
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y)) where
  integralShift : (constructibleIntegralPullback l E g).CommShift ℤ
  comparison : (sfIntegralConstructible l E Y).ι ⋙ inverseImageIntegralDerived l E g ≅
    constructibleIntegralPullback l E g ⋙ (sfIntegralConstructible l E X).ι
  comparison_normalization : ∀ K : sfIntegralConstructibleCategory l E Y,
    HEq (comparison.hom.app K) (inverseImagePullbackComparisonDerived l E g hX hY K.obj)
  shift_normalization :
    (fun [_s : (constructibleIntegralPullback l E g).CommShift ℤ] ↦
      NatTrans.CommShift comparison.hom ℤ) (_s := integralShift)
  integral_linear : (constructibleIntegralPullback l E g).Linear
    (Padic.coefficientExtensionIntegers l E)
  integral_exact :
    (fun [_s : (constructibleIntegralPullback l E g).CommShift ℤ] ↦
      (constructibleIntegralPullback l E g).IsTriangulated) (_s := integralShift)
  integral_tExact : ∀ (b : Bool) (n : ℤ) (K : sfIntegralConstructibleCategory l E Y),
    sfIntegralStandardClass l E Y b n K →
      sfIntegralStandardClass l E X b n ((constructibleIntegralPullback l E g).obj K)
  rationalShift : (rationalDerivedPullback l E g).CommShift ℤ
  rational_shift_normalization : ∀ K : sfIntegralConstructibleCategory l E Y,
    HEq (((rationalDerivedPullback l E g).commShiftIso
        (self := rationalShift) (1 : ℤ)).hom.app
          ((sfRationalConstructibleLocalization l E Y).obj K))
      ((sfRationalConstructibleLocalization l E X).map
        (((constructibleIntegralPullback l E g).commShiftIso
          (self := integralShift) (1 : ℤ)).hom.app K))
  rational_exact :
    (fun [_s : (rationalDerivedPullback l E g).CommShift ℤ] ↦
      (rationalDerivedPullback l E g).IsTriangulated) (_s := rationalShift)
  rational_tExact : ∀ (b : Bool) (n : ℤ) (K : sfRationalConstructibleCategory l E Y),
    sfRationalStandardClass l E Y b n K →
      sfRationalStandardClass l E X b n ((rationalDerivedPullback l E g).obj K)

attribute [local irreducible] isomorphismPullbackShiftSquare

section Coherence
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]
  (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
  (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))

/-- The integral balancing associator, conjugated by the existing completion comparison
and the actual equality of the small coefficient inclusions. It introduces no new map.
Source: blueprint scalar-tower clause; prop-weil-pbc-scalar-extension
(blueprint: lem-pod-isomorphism-pullback-texact-coefficients). -/
abbrev isomorphismPullbackIntegralAssociator (W : Scheme.{u})
    (E L M : Index l Ω) (h : E ≤ L) (k : L ≤ M) :
    GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω W E L h ⋙
        GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω W L M k ≅
      GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω W E M (h.trans k) :=
  isomorphismCoefficientIntegralAssociator l Ω W E L M h k

/-- Identity scalar extension with its existing completion-unit normalization.
Source: blueprint identity-extension clause; lem-weil-scalar-extension-composition
(blueprint: lem-pod-isomorphism-pullback-texact-coefficients). -/
abbrev isomorphismPullbackIntegralUnitor (W : Scheme.{u}) (E : Index l Ω) :
    GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω W E E le_rfl ≅
      𝟭 (sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) W) :=
  isomorphismCoefficientIntegralUnitor l Ω W E

/-- Shift exactness and integral components of the already prescribed rational comparison.
There is no additional choice of a rational comparison.
Source: blueprint scalar-localization and shift clauses
(blueprint: lem-pod-isomorphism-pullback-texact-coefficients). -/
def isomorphismPullbackRationalScalarLaws
    (S : ∀ E : Index l Ω,
      IsomorphismPullbackCoefficientStage l (Coefficient.{u} l Ω E) g hX hY)
    (E L : Index l Ω) (h : E ≤ L)
    (integral : constructibleIntegralPullback l (Coefficient.{u} l Ω E) g ⋙
      GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω X E L h ≅
    GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω Y E L h ⋙
      constructibleIntegralPullback l (Coefficient.{u} l Ω L) g) : Prop :=
  isomorphismPullbackShiftSquare
    (rationalDerivedPullback l (Coefficient.{u} l Ω E) g)
    (sfRationalScalarExtension l (Coefficient.{u} l Ω E) X 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω L)
      (isomorphismCoefficientInclusion l Ω E L h))
    (sfRationalScalarExtension l (Coefficient.{u} l Ω E) Y 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω L)
      (isomorphismCoefficientInclusion l Ω E L h))
    (rationalDerivedPullback l (Coefficient.{u} l Ω L) g)
    (@IsomorphismPullbackCoefficientStage.rationalShift l _
      (Coefficient.{u} l Ω E) _ _ _ X Y g _ _ _ hX hY (S E))
    (GeneralAlgebraicallyClosedCoefficients.transitionCommShift l Ω X E L h)
    (GeneralAlgebraicallyClosedCoefficients.transitionCommShift l Ω Y E L h)
    (@IsomorphismPullbackCoefficientStage.rationalShift l _
      (Coefficient.{u} l Ω L) _ _ _ X Y g _ _ _ hX hY (S L)) (rationalPullbackScalarComparison l
      (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω L) (isomorphismCoefficientInclusion l Ω E L h) g) ∧
  ∀ K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) Y,
      HEq ((rationalPullbackScalarComparison l (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω L) (isomorphismCoefficientInclusion l Ω E L h) g).hom.app K)
        ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω L) X).map
          (integral.hom.app K.obj))

attribute [local irreducible] isomorphismPullbackRationalScalarLaws

/-- The specified integral scalar comparison, with naturality on all integral arrows,
and exactness of it and its already-prescribed rationalization. Both endpoint shifts
are those of the same stage family, not independently chosen for each extension.
Source: blueprint scalar/shift paragraph; integral-operations scalar comparison
(blueprint: lem-pod-isomorphism-pullback-texact-coefficients). -/
structure IsomorphismPullbackScalarComparison
    (S : ∀ E : Index l Ω,
      IsomorphismPullbackCoefficientStage l (Coefficient.{u} l Ω E) g hX hY)
    (E L : Index l Ω) (h : E ≤ L) where
  integral : constructibleIntegralPullback l (Coefficient.{u} l Ω E) g ⋙
      GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω X E L h ≅
    GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω Y E L h ⋙
      constructibleIntegralPullback l (Coefficient.{u} l Ω L) g
  integral_normalization : ∀ K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) Y,
    integral.app K = integralPullbackScalarComparison l (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω L) (isomorphismCoefficientInclusion l Ω E L h) g K
  integral_shift :
    (fun [_sE : (constructibleIntegralPullback l (Coefficient.{u} l Ω E) g).CommShift ℤ]
      [_sL : (constructibleIntegralPullback l (Coefficient.{u} l Ω L) g).CommShift ℤ] ↦
        NatTrans.CommShift integral.hom ℤ)
      (_sE := (@IsomorphismPullbackCoefficientStage.integralShift l _
      (Coefficient.{u} l Ω E) _ _ _ X Y g _ _ _ hX hY (S E))) (_sL :=
      (@IsomorphismPullbackCoefficientStage.integralShift l _
      (Coefficient.{u} l Ω L) _ _ _ X Y g _ _ _ hX hY (S L)))
  rational_laws : isomorphismPullbackRationalScalarLaws l Ω g hX hY S E L h integral

/-- The identity and tower equations for the same normalized comparison family.
Identity is expressed through the canonical scalar unitors, so that identity extensions
are included even in the unnormalized tensor presentation of the integral categories.
Source: blueprint final automorphism sentence, unit and tower clause
(blueprint: lem-pod-isomorphism-pullback-texact-coefficients). -/
structure IsomorphismPullbackCoefficientCoherence
    (S : ∀ E : Index l Ω,
      IsomorphismPullbackCoefficientStage l (Coefficient.{u} l Ω E) g hX hY)
    (B : ∀ (E L : Index l Ω) (h : E ≤ L),
      IsomorphismPullbackScalarComparison l Ω g hX hY S E L h) : Prop where
  integral_unit : ∀ (E : Index l Ω)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) Y),
      (B E E le_rfl).integral.hom.app K ≫
        (constructibleIntegralPullback l (Coefficient.{u} l Ω E) g).map
          ((isomorphismPullbackIntegralUnitor l Ω Y E).hom.app K) =
      (isomorphismPullbackIntegralUnitor l Ω X E).hom.app
        ((constructibleIntegralPullback l (Coefficient.{u} l Ω E) g).obj K)
  integral_tower : ∀ (E L M : Index l Ω) (h : E ≤ L) (k : L ≤ M)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) Y),
      (GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω X L M k).map
          ((B E L h).integral.hom.app K) ≫
        (B L M k).integral.hom.app
          ((GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω Y E L h).obj K) ≫
        (constructibleIntegralPullback l (Coefficient.{u} l Ω M) g).map
          ((isomorphismPullbackIntegralAssociator l Ω Y E L M h k).hom.app K) =
      (isomorphismPullbackIntegralAssociator l Ω X E L M h k).hom.app
          ((constructibleIntegralPullback l (Coefficient.{u} l Ω E) g).obj K) ≫
        (B E M (h.trans k)).integral.hom.app K
  rational_unit : ∀ (E : Index l Ω)
    (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) Y),
      (rationalPullbackScalarComparison l (Coefficient.{u} l Ω E)
          (Coefficient.{u} l Ω E) (isomorphismCoefficientInclusion l Ω E E le_rfl) g).hom.app K ≫
        (rationalDerivedPullback l (Coefficient.{u} l Ω E) g).map
          ((GeneralAlgebraicallyClosedCoefficients.unitor l Ω Y E).hom.app K) =
      (GeneralAlgebraicallyClosedCoefficients.unitor l Ω X E).hom.app
        ((rationalDerivedPullback l (Coefficient.{u} l Ω E) g).obj K)
  rational_tower : ∀ (E L M : Index l Ω) (h : E ≤ L) (k : L ≤ M)
    (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) Y),
      (sfRationalScalarExtension l (Coefficient.{u} l Ω L) X 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω M)
          (isomorphismCoefficientInclusion l Ω L M k)).map
          ((rationalPullbackScalarComparison l (Coefficient.{u} l Ω E)
          (Coefficient.{u} l Ω L) (isomorphismCoefficientInclusion l Ω E L h) g).hom.app K) ≫
        (rationalPullbackScalarComparison l (Coefficient.{u} l Ω L)
          (Coefficient.{u} l Ω M) (isomorphismCoefficientInclusion l Ω L M k) g).hom.app
          ((sfRationalScalarExtension l (Coefficient.{u} l Ω E) Y 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω L)
          (isomorphismCoefficientInclusion l Ω E L h)).obj K) ≫
        (rationalDerivedPullback l (Coefficient.{u} l Ω M) g).map
          ((GeneralAlgebraicallyClosedCoefficients.associator l Ω Y E L M h k).hom.app K) =
      (GeneralAlgebraicallyClosedCoefficients.associator l Ω X E L M h k).hom.app
          ((rationalDerivedPullback l (Coefficient.{u} l Ω E) g).obj K) ≫
        (rationalPullbackScalarComparison l (Coefficient.{u} l Ω E)
          (Coefficient.{u} l Ω M) (isomorphismCoefficientInclusion l Ω E M (h.trans k)) g).hom.app K

end Coherence

/-- Residue-field invertibility extracted from the stated stalk-unit hypothesis.
This is real data, unique because invertibility structures are subsingletons.
Source: blueprint prime-invertibility hypothesis
(blueprint: lem-pod-isomorphism-pullback-texact-coefficients). -/
@[instance_reducible]
def isomorphismPullbackResidueUnits (l : ℕ) (W : Scheme.{u})
    (hW : ∀ w : W, IsUnit (l : W.presheaf.stalk w)) (w : W) :
    Invertible (l : W.residueField w) :=
  ((map_natCast (W.residue w).hom l) ▸ ((hW w).map (W.residue w).hom)).invertible


section
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]
  (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
  (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))

private theorem coefficientStage_exists :
    Nonempty (IsomorphismPullbackCoefficientStage l E g hX hY) := by
  obtain ⟨s, e, he, ⟨hs, ht⟩, hlin, hi, sr, hr, hrt, hrtEx⟩ :=
    isomorphismPullbackRawStage l E g hX hY
  exact ⟨{ integralShift := s
           comparison := e
           comparison_normalization := he
           shift_normalization := hs
           integral_linear := hlin
           integral_exact := ht
           integral_tExact := hi
           rationalShift := sr
           rational_shift_normalization := hr
           rational_exact := hrt
           rational_tExact := hrtEx }⟩
end

set_option allowUnsafeReducibility true in
attribute [local reducible] constructibleIntegralPullback
  sfConstructibleIntegralScalarExtension scalarReductionSource scalarReductionTarget

section
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

private noncomputable def normalizedIntegralScalarComparison
    :
    constructibleIntegralPullback l E g ⋙
        sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι X ≅
      sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι Y ⋙
          constructibleIntegralPullback l L g :=
  NatIso.ofComponents (integralPullbackScalarComparison l E L ι g) (fun {K J} f ↦ by
    apply ObjectProperty.hom_ext
    exact (specifiedPullbackComparisonAlpha l E L ι g K.obj K.property).choose_spec.2
      J.obj J.property _ f.hom)


end

set_option allowUnsafeReducibility true in
attribute [local irreducible] constructibleIntegralPullback
  sfConstructibleIntegralScalarExtension


section
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]
  (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
  (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))

private theorem coefficientComparisons_exists
    (S : ∀ E : Index l Ω,
      IsomorphismPullbackCoefficientStage l (Coefficient.{u} l Ω E) g hX hY) :
    Nonempty (∀ (E L : Index l Ω) (h : E ≤ L),
      IsomorphismPullbackScalarComparison l Ω g hX hY S E L h) := by
  refine ⟨fun E L h ↦ ?_⟩
  let α := normalizedIntegralScalarComparison l (Coefficient.{u} l Ω E)
    (Coefficient.{u} l Ω L) (isomorphismCoefficientInclusion l Ω E L h) g
  have hs := isomorphismPullbackScalarShift l Ω g hX hY E L h
    (S E).integralShift (S E).rationalShift (S E).comparison
    (S E).comparison_normalization (S E).shift_normalization
    (S E).rational_shift_normalization
    (S L).integralShift (S L).rationalShift (S L).comparison
    (S L).comparison_normalization (S L).shift_normalization
    (S L).rational_shift_normalization α (fun _ ↦ rfl)
  refine { integral := α
           integral_normalization := fun _ ↦ rfl
           integral_shift := hs.1
           rational_laws := ?_ }
  unfold isomorphismPullbackRationalScalarLaws isomorphismPullbackShiftSquare
  refine ⟨hs.2, ?_⟩
  intro K
  unfold rationalPullbackScalarComparison
  exact (rationalPullbackScalarComparison_existsUnique l (Coefficient.{u} l Ω E)
    (Coefficient.{u} l Ω L)
    (isomorphismCoefficientInclusion l Ω E L h) g).exists.choose_spec K


private theorem coefficientCoherence
    (S : ∀ E : Index l Ω,
      IsomorphismPullbackCoefficientStage l (Coefficient.{u} l Ω E) g hX hY)
    (B : ∀ (E L : Index l Ω) (h : E ≤ L),
      IsomorphismPullbackScalarComparison l Ω g hX hY S E L h) :
    IsomorphismPullbackCoefficientCoherence l Ω g hX hY S B := by
  have hA (E L : Index l Ω) (h : E ≤ L)
      (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) Y) :
      (B E L h).integral.app K = integralPullbackScalarComparison l
        (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
        (isomorphismCoefficientInclusion l Ω E L h) g K :=
    (B E L h).integral_normalization K
  have hUnit := isomorphismPullbackUnitLaws l Ω g (fun E L h ↦ (B E L h).integral) hA
  have hTower := isomorphismPullbackTowerLaws l Ω g (fun E L h ↦ (B E L h).integral) hA
  exact ⟨hUnit.1, hTower.1, hUnit.2, hTower.2⟩

end

/-- Isomorphism pullback gives the specified coherent exact, t-exact coefficient family.
Source: blueprint main-20261015, sec-poincare-duality/sk-lem-finite,
prop-constructible-truncations.proof.md, final sentence
(blueprint: lem-pod-isomorphism-pullback-texact-coefficients).

Proof: at each finite coefficient field, isomorphismPullbackRawStage supplies
normalized integral and rational shifts, exactness, both standard-half preservation
clauses, and the specified inverse-image comparison. Package these clauses as S.
The integral scalar comparison has the prescribed components and is natural on
all integral morphisms by specifiedPullbackComparisonAlpha. Package that natural
isomorphism and use isomorphismPullbackScalarShift for its two shift equations.
The existing rationalPullbackScalarComparison already has precisely the localized
integral components, so its uniqueness specification supplies the normalization.
Finally apply isomorphismPullbackUnitLaws and isomorphismPullbackTowerLaws to this
same integral family and its component normalizations. Their four equations are
exactly the integral and rational fields of the required coherence package.
The integral structural maps are the original completion-normalized adapters;
the rational unitors and associators are the existing canonical ones. Thus the
construction chooses no new pullback, transition, or rational comparison, and
retains identity inclusions, torsion arrows and empty schemes.
-/
theorem isomorphismPullback_tExact_coefficients
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [IsNoetherian X] [IsNoetherian Y]
    (_hDimX : ∃ n : ℕ, topologicalKrullDim X ≤ n)
    (_hDimY : ∃ n : ℕ, topologicalKrullDim Y ≤ n)
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y)) :
    (fun [_iX : ∀ x : X, Invertible (l : X.residueField x)]
      [_iY : ∀ y : Y, Invertible (l : Y.residueField y)] ↦
        ∃ S : ∀ E : Index l Ω,
            IsomorphismPullbackCoefficientStage l (Coefficient.{u} l Ω E) g hX hY,
          ∃ B : ∀ (E L : Index l Ω) (h : E ≤ L),
            IsomorphismPullbackScalarComparison l Ω g hX hY S E L h,
            IsomorphismPullbackCoefficientCoherence l Ω g hX hY S B)
      (_iX := isomorphismPullbackResidueUnits l X hX)
      (_iY := isomorphismPullbackResidueUnits l Y hY) := by
  classical
  let : ∀ x : X, Invertible (l : X.residueField x) :=
    isomorphismPullbackResidueUnits l X hX
  let : ∀ y : Y, Invertible (l : Y.residueField y) :=
    isomorphismPullbackResidueUnits l Y hY
  let S : ∀ E : Index l Ω,
      IsomorphismPullbackCoefficientStage l (Coefficient.{u} l Ω E) g hX hY :=
    fun E ↦ Classical.choice (coefficientStage_exists l (Coefficient.{u} l Ω E) g hX hY)
  let B := Classical.choice (coefficientComparisons_exists l Ω g hX hY S)
  exact ⟨S, B, coefficientCoherence l Ω g hX hY S B⟩

end WeilConjectures
