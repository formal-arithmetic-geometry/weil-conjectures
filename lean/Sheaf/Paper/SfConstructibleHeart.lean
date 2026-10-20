/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.Paper.ConstructibleHeart
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
import Mathlib.CategoryTheory.Triangulated.TStructure.Induced
import Sheaf.Paper.SfIntegralStandardTruncations
import Sheaf.Paper.SfScalarExtensionComposition
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TStructure.Heart

/-! # Constructible hearts on the intrinsic coefficient categories

Source: Weil blueprint, order 1506, constructible heart and its standard t-structure
(blueprint: def-weil-constructible-heart).
The existing heart module uses the earlier integral predicate. Here the same standard
classes are placed on the currently recorded intrinsic rational and common-stage categories.

## Main definitions

- `sfRationalHeart`: the full heart in the intrinsic rational category.
- `sfCommonStageHeart`: the full heart in the general common-stage category.
- `sfRationalStandardTStructure` and `sfCommonStageStandardTStructure`: standard t-structures.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (Y : Scheme.{u})

/-- The integral standard class, with either cohomological inequality.
Source: blueprint order 1506 (blueprint: def-weil-constructible-heart). -/
def sfIntegralStandardClass (nonpositive : Bool) (n : ℤ) :
    ObjectProperty (sfIntegralConstructibleCategory l E Y) :=
  fun K ↦ ∀ i : ℤ, (if nonpositive then n < i else i < n) →
    IsZero ((DerivedCategory.homologyFunctor (scalarReductionSource l E Y) i).obj K.obj)

/-- Rational standard classes are the isomorphism closures of the integral classes.
Source: blueprint order 1506 (blueprint: def-weil-constructible-heart). -/
def sfRationalStandardClass (nonpositive : Bool) (n : ℤ) :
    ObjectProperty (sfRationalConstructibleCategory l E Y) :=
  fun K ↦ ∃ M : sfIntegralConstructibleCategory l E Y,
    sfIntegralStandardClass l E Y nonpositive n M ∧
      Nonempty (K ≅ (sfRationalConstructibleLocalization l E Y).obj M)

/-- The heart is exactly the intersection of the two standard degree-zero classes.
Source: blueprint order 1506 (blueprint: def-weil-constructible-heart). -/
def sfRationalHeartProperty : ObjectProperty (sfRationalConstructibleCategory l E Y) :=
  sfRationalStandardClass l E Y true 0 ⊓ sfRationalStandardClass l E Y false 0

/-- The constructible E-heart with its inherited full-subcategory morphisms.
Source: blueprint order 1506 (blueprint: def-weil-constructible-heart). -/
abbrev sfRationalHeart := (sfRationalHeartProperty l E Y).FullSubcategory

variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- Common-stage standard classes are represented in the corresponding finite-stage class.
Source: blueprint order 1506 (blueprint: def-weil-constructible-heart). -/
def sfCommonStageStandardClass (nonpositive : Bool) (n : ℤ) :
    ObjectProperty (generalAlgebraicallyClosedConstructibleCategory l Ω Y) :=
  fun K ↦ ∃ (L : AlgebraicallyClosedCoefficients.Index l Ω)
    (M : GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y L),
    sfRationalStandardClass l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
        Y nonpositive n M ∧
      Nonempty (K ≅
        (GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := Y) L).obj M)

/-- The common-stage constructible heart property.
Source: blueprint order 1506 (blueprint: def-weil-constructible-heart). -/
def sfCommonStageHeartProperty :
    ObjectProperty (generalAlgebraicallyClosedConstructibleCategory l Ω Y) :=
  sfCommonStageStandardClass l Y Ω true 0 ⊓ sfCommonStageStandardClass l Y Ω false 0

/-- The constructible algebraically closed heart is a full subcategory.
Source: blueprint order 1506 (blueprint: def-weil-constructible-heart). -/
abbrev sfCommonStageHeart := (sfCommonStageHeartProperty l Y Ω).FullSubcategory

private theorem rationalStandardClass_scalar
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (Y : Scheme.{u})
    (b : Bool) (n : ℤ) (K : sfRationalConstructibleCategory l E Y)
    (hK : sfRationalStandardClass l E Y b n K) :
    sfRationalStandardClass l L Y b n
      ((sfRationalScalarExtension l E Y 0 (Nat.Prime.ne_zero (Fact.out : l.Prime))
        L ι).obj K) := by
  let hp := Nat.Prime.ne_zero (Fact.out : l.Prime)
  let F := sfRationalScalarExtension l E Y 0 hp L ι
  let I := sfConstructibleIntegralScalarExtension 0 l hp E L ι Y
  obtain ⟨M, hM, ⟨e⟩⟩ := hK
  refine ⟨I.obj M, ?_, ⟨F.mapIso e ≪≫ eqToIso
    ((sfRationalScalarExtension_existsUnique l E Y 0 hp L ι).exists.choose_spec.2.1 _)⟩⟩
  intro i hi
  let G := integralOrdinaryScalar l E L ι Y
  have hz := G.isZero_homologyFunctor_mapDerivedCategory_obj (hM i hi)
  exact hz.of_iso
    ((DerivedCategory.homologyFunctor _ i).mapIso
      ((sfIntegralOrdinaryComparison l E L ι Y).symm.app M))

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  [base : Y.Over (Spec (.of D.k))]
  [hft : LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [hqc : QuasiCompact (Y ↘ Spec (.of D.k))]

include D hl base hft hqc

/-- The intrinsic rational standard classes determine the bounded standard t-structure.
Source: blueprint order 1506 (blueprint: def-weil-constructible-heart).
Proof: good truncations preserve the derived-complete constructible integral category.
Their triangles rationalize through scalar localization. The displayed classes are exactly
its isomorphism closures, so orthogonality, shift stability and truncation follow from the
integral statements. Uniform finite-reduction bounds give boundedness. The prescribed
classes in every degree determine the t-structure uniquely. The finite-type geometric
hypotheses are precisely those of the recorded constructible-heart definition. -/
theorem sfRationalStandardTStructure_existsUnique :
    ∃! t : CategoryTheory.Triangulated.TStructure (sfRationalConstructibleCategory l E Y),
      (∀ n : ℤ, t.le n = sfRationalStandardClass l E Y true n ∧
        t.ge n = sfRationalStandardClass l E Y false n) ∧ ∀ K, t.bounded K := by
  let P := sfIntegralConstructible l E Y
  let a := DerivedCategory.TStructure.t (C := scalarReductionSource l E Y)
  let htr := sfIntegralStandardTruncations l E Y D hl
  let : P.HasInducedTStructure a :=
    ObjectProperty.HasInducedTStructure.mk' (fun X hX n ↦ (htr ⟨X, hX⟩).2 n)
  let t := P.tStructure a
  let Q := sfRationalConstructibleLocalization l E Y
  have hle (n : ℤ) (K : sfIntegralConstructibleCategory l E Y) :
      t.le n K ↔ sfIntegralStandardClass l E Y true n K := by
    change a.le n K.obj ↔ _
    rw [a.le_iff_isLE]
    change K.obj.IsLE n ↔ _
    rw [DerivedCategory.isLE_iff]
    rfl
  have hge (n : ℤ) (K : sfIntegralConstructibleCategory l E Y) :
      t.ge n K ↔ sfIntegralStandardClass l E Y false n K := by
    change a.ge n K.obj ↔ _
    rw [a.ge_iff_isGE]
    change K.obj.IsGE n ↔ _
    rw [DerivedCategory.isGE_iff]
    rfl
  let s : CategoryTheory.Triangulated.TStructure (sfRationalConstructibleCategory l E Y) :=
    { le := sfRationalStandardClass l E Y true
      ge := sfRationalStandardClass l E Y false
      le_isClosedUnderIsomorphisms := by
        intro n
        exact ⟨fun e ⟨M, hM, ⟨i⟩⟩ ↦ ⟨M, hM, ⟨e.symm ≪≫ i⟩⟩⟩
      ge_isClosedUnderIsomorphisms := by
        intro n
        exact ⟨fun e ⟨M, hM, ⟨i⟩⟩ ↦ ⟨M, hM, ⟨e.symm ≪≫ i⟩⟩⟩
      le_shift := by
        intro n b n' h K hK
        obtain ⟨M, hM, ⟨e⟩⟩ := hK
        refine ⟨M⟦b⟧, (hle n' _).mp (t.le_shift n b n' h M ((hle n M).mpr hM)), ?_⟩
        exact ⟨(shiftFunctor _ b).mapIso e ≪≫ (Q.commShiftIso b).symm.app M⟩
      ge_shift := by
        intro n b n' h K hK
        obtain ⟨M, hM, ⟨e⟩⟩ := hK
        refine ⟨M⟦b⟧, (hge n' _).mp (t.ge_shift n b n' h M ((hge n M).mpr hM)), ?_⟩
        exact ⟨(shiftFunctor _ b).mapIso e ≪≫ (Q.commShiftIso b).symm.app M⟩
      zero' := by
        intro K L f hK hL
        obtain ⟨M, hM, ⟨e⟩⟩ := hK
        obtain ⟨N, hN, ⟨e'⟩⟩ := hL
        have hz : ∀ g : Q.obj M ⟶ Q.obj N, g = 0 := by
          intro g
          induction g using TensorProduct.induction_on with
          | zero => rfl
          | tmul c g =>
            have hg : g = 0 := t.zero' g ((hle 0 M).mpr hM) ((hge 1 N).mpr hN)
            simp [hg]
          | add g g' hg hg' => simp [hg, hg']
        have hf := hz (e.inv ≫ f ≫ e'.hom)
        simpa using congrArg (fun g ↦ e.hom ≫ g ≫ e'.inv) hf
      le_zero_le := by
        rintro K ⟨M, hM, e⟩
        exact ⟨M, (hle 1 M).mp (t.le_zero_le M ((hle 0 M).mpr hM)), e⟩
      ge_one_le := by
        rintro K ⟨M, hM, e⟩
        exact ⟨M, (hge 0 M).mp (t.ge_one_le M ((hge 1 M).mpr hM)), e⟩
      exists_triangle_zero_one := by
        intro K
        obtain ⟨M, N, hM, hN, f, g, δ, hT⟩ := t.exists_triangle_zero_one K.obj
        refine ⟨Q.obj M, Q.obj N, ⟨M, (hle 0 M).mp hM, ⟨Iso.refl _⟩⟩,
          ⟨N, (hge 1 N).mp hN, ⟨Iso.refl _⟩⟩, Q.map f, Q.map g,
          Q.map δ ≫ (Q.commShiftIso (1 : ℤ)).hom.app M, ?_⟩
        exact Q.map_distinguished _ hT }
  refine ⟨s, ⟨fun n ↦ ⟨rfl, rfl⟩, ?_⟩, ?_⟩
  · intro K
    obtain ⟨⟨lo, hlo⟩, ⟨hi, hhi⟩⟩ := (htr K.obj).1
    refine ⟨⟨lo, ?_⟩, ⟨hi, ?_⟩⟩
    · constructor
      exact ⟨K.obj, (hge lo K.obj).mp hlo.ge, ⟨Iso.refl _⟩⟩
    · constructor
      exact ⟨K.obj, (hle hi K.obj).mp hhi.le, ⟨Iso.refl _⟩⟩
  · intro s' hs'
    have hle' : s'.le = s.le := funext (fun n ↦ (hs'.1 n).1)
    have hge' : s'.ge = s.ge := funext (fun n ↦ (hs'.1 n).2)
    have extensionality (x y : CategoryTheory.Triangulated.TStructure
        (sfRationalConstructibleCategory l E Y))
        (h₁ : x.le = y.le) (h₂ : x.ge = y.ge) : x = y := by
      cases x
      cases y
      congr 1
    exact extensionality s' s hle' hge'

/-- The bounded rational standard t-structure, fixed by its classes in every degree.
Source: blueprint order 1506 (blueprint: def-weil-constructible-heart). -/
def sfRationalStandardTStructure :=
  (sfRationalStandardTStructure_existsUnique l E Y D hl).exists.choose

/-- The common-stage standard pair determines the bounded t-structure.
Source: blueprint order 1506 (blueprint: def-weil-constructible-heart).
Proof: every finite diagram has a common coefficient field. Finite scalar extension is
exact and t-exact, by its finite free integral description. Thus the finite-stage
truncation triangles descend to the recorded common-stage triangles; orthogonality and
shift stability are checked there. Every object has a finite-stage bound. Uniqueness
follows from the prescribed classes, as in the rational case. -/
theorem sfCommonStageStandardTStructure_existsUnique :
    ∃! t : CategoryTheory.Triangulated.TStructure
        (generalAlgebraicallyClosedConstructibleCategory l Ω Y),
      (∀ n : ℤ, t.le n = sfCommonStageStandardClass l Y Ω true n ∧
        t.ge n = sfCommonStageStandardClass l Y Ω false n) ∧ ∀ K, t.bounded K := by
  classical
  let S := GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y
  let t (A : AlgebraicallyClosedCoefficients.Index l Ω) :=
    sfRationalStandardTStructure l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A) Y D hl
  have ht (A : AlgebraicallyClosedCoefficients.Index l Ω) :
      (∀ n : ℤ, (t A).le n = sfRationalStandardClass l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A) Y true n ∧
        (t A).ge n = sfRationalStandardClass l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A) Y false n) ∧
      ∀ K, (t A).bounded K :=
    (sfRationalStandardTStructure_existsUnique l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A) Y D hl).exists.choose_spec
  have hpres (A B : AlgebraicallyClosedCoefficients.Index l Ω) (h : A ≤ B)
      (b : Bool) (n : ℤ) (M : GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y A)
      (hM : sfRationalStandardClass l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A) Y b n M) :
      sfRationalStandardClass l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω B) Y b n ((S.T h).obj M) := by
    have hspec :=
      (GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique l Ω Y).exists.choose_spec
    have htransition : S.T h =
        GeneralAlgebraicallyClosedCoefficients.transition l Ω Y A B h := hspec.1 A B h
    have hobj := congrArg (fun F : GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y A ⥤
      GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y B ↦ F.obj M) htransition
    exact hobj.symm ▸ rationalStandardClass_scalar l _ _
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω A B h) Y b n M hM
  let s : CategoryTheory.Triangulated.TStructure
      (generalAlgebraicallyClosedConstructibleCategory l Ω Y) :=
    { le := sfCommonStageStandardClass l Y Ω true
      ge := sfCommonStageStandardClass l Y Ω false
      le_isClosedUnderIsomorphisms := by
        intro n
        exact ⟨fun e ⟨A, M, hM, ⟨i⟩⟩ ↦ ⟨A, M, hM, ⟨e.symm ≪≫ i⟩⟩⟩
      ge_isClosedUnderIsomorphisms := by
        intro n
        exact ⟨fun e ⟨A, M, hM, ⟨i⟩⟩ ↦ ⟨A, M, hM, ⟨e.symm ≪≫ i⟩⟩⟩
      le_shift := by
        intro n b n' h K hK
        obtain ⟨A, M, hM, ⟨e⟩⟩ := hK
        let J := GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω)
          (Y := Y) A
        refine ⟨A, M⟦b⟧, ?_,
          ⟨(shiftFunctor _ b).mapIso e ≪≫ (J.commShiftIso b).symm.app M⟩⟩
        rw [← ((ht A).1 n').1]
        exact (t A).le_shift n b n' h M (by rwa [((ht A).1 n).1])
      ge_shift := by
        intro n b n' h K hK
        obtain ⟨A, M, hM, ⟨e⟩⟩ := hK
        let J := GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω)
          (Y := Y) A
        refine ⟨A, M⟦b⟧, ?_,
          ⟨(shiftFunctor _ b).mapIso e ≪≫ (J.commShiftIso b).symm.app M⟩⟩
        rw [← ((ht A).1 n').2]
        exact (t A).ge_shift n b n' h M (by rwa [((ht A).1 n).2])
      zero' := by
        intro K L f hK hL
        obtain ⟨A, M, hM, ⟨e⟩⟩ := hK
        obtain ⟨B, N, hN, ⟨e'⟩⟩ := hL
        have hz : ∀ g : (S.ι A).obj M ⟶ (S.ι B).obj N, g = 0 := by
          intro g
          induction g using StageSystem.PairCategory.hom_induction with
          | h C hA hB g =>
            have hM' := hpres A C hA true 0 M hM
            have hN' := hpres B C hB false 1 N hN
            rw [← ((ht C).1 0).1] at hM'
            rw [← ((ht C).1 1).2] at hN'
            have hg := (t C).zero' g hM' hN'
            rw [StageSystem.mkHom_eq_isoToStage, hg]
            change _ ≫ (GeneralAlgebraicallyClosedCoefficients.inclusion
              (l := l) (Ω := Ω) (Y := Y) C).map 0 ≫ _ = _
            simp
        have hf := hz (e.inv ≫ f ≫ e'.hom)
        simpa using congrArg (fun g ↦ e.hom ≫ g ≫ e'.inv) hf
      le_zero_le := by
        rintro K ⟨A, M, hM, e⟩
        refine ⟨A, M, ?_, e⟩
        rw [← ((ht A).1 1).1]
        exact (t A).le_zero_le M (by rwa [((ht A).1 0).1])
      ge_one_le := by
        rintro K ⟨A, M, hM, e⟩
        refine ⟨A, M, ?_, e⟩
        rw [← ((ht A).1 0).2]
        exact (t A).ge_one_le M (by rwa [((ht A).1 1).2])
      exists_triangle_zero_one := by
        intro K
        let J := GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω)
          (Y := Y) K.stage
        obtain ⟨M, N, hM, hN, f, g, δ, hT⟩ := (t K.stage).exists_triangle_zero_one K.obj
        refine ⟨J.obj M, J.obj N,
          ⟨K.stage, M, ?_, ⟨Iso.refl _⟩⟩, ⟨K.stage, N, ?_, ⟨Iso.refl _⟩⟩,
          J.map f, J.map g, J.map δ ≫ (J.commShiftIso (1 : ℤ)).hom.app M, ?_⟩
        · rwa [← ((ht K.stage).1 0).1]
        · rwa [← ((ht K.stage).1 1).2]
        · exact J.map_distinguished _ hT }
  refine ⟨s, ⟨fun n ↦ ⟨rfl, rfl⟩, ?_⟩, ?_⟩
  · intro K
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := (ht K.stage).2 K.obj
    refine ⟨⟨a, ⟨?_⟩⟩, ⟨b, ⟨?_⟩⟩⟩
    · exact ⟨K.stage, K.obj, (by rw [← ((ht K.stage).1 a).2]; exact ha.ge), ⟨Iso.refl _⟩⟩
    · exact ⟨K.stage, K.obj, (by rw [← ((ht K.stage).1 b).1]; exact hb.le), ⟨Iso.refl _⟩⟩
  · intro s' hs'
    have hle : s'.le = s.le := funext (fun n ↦ (hs'.1 n).1)
    have hge : s'.ge = s.ge := funext (fun n ↦ (hs'.1 n).2)
    have extensionality (x y : CategoryTheory.Triangulated.TStructure
        (generalAlgebraicallyClosedConstructibleCategory l Ω Y))
        (h₁ : x.le = y.le) (h₂ : x.ge = y.ge) : x = y := by
      cases x
      cases y
      congr 1
    exact extensionality s' s hle hge

/-- The bounded standard t-structure on the actual common-stage category.
Source: blueprint order 1506 (blueprint: def-weil-constructible-heart). -/
def sfCommonStageStandardTStructure :=
  (sfCommonStageStandardTStructure_existsUnique l Y Ω D hl).exists.choose

/-- Rational truncation and abelianity clauses of the constructible-heart definition.
Source: blueprint order 1506 (blueprint: def-weil-constructible-heart).
Proof: the prescribed zero classes identify the heart. The standard t-structure
truncation criteria give the two equivalences, and the heart of a t-structure on a
triangulated category is abelian. Transport along the equality of heart predicates. -/
theorem sfRationalHeart_properties :
    (sfRationalStandardTStructure l E Y D hl).heart = sfRationalHeartProperty l E Y ∧
      (∀ K : sfRationalConstructibleCategory l E Y,
        (sfRationalStandardClass l E Y true 0 K ↔
          IsZero (((sfRationalStandardTStructure l E Y D hl).truncGE 1).obj K)) ∧
        (sfRationalStandardClass l E Y false 0 K ↔
          IsZero (((sfRationalStandardTStructure l E Y D hl).truncLE (-1)).obj K))) ∧
      Nonempty (Abelian (sfRationalHeart l E Y)) := by
  let t := sfRationalStandardTStructure l E Y D hl
  have hclasses : ∀ n : ℤ, t.le n = sfRationalStandardClass l E Y true n ∧
      t.ge n = sfRationalStandardClass l E Y false n :=
    (sfRationalStandardTStructure_existsUnique l E Y D hl).exists.choose_spec.1
  have hheart : t.heart = sfRationalHeartProperty l E Y := by
    change t.le 0 ⊓ t.ge 0 = _
    rw [(hclasses 0).1, (hclasses 0).2]
    rfl
  refine ⟨hheart, ?_, ?_⟩
  · intro K
    constructor
    · rw [← (hclasses 0).1, t.le_iff_isLE]
      exact t.isLE_iff_isZero_truncGE_obj 0 1 rfl K
    · rw [← (hclasses 0).2, t.ge_iff_isGE]
      exact t.isGE_iff_isZero_truncLE_obj (-1) 0 rfl K
  · change Nonempty (Abelian (sfRationalHeartProperty l E Y).FullSubcategory)
    rw [← hheart]
    let := t.hasHeartFullSubcategory
    exact ⟨t.abelianHeart t.heart.FullSubcategory⟩

/-- Common-stage truncation and abelianity clauses.
Source: blueprint order 1506 (blueprint: def-weil-constructible-heart).
Proof: identify the zero classes with the unique standard t-structure's heart, apply
its two truncation-vanishing criteria, and transport the heart's abelian structure. -/
theorem sfCommonStageHeart_properties :
    (sfCommonStageStandardTStructure l Y Ω D hl).heart = sfCommonStageHeartProperty l Y Ω ∧
      (∀ K : generalAlgebraicallyClosedConstructibleCategory l Ω Y,
        (sfCommonStageStandardClass l Y Ω true 0 K ↔
          IsZero (((sfCommonStageStandardTStructure l Y Ω D hl).truncGE 1).obj K)) ∧
        (sfCommonStageStandardClass l Y Ω false 0 K ↔
          IsZero (((sfCommonStageStandardTStructure l Y Ω D hl).truncLE (-1)).obj K))) ∧
      Nonempty (Abelian (sfCommonStageHeart l Y Ω)) := by
  let t := sfCommonStageStandardTStructure l Y Ω D hl
  have hclasses : ∀ n : ℤ, t.le n = sfCommonStageStandardClass l Y Ω true n ∧
      t.ge n = sfCommonStageStandardClass l Y Ω false n :=
    (sfCommonStageStandardTStructure_existsUnique l Y Ω D hl).exists.choose_spec.1
  have hheart : t.heart = sfCommonStageHeartProperty l Y Ω := by
    change t.le 0 ⊓ t.ge 0 = _
    rw [(hclasses 0).1, (hclasses 0).2]
    rfl
  refine ⟨hheart, ?_, ?_⟩
  · intro K
    constructor
    · rw [← (hclasses 0).1, t.le_iff_isLE]
      exact t.isLE_iff_isZero_truncGE_obj 0 1 rfl K
    · rw [← (hclasses 0).2, t.ge_iff_isGE]
      exact t.isGE_iff_isZero_truncLE_obj (-1) 0 rfl K
  · change Nonempty (Abelian (sfCommonStageHeartProperty l Y Ω).FullSubcategory)
    rw [← hheart]
    let := t.hasHeartFullSubcategory
    exact ⟨t.abelianHeart t.heart.FullSubcategory⟩

end WeilConjectures
