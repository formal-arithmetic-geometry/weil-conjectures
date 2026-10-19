/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.Paper.ConstructibleHeart
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
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
  sorry

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
  sorry

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
