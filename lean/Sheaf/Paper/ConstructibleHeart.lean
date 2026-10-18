/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NV
-/
module

public import Sheaf.Paper.ConstructibleStandardTStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.Heart
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import Sheaf.CategoryTheory.Triangulated.TStructure.HeartAbelianKernelSplitting

import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Preadditive.Biproducts
/-! # Constructible hearts and their standard truncations

Source: Weil conjectures blueprint, `sec-smooth-purity/sk-def-sf-admissible`,
`def-weil-constructible-heart`, order 1506 (blueprint: def-weil-constructible-heart).

The hearts are the full subcategories on the intersection of the specified standard
classes. On a finite-type geometric scheme the standard pair determines a unique
bounded t-structure; its canonical truncations give the displayed vanishing tests.
-/

@[expose] public section

set_option autoImplicit false

universe d u v

open CategoryTheory CategoryTheory.Limits

namespace WeilConjectures

section Hearts

variable (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (Y : AlgebraicGeometry.Scheme.{u})

/-- The rational heart condition is the intersection of the two standard classes.
Source: blueprint `def-weil-constructible-heart`, final display and paragraph
(blueprint: def-weil-constructible-heart). -/
def rationalConstructibleHeartProperty :
    ObjectProperty (rationalConstructibleCategory D l hl E Y) :=
  rationalConstructibleLEZero D l hl E Y ⊓ rationalConstructibleGEZero D l hl E Y

/-- The constructible E-heart, as the full subcategory of the raw rational category.
Source: blueprint `def-weil-constructible-heart`, final paragraph
(blueprint: def-weil-constructible-heart). -/
abbrev rationalConstructibleHeart :=
  (rationalConstructibleHeartProperty D l hl E Y).FullSubcategory

variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The algebraically closed heart condition uses both common-stage standard classes.
Source: blueprint `def-weil-constructible-heart`, final display and paragraph
(blueprint: def-weil-constructible-heart). -/
def algebraicallyClosedConstructibleHeartProperty :
    ObjectProperty (algebraicallyClosedConstructibleCategory D l hl Ω Y) :=
  algebraicallyClosedConstructibleLEZero D l hl Y Ω ⊓
    algebraicallyClosedConstructibleGEZero D l hl Y Ω

/-- The constructible algebraically closed heart, with the inherited full-subcategory Hom.
Source: blueprint `def-weil-constructible-heart`, final paragraph
(blueprint: def-weil-constructible-heart). -/
abbrev algebraicallyClosedConstructibleHeart :=
  (algebraicallyClosedConstructibleHeartProperty D l hl Y Ω).FullSubcategory

end Hearts

section FiniteType

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (Y : AlgebraicGeometry.Scheme.{u})
  [base : Y.Over (AlgebraicGeometry.Spec (CommRingCat.of D.k))]
  [finiteTypeLocal :
    AlgebraicGeometry.LocallyOfFiniteType (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of D.k))]
  [finiteTypeCompact :
    AlgebraicGeometry.QuasiCompact (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of D.k))]

include base finiteTypeLocal finiteTypeCompact

/-- The prescribed rational standard pair determines a unique bounded t-structure.
Source: blueprint `def-weil-constructible-heart`, standard-t-structure paragraph;
`prop-constructible-truncations`, rational coefficient clause
(blueprint: def-weil-constructible-heart).

Proof: finite type over the geometric field makes Y noetherian of finite dimension.
The integral constructible category is preserved by the ambient good truncations:
on a finite constructible stratification its cohomology sheaves are finite modules,
and the uniform reduction bounds give the common cohomological bounds. The integral
standard truncation triangles therefore lie in that full subcategory. Rationalize
these triangles and maps through the raw scalar localization. The localized Hom
formula preserves orthogonality, and taking isomorphism closures gives exactly the
stated rational classes. Thus shift stability, orthogonality and the truncation
triangle axiom hold. Each rational object has an integral representative with a finite
cohomological interval, giving boundedness. The aisle functions specify all the data
of a t-structure; the remaining fields are propositions, proving uniqueness. -/
theorem rationalConstructibleStandardTStructure_existsUnique :
    ∃! t : CategoryTheory.Triangulated.TStructure (rationalConstructibleCategory D l hl E Y),
      (∀ n : ℤ, t.le n = rationalConstructibleLE D l hl E Y n ∧
        t.ge n = rationalConstructibleGE D l hl E Y n) ∧
      ∀ K, t.bounded K := by
  sorry

/-- The unique standard t-structure; its two classes are prescribed, rather than chosen.
Source: blueprint `def-weil-constructible-heart`, standard-t-structure paragraph
(blueprint: def-weil-constructible-heart). -/
noncomputable def rationalConstructibleStandardTStructure :=
  (rationalConstructibleStandardTStructure_existsUnique D l hl E Y).exists.choose

/-- The constructible upper truncation at any integer cutoff.
Source: blueprint `def-weil-constructible-heart`, truncation paragraph
(blueprint: def-weil-constructible-heart). -/
noncomputable def rationalConstructibleTruncLE (m : ℤ) :=
  (rationalConstructibleStandardTStructure D l hl E Y).truncLE m

/-- The constructible lower truncation at any integer cutoff.
Source: blueprint `def-weil-constructible-heart`, truncation paragraph
(blueprint: def-weil-constructible-heart). -/
noncomputable def rationalConstructibleTruncGE (m : ℤ) :=
  (rationalConstructibleStandardTStructure D l hl E Y).truncGE m

/-- The rational heart is the heart of the specified standard t-structure; the two
complementary truncations give the displayed tests, and this full category is abelian.
Source: blueprint `def-weil-constructible-heart`, both displays and final paragraph
(blueprint: def-weil-constructible-heart).

Proof: the uniqueness theorem identifies the standard classes in every degree.
At zero their intersection is precisely Mathlib's t.heart. For any t-structure,
isLE_iff_isZero_truncGT_obj at zero identifies the nonpositive class with vanishing
of truncGE 1, and isGE_iff_isZero_truncLE_obj at -1 identifies the nonnegative class
with vanishing of truncLE (-1). The shift-zero isomorphism identifies the indexed
zero classes with their degree-zero definitions. Finally apply the heart-abelian
clause of prop-weil-heart-abelian to this triangulated category and this t-structure;
transport its abelian structure along the equality of the two object properties. -/
theorem rationalConstructibleHeart_properties :
    (rationalConstructibleStandardTStructure D l hl E Y).heart =
        rationalConstructibleHeartProperty D l hl E Y ∧
      (∀ K : rationalConstructibleCategory D l hl E Y,
        (rationalConstructibleLEZero D l hl E Y K ↔
          IsZero ((rationalConstructibleTruncGE D l hl E Y 1).obj K)) ∧
        (rationalConstructibleGEZero D l hl E Y K ↔
          IsZero ((rationalConstructibleTruncLE D l hl E Y (-1)).obj K))) ∧
      Nonempty (Abelian (rationalConstructibleHeart D l hl E Y)) := by
  sorry

variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The prescribed common-stage standard pair determines a unique bounded t-structure.
Source: blueprint `def-weil-constructible-heart`, standard-t-structure paragraph;
`prop-constructible-truncations`, algebraically closed coefficient clause
(blueprint: def-weil-constructible-heart).

Proof: every object, arrow and finite diagram has a common finite coefficient field.
Finite scalar extension is exact and t-exact: its ordinary completed coefficient
extension is finite free, so commutes with cohomology and the standard good
truncations, and its specified completion comparison is invertible on complete
inputs. Therefore the finite-stage standard classes are preserved by every
transition. Apply the finite-stage standard truncation to a representative. Its
triangle descends to the specified common-stage distinguished triangle. For maps
between the two classes, pass to a common stage and use finite-stage orthogonality.
Isomorphism closure makes the resulting classes exactly the two classes stated
here. Shift stability and the truncation triangle axiom follow at that same stage.
Every object has finite-stage cohomological bounds, so the t-structure is bounded.
The prescribed aisle functions determine its data uniquely, by proof irrelevance. -/
theorem algebraicallyClosedConstructibleStandardTStructure_existsUnique :
    ∃! t : CategoryTheory.Triangulated.TStructure
        (algebraicallyClosedConstructibleCategory D l hl Ω Y),
      (∀ n : ℤ, t.le n = algebraicallyClosedConstructibleLE D l hl Y Ω n ∧
        t.ge n = algebraicallyClosedConstructibleGE D l hl Y Ω n) ∧
      ∀ K, t.bounded K := by
  sorry

/-- The unique standard t-structure on the actual common-stage pair category.
Source: blueprint `def-weil-constructible-heart`, standard-t-structure paragraph
(blueprint: def-weil-constructible-heart). -/
noncomputable def algebraicallyClosedConstructibleStandardTStructure :=
  (algebraicallyClosedConstructibleStandardTStructure_existsUnique D l hl Y Ω).exists.choose

/-- Constructible upper truncation in the common-stage category at any integer.
Source: blueprint `def-weil-constructible-heart`, truncation paragraph
(blueprint: def-weil-constructible-heart). -/
noncomputable def algebraicallyClosedConstructibleTruncLE (m : ℤ) :=
  (algebraicallyClosedConstructibleStandardTStructure D l hl Y Ω).truncLE m

/-- Constructible lower truncation in the common-stage category at any integer.
Source: blueprint `def-weil-constructible-heart`, truncation paragraph
(blueprint: def-weil-constructible-heart). -/
noncomputable def algebraicallyClosedConstructibleTruncGE (m : ℤ) :=
  (algebraicallyClosedConstructibleStandardTStructure D l hl Y Ω).truncGE m

/-- The common-stage heart is the standard t-structure's heart, has the two displayed
truncation-vanishing characterizations, and is abelian.
Source: blueprint `def-weil-constructible-heart`, both displays and final paragraph
(blueprint: def-weil-constructible-heart).

Proof: the uniqueness theorem fixes every standard class. Its degree-zero
intersection is the object property defining the full heart. The two general
truncation-vanishing lemmas for t-structures give the displayed equivalences, with
cutoffs 1 and -1 respectively. Apply prop-weil-heart-abelian to the common-stage
triangulated category and transport the resulting abelian structure along the
heart-property equality. No representative or idempotent is added to this category. -/
theorem algebraicallyClosedConstructibleHeart_properties :
    (algebraicallyClosedConstructibleStandardTStructure D l hl Y Ω).heart =
        algebraicallyClosedConstructibleHeartProperty D l hl Y Ω ∧
      (∀ K : algebraicallyClosedConstructibleCategory D l hl Ω Y,
        (algebraicallyClosedConstructibleLEZero D l hl Y Ω K ↔
          IsZero ((algebraicallyClosedConstructibleTruncGE D l hl Y Ω 1).obj K)) ∧
        (algebraicallyClosedConstructibleGEZero D l hl Y Ω K ↔
          IsZero ((algebraicallyClosedConstructibleTruncLE D l hl Y Ω (-1)).obj K))) ∧
      Nonempty (Abelian (algebraicallyClosedConstructibleHeart D l hl Y Ω)) := by
  sorry

end FiniteType

section PaperCoefficients

/-- The constructible heart for a finite coefficient subfield of the fixed closure.
The field uses the dependency's specified small algebra-equivalent model; its inclusion
in Ω is the actual intermediate-field inclusion. The scheme has precisely the paper's
finite-type geometric base. Source: blueprint `def-weil-constructible-heart`, finite case
(blueprint: def-weil-constructible-heart). -/
abbrev constructibleHeart
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (Y : AlgebraicGeometry.Scheme.{u})
    [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of D.k))]
    [AlgebraicGeometry.LocallyOfFiniteType (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of D.k))]
    [AlgebraicGeometry.QuasiCompact (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of D.k))]
    (E : AlgebraicallyClosedCoefficients.Index l Ω) :=
  (rationalConstructibleStandardTStructure D l hl
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) Y).heart.FullSubcategory

/-- The constructible heart for the fixed algebraic closure on a finite-type k-scheme.
It is the full heart in the actual common-stage coefficient category.
Source: blueprint `def-weil-constructible-heart`, algebraically closed case
(blueprint: def-weil-constructible-heart). -/
abbrev constructibleHeartAlgebraicallyClosed
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (Y : AlgebraicGeometry.Scheme.{u})
    [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of D.k))]
    [AlgebraicGeometry.LocallyOfFiniteType (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of D.k))]
    [AlgebraicGeometry.QuasiCompact (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of D.k))] :=
  (algebraicallyClosedConstructibleStandardTStructure D l hl Y Ω).heart.FullSubcategory

end PaperCoefficients

end WeilConjectures
