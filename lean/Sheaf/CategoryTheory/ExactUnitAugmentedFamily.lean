/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K5
-/
module

public import Sheaf.CategoryTheory.CechLocalizationUnitModels
import Sheaf.CategoryTheory.ExactUnitDerivedTotalSquare
import Sheaf.CategoryTheory.CosimplicialInjectiveTotalReplacement

/-! # Exact-unit comparisons for strict augmented families

Source: Stacks 015F and 015J.
(blueprint: lem-sfb-exact-unit-augmented-family).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u uP vP

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.CechLocalizationUnit

/-- Apply an exact unit, a right-derived functor and an exact functor to an entire
strict augmented family, without any site or covering hypotheses.

Source: Stacks derived.tex, lemma-right-derived-exact-functor (015F) and
lemma-two-ss-complex-functor (015J); the exact-unit square and its augmentation clauses
are lem-sfb-exact-unit-derived-total-square.
(blueprint: lem-sfb-exact-unit-augmented-family).

Proof: Use one functorial nonnegative injective replacement on all point complexes,
columns, augmentations, parameter arrows and the termwise unit. Apply it separately
to the original diagram and its image under H; H need not preserve injectives.
Apply G and T termwise to these resolved diagrams. Naturality of the replacement
unit supplies their strict augmentations and strict unit map, including all mixed
parameter and cosimplicial equations. The nonnegative total of each resolved
augmentation is a quasi-isomorphism: the original augmentation is one, replacement
preserves it, and both its point and its total are bounded-below injective complexes
before applying G. The acyclic injective cone remains acyclic under G, and exact T
preserves this. The summand-normalized beta comparisons fix the displayed
AugmentedModel.total_formula. Use exact_unit_derived_total_square for G,H,T,eta.
Its normalized column maps yield sourceColumns and targetColumns; its augmentation
clause yields sourcePoint and targetPoint and the two augmentation equations. Compose
its total comparisons with G and T applied to a and to the localized total
augmentation. Its naturality clause for every parameter map yields the natural
isomorphisms sourceComparison and targetComparison. Its square gives unit_total;
its column_square gives unit_columns. The descended thetaD equals exactUnit eta:
both have the same component after precomposition with DerivedCategory.Q and the
same exact-factorization isomorphisms, so localization uniqueness identifies them.
Transport along that equality. The two normalization equations are precisely the
augmentation clause, so both comparisons retain the original augmentation. -/
theorem exact_unit_augmented_family
    {A B C : Type (u + 1)}
    [Category.{u} A] [Abelian A] [Category.{u} B] [Abelian B]
    [Category.{u} C] [Abelian C]
    [IsGrothendieckAbelian.{u} A] [IsGrothendieckAbelian.{u} B]
    [IsGrothendieckAbelian.{u} C]
    [HasDerivedCategory.{u + 1} A] [HasDerivedCategory.{u + 1} B]
    [HasDerivedCategory.{u + 1} C]
    [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions B]
    (G : A ⥤ B) [G.Additive] [PreservesFiniteLimits G]
    (T : B ⥤ C) [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (H : A ⥤ A) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (η : 𝟭 A ⟶ H)
    {P : Type uP} [Category.{vP} P]
    (M : P ⥤ DerivedCategory A) (b : AugmentedModel A P)
    (a : M ≅ b.point ⋙ QNN A) :
    Nonempty (UnitFamily G T H η M b a) := by sorry

end CategoryTheory.CechLocalizationUnit
