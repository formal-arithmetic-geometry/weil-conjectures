/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V6
-/
module

public import Sheaf.Paper.PurAdicLineSystemData

/-! # Localization of semilinear pair comparisons

Source: the Integral twist and Rational and algebraic closure paragraphs of the
main-20261015 coefficient-twists proof (blueprint: lem-pur-adic-localization-comparison).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

universe w uC vC uD vD

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- Localization of a semilinear diagram comparison, including naturality in the index
and uniqueness among normalized semilinear isomorphisms.

Source: the rational-and-algebraic-closure paragraph of the coefficient-twists proof;
Stacks Modules on Sites, Tags 03CY and 03CZ; Algebra, Tag 00DK.
(blueprint: lem-pur-adic-localization-comparison)

Proof: construct each localized ring by sheafifying its sectionwise fraction ring and
each localized module by sheafifying its module of fractions. Its restriction of scalars
is tensor localization, with m/1 identified with m tensor 1. The universal fraction maps
extend every transition map uniquely and give a diagram of pairs. The scalar section is
preserved under t, so its inverse image identifies the two sequential diagrams used for
module localization. Inverse image preserves their colimits, giving invertible module
comparisons; the fraction-ring mapping property gives the coefficient comparisons.
Their scalar compatibility is checked on fractions, and hence locally after
sheafification. Maps out of localization are fixed by their values on the unit, since
multiplication by the denominator is invertible. This proves naturality and both
uniqueness assertions. This argument includes zero rings and nilpotent denominators. -/
theorem purAdicLocalizationComparison_exists
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasSheafify J CommRingCat.{w}]
    [HasSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasSheafify K CommRingCat.{w}]
    (L : Sheaf J (Type w) ⥤ Sheaf K (Type w))
    (V : Sheaf K (Type w) ⥤ Sheaf J (Type w)) (adj : L ⊣ V)
    [PreservesFiniteLimits L]
    {I : Type w} [PartialOrder I]
    (A : PurAdicPairDiagram.{w} J I) (B : PurAdicPairDiagram.{w} K I)
    (t : PurAdicPairComparison L A B)
    (s : ∀ i : I, ((A.R.obj i).obj ⋙ forget CommRingCat.{w}).sections)
    (s' : ∀ i : I, ((B.R.obj i).obj ⋙ forget CommRingCat.{w}).sections)
    (hs : ∀ {i j : I} (h : i ≤ j) (W : Cᵒᵖ),
      (A.R.map (homOfLE h)).hom.app W ((s i).val W) = (s j).val W)
    (hsection : ∀ i : I, IsInverseImageSection.{w, uC, vC, uD, vD} (t.a i) (s i) (s' i)) :
    ∃ (Q : PurAdicLocalization A s) (Q' : PurAdicLocalization B s')
      (d : PurAdicPairComparison L Q.pairs Q'.pairs),
      PurAdicLocalizationNormalized L t Q Q' d ∧
      (∀ d' : PurAdicPairComparison L Q.pairs Q'.pairs,
        PurAdicLocalizationNormalized L t Q Q' d' →
        ∀ i : I, (d'.a i).ringUnderlying = (d.a i).ringUnderlying ∧
          purAdicModuleIso L Q.pairs Q'.pairs i (d'.a i) (d'.c i) =
            purAdicModuleIso L Q.pairs Q'.pairs i (d.a i) (d.c i)) := by
  sorry

end CategoryTheory
