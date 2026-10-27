/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y8
-/
module

public import Sheaf.SixFunctors.AugmentedStrictIntegralCompletion

/-! # OpenExactPullbackLocalization

Source: Stacks Project, proetale.tex, Tag 099N (2),(5), and sites-cohomology.tex,
Tags 0G7E and 07A4 (blueprint: lem-sf-open-exact-pullback-localization).
The index n denotes exponent n+1. Site and coefficient universes are independent.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.OpenQuotientCompletion
open CompletedTowerIndependent

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

variable {V W : Scheme.{t}} (e : V ⟶ W) [IsOpenImmersion e]
  (o : IntegralOpenReduction.Operations l E e)

attribute [local irreducible] restrict HasDerivedCategory.standard

/-- Actual module inverse image at an open is exact slice restriction, with
its graph-generator normalization.
Source: Stacks Project, Tags 03D2, 00VC, 09BN and 099N
(blueprint: lem-sf-open-exact-pullback-localization).
Proof: the slice-to-open site equivalence identifies inverse image at the monic
open object with evaluation on the slice. The completed coefficient structure
map is the projection-normalized coefficient identification. Transport modules
through that identification. The ringed inverse-image tensor comparison gives
an isomorphism from the actual pullback to restrict. The unit generator at Z,
restricted along the distinguished graph, is sent to the section x; this is the
ordinary_normalized equation, with the chosen coefficient equivalence's counit.
This assertion involves neither quotient tensor descent nor inverse limits.
For an identity open its generator equation fixes the identity comparison, and
for the empty open both functors take values in the zero module category. The
argument is exact for arbitrary unbounded complexes and non-quasi-compact opens. -/
theorem openExactPullbackLocalization :
    ∃ ordinary : pull l E e ≅ restrict l E e o,
      ∀ (M : Modules l E W)
        (Z : Over (IntegralOpenReduction.openObject e)) (x : M.val.obj (op Z.left)),
        (ordinary.hom.app M).val.app (op ((IntegralOpenReduction.sliceSite e).obj Z))
          (((pull l E e).obj M).val.map (sliceGraph e Z).op
            (((adjunction l E e).unit.app M).val.app (op Z.left) x)) =
          restrictionSection l E e o M Z x := by
  sorry

end WeilConjectures.OpenQuotientCompletion
