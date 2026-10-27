/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.Paper.IntegralTensorPullbackData

/-! # Ordinary pullback and the actual completion augmentation

Source: blueprint det-lem-int-tensor-pullback, first paragraph; Stacks 099M.
(blueprint: lem-sfb-internal-pullback-roos-unit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralTensorPullback
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The pulled strict quotient tower has the same augmented Roos complex as the
quotient tower of the ordinary inverse image. This holds before localization and
without completeness, constructibility, or K-flatness assumptions.

Source: blueprint det-lem-int-tensor-pullback, first paragraph; strict normalization
step 8; Stacks 099M and 08TC.
(blueprint: lem-sfb-internal-pullback-roos-unit).

Proof: the monoidal coefficient-square comparison identifies the pullback of each
finite quotient module with that quotient on X, naturally in its coefficient
module. Compose this with the strong monoidal tensor comparison to identify
F(P tensor A_n) with F(P) tensor A_n in each degree. Naturality in the quotient
map identifies consecutive transitions, and monoidal unit compatibility identifies
the quotient augmentations. Take the product of these level isomorphisms. It
intertwines 1 minus shift, hence induces the diagonal mapping-cocone isomorphism.
Convert the mapping cocone to the explicit completion coordinates (x,-y); its
second coordinate differential is (1-shift)x-dy. Both augmentations have zero
second coordinate and the same first coordinate, proving the asserted equality.
The argument applies unchanged to zero complexes, empty schemes, and identity
morphisms. -/
theorem ordinary_roos_unit {X Y : Scheme.{u}} (g : X ⟶ Y)
    (P : CochainComplex (AdicCompletion.Modules l E Y) ℤ) :
    ∃ e : WeilConjectures.integralOperationsRoos (pulledTower l E g P) ≅
        AdicCompletion.roos l E X
          (((CondensedRing.upperStar (DerivedNakayama.integerRing l E) g).mapHomologicalComplex
            (.up ℤ)).obj P),
      comparison l E g P ≫ e.hom =
        AdicCompletion.augmentation l E X
          (((CondensedRing.upperStar (DerivedNakayama.integerRing l E) g).mapHomologicalComplex
            (.up ℤ)).obj P) := by sorry

end AlgebraicGeometry.ProEtale.IntegralTensorPullback
