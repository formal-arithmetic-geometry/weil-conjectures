/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.RingTheory.Ideal.Defs
public import Sheaf.Paper.ConstantCompletionCore
public import Sheaf.Paper.ConstantCompletionInverseImage
import Sheaf.Paper.ConstantCompletionDerivedPull

/-! A decomposition of the ordinary finite pullback comparison.
Source: Stacks Project, Tags 06YY and 099L.
(blueprint: lem-weil-pbc-constant-completion-ordinary-finite-pull-existence).
The existence and insertion-normalization part is isolated so that it can be
proved independently from the uniqueness argument. -/
@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace CategoryTheory.ConstantCompletion
variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
variable {C' : Type u} [SmallCategory C'] {J' : GrothendieckTopology C'}
variable {L : Sheaf J (Type u) ⥤ Sheaf J' (Type u)} (F : InverseImageData L)
variable (V : Sheaf J' (Type u) ⥤ Sheaf J (Type u)) (adj : L ⊣ V)
variable [hL : PreservesFiniteLimits L]
attribute [local irreducible] completed derivedExtension SheafOfModules.monoidalCategory
  strictLimit ordinaryUnit quotientPresentation
attribute [local irreducible] derivedPull pull change

include V adj hL in
/-- Existence of the normalized ordinary finite pullback comparison.
Source: Stacks Project, Tags 06YY and 099L.
(blueprint: lem-weil-pbc-constant-completion-equivalence).
The map is obtained by transporting the finite quotient tensor comparison through
inverse image; pure tensors with coefficient one give the displayed normalization. -/
theorem ordinaryFinitePull_exists
    (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) :
    ∃ e : pull F (constantMap F A) ⋙ change (quotient J' A I n) ≅
        change (quotient J A I n) ⋙ pull F (constantMap F (A ⧸ I ^ (n + 1))),
      ∀ M : Mod (constant J A),
        pullInsertion F (constantMap F A) M ≫
            insertion (quotient J' A I n) ((pull F (constantMap F A)).obj M) ≫
            (underlying (finite J' A I n)).map (e.hom.app M) =
          L.map (insertion (quotient J A I n) M) ≫
            pullInsertion F (constantMap F (A ⧸ I ^ (n + 1)))
              ((change (quotient J A I n)).obj M) := by
  sorry
end CategoryTheory.ConstantCompletion
