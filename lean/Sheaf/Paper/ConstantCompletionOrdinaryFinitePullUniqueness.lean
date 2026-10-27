/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE.
-/
module
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.RingTheory.Ideal.Defs
public import Sheaf.Paper.ConstantCompletionCore
public import Sheaf.Paper.ConstantCompletionInverseImage
import Sheaf.Paper.ConstantCompletionOrdinaryFinitePullExistence

/-! Uniqueness for the normalized ordinary finite pullback comparison.
Source: Stacks Project, Tags 06YY and 099L.
(blueprint: lem-weil-pbc-constant-completion-ordinary-finite-pull-uniqueness).
-/
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
/-- Two isomorphisms satisfying the insertion normalization are equal.
Source: Stacks Project, Tags 06YY and 099L.
(blueprint: lem-weil-pbc-constant-completion-equivalence).
The insertion maps generate the sheafified scalar extensions, so the displayed
formula determines every component and hence the natural isomorphism. -/
theorem ordinaryFinitePull_unique
    (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ)
    (e e' : pull F (constantMap F A) ⋙ change (quotient J' A I n) ≅
        change (quotient J A I n) ⋙ pull F (constantMap F (A ⧸ I ^ (n + 1))))
    (he : ∀ M : Mod (constant J A),
      pullInsertion F (constantMap F A) M ≫
          insertion (quotient J' A I n) ((pull F (constantMap F A)).obj M) ≫
          (underlying (finite J' A I n)).map (e.hom.app M) =
        L.map (insertion (quotient J A I n) M) ≫
          pullInsertion F (constantMap F (A ⧸ I ^ (n + 1)))
            ((change (quotient J A I n)).obj M))
    (he' : ∀ M : Mod (constant J A),
      pullInsertion F (constantMap F A) M ≫
          insertion (quotient J' A I n) ((pull F (constantMap F A)).obj M) ≫
          (underlying (finite J' A I n)).map (e'.hom.app M) =
        L.map (insertion (quotient J A I n) M) ≫
          pullInsertion F (constantMap F (A ⧸ I ^ (n + 1)))
            ((change (quotient J A I n)).obj M)) : e = e' := by
  sorry
end CategoryTheory.ConstantCompletion
