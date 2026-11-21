/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import WeilConjectures.CategoryTheory.DeltaFunctor
import WeilConjectures.CategoryTheory.EffaceableDeltaFunctorUniversal
import WeilConjectures.CategoryTheory.Abelian.HorseshoeDeltaFunctor

/-!
# Right derived functors form a universal delta-functor

Source: Stacks Project, Derived Categories, Lemmas 015B (2), (4) and 05TE.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory.Limits

namespace CategoryTheory

/-- The right derived functors of a left exact additive functor carry connecting maps
making them a universal cohomological delta-functor, and degree zero is naturally
isomorphic to the original functor.

Source: Stacks Project, Derived Categories, Lemmas 015B (2), (4) and 05TE.

Proof:
1. Choose injective resolutions and lift each morphism to a chain map. The sum of lifts
lifts the sum, so additivity of the functor and homology makes every right derived functor
additive.
2. Left exactness identifies the degree-zero homology of the image resolution with the
original object image. Lifts respect the augmentations, so these identifications are
natural.
3. A short exact sequence, viewed as complexes concentrated in degree zero, gives a
natural distinguished triangle.
4. Apply the triangulated right derived functor, using its natural shift isomorphism.
5. Take the long exact cohomology sequence and transport along the natural identification
with the right derived functors on objects. These give the connecting maps.
6. The degree-zero identification and left exactness make the initial map monic.
7. Naturality of the cohomology ladder and the identifications makes the connecting maps
natural.
8. Additivity, exactness including the initial zero, and naturality give the required
delta-functor.
9. Embed each object into an injective. Positive right derived functors vanish on it,
so the induced map effaces each positive degree.
10. Effaceability implies universality by Homology, Lemma 010T. -/
theorem Functor.exists_universal_rightDerived_deltaFunctor
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Abelian A]
    [EnoughInjectives A] [Category.{v₂} B] [Abelian B]
    (v : A ⥤ B) [v.Additive] [PreservesFiniteLimits v] :
    ∃ G : CohomologicalDeltaFunctor A B,
      G.F = (fun n : ℕ ↦ v.rightDerived n) ∧ G.IsUniversal ∧
        Nonempty (v.rightDerived 0 ≅ v) := by
  obtain ⟨G, hG, _⟩ := exists_horseshoe_rightDerived_deltaFunctor v
  refine ⟨G, hG, effaceable_deltaFunctor_isUniversal G ?_, ⟨v.rightDerivedZeroIsoSelf⟩⟩
  intro n hn X
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  refine ⟨Injective.under X, Injective.ι X, inferInstance, ?_⟩
  rw [hG]
  exact (v.isZero_rightDerived_obj_injective_succ m (Injective.under X)).eq_of_tgt _ _

end CategoryTheory
