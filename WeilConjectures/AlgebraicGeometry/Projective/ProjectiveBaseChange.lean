/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective

/-!
# Projective morphisms are stable under base change

Source: Stacks Project, Morphisms of Schemes, Lemmas 01WF and 01K5
(blueprint: lem-pc-projective-base-change).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Projectivity of a morphism is preserved by arbitrary base change.

Source: Stacks Project, Morphisms of Schemes, Lemmas 01WF and 01K5
(blueprint: lem-pc-projective-base-change).

Proof steps (blueprint nodes in brackets): (1) unfold `IsProjective` and choose the
closed immersion into relative projective space supplied by `IsHProjective`
([def-pc-projective-morphism]); base change it along `g` using the closed-immersion
base-change statement ([lem-pc-closed-imm-base-change]), and use the canonical
identification of the resulting projective space with projective space over `S'`
([def-pc-fibre-product], [def-pc-base-change]) to obtain the H-projective factorization
of `pullback.snd f g`; (2) apply quasi-compactness stability under base change
([lem-pc-quasi-compact-base-change]) to the quasi-compact clause of `IsProjective`
([def-pc-projective-morphism]), obtaining projectivity of the projection.
-/
theorem projective_base_change {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [IsProjective f] : IsProjective (pullback.snd f g) := by
  obtain ⟨n, hn, i, hi, hif⟩ := IsHProjective.exists_isClosedImmersion (f := f)
  have w : pullback.snd f g ≫ g = (pullback.fst f g ≫ i) ≫ ℙ(n; S) ↘ S := by
    rw [Category.assoc, hif, pullback.condition]
  let i' := ProjectiveSpace.liftBaseChange (pullback.snd f g) (pullback.fst f g ≫ i) w
  have hpb : IsPullback (pullback.fst f g) i' i (ProjectiveSpace.map n g) := by
    apply ProjectiveSpace.isPullback_liftBaseChange
    rw [hif]
    exact IsPullback.of_hasPullback f g
  have hi' : IsClosedImmersion i' := MorphismProperty.of_isPullback hpb hi
  exact { exists_isClosedImmersion :=
    ⟨n, hn, i', hi', ProjectiveSpace.liftBaseChange_over _ _ _⟩ }

end AlgebraicGeometry
