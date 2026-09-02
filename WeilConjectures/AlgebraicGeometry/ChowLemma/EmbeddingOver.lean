/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.AlgebraicGeometry.ChowLemma
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.BaseChange

/-!
# The Chow embedding over the source

For a proper morphism `f : X ⟶ S` over a Noetherian base, Chow's lemma provides the Chow
modification `π : X' ⟶ X` together with a closed immersion `ι : X' ⟶ ℙ(n; S)` over `S`. The
pair `(π, ι)` is a morphism `X' ⟶ X ×_S ℙ(n; S) = ℙ(n; X)` over `X`
(`AlgebraicGeometry.ChowModification.toProjectiveSpaceOver`), and it is a closed immersion
(`AlgebraicGeometry.ChowModification.isClosedImmersion_toProjectiveSpaceOver`): composed with
the base change `ℙ(n; X) ⟶ ℙ(n; S)` of `f`, which is separated, it is the closed immersion `ι`.
This is the form of Chow's lemma used in the reduction of proper base change to the
projective line.

-/

@[expose] public section

universe u

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.ChowModification

section

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [IsSeparated f] [LocallyOfFiniteType f]
  [QuasiCompact f]

/-- The Chow modification `X'` of `f : X ⟶ S`, embedded into the projective space over `X`:
the morphism `(π, ι) : X' ⟶ X ×_S ℙ(n; S) = ℙ(n; X)`. -/
def toProjectiveSpaceOver : ChowModification f ⟶ ℙ(index f; X) :=
  ProjectiveSpace.lift (modificationMap f) (toProjectiveSpace f) (toProjectiveSpace_over f).symm

/-- `toProjectiveSpaceOver f` is a morphism over `X`. -/
@[reassoc (attr := simp)]
lemma toProjectiveSpaceOver_over :
    toProjectiveSpaceOver f ≫ ℙ(index f; X) ↘ X = modificationMap f :=
  ProjectiveSpace.lift_over _ _ _

/-- `toProjectiveSpaceOver f` composed with the base change `ℙ(n; X) ⟶ ℙ(n; S)` of `f` is the
immersion `toProjectiveSpace f : X' ⟶ ℙ(n; S)`. -/
@[reassoc (attr := simp)]
lemma toProjectiveSpaceOver_map :
    toProjectiveSpaceOver f ≫ ProjectiveSpace.map (index f) f = toProjectiveSpace f :=
  ProjectiveSpace.lift_map _ _ _

/-- The base change `ℙ(n; X) ⟶ ℙ(n; S)` of a separated morphism `f` is separated. -/
instance isSeparated_map : IsSeparated (ProjectiveSpace.map (index f) f) :=
  MorphismProperty.of_isPullback (ProjectiveSpace.isPullback_map (index f) f).flip ‹_›

end

/-- **The Chow embedding over `X`** (blueprint: `lemma:weil-pbc-chow-embedding-over-x`): for
`f : X ⟶ S` proper, the morphism `(π, ι) : X' ⟶ ℙ(n; X)` is a closed immersion, since composed
with the separated base change `ℙ(n; X) ⟶ ℙ(n; S)` of `f` it is the closed immersion `ι`. -/
instance isClosedImmersion_toProjectiveSpaceOver {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S]
    [IsProper f] :
    IsClosedImmersion (toProjectiveSpaceOver f) := by
  have : IsClosedImmersion (toProjectiveSpaceOver f ≫ ProjectiveSpace.map (index f) f) := by
    rw [toProjectiveSpaceOver_map]
    infer_instance
  exact IsClosedImmersion.of_comp _ (ProjectiveSpace.map (index f) f)

end AlgebraicGeometry.ChowModification

end
