/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib
public import WeilConjectures.AlgebraicGeometry.ChowLemma
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty

/-!

# The projective line, and the reduction of proper base change to it

The proof of the proper base change theorem has two halves. The geometric half is the
single computation that the projection `ℙ¹_S ⟶ S` satisfies the base change property
`AlgebraicGeometry.Etale.SatisfiesBaseChange` for every base scheme `S`; it rests on the
cohomology of curves over a separably closed field. The formal half deduces the general
theorem from that one case, using Chow's lemma
(`AlgebraicGeometry.ChowModification.nonempty_data`) to dominate an arbitrary proper
morphism by a projective one.

Both halves are stated here; the theorem they combine into is
`AlgebraicGeometry.Etale.isIso_baseChange_of_isProper` of
`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper`.

Following `AlgebraicGeometry.ProjectiveSpace`, whose index type is that of the
*homogeneous* coordinates, the projective line over `S` is `ℙ(ULift (Fin 2); S)`, with
structure morphism `ℙ(ULift (Fin 2); S) ↘ S`.

## Main statements

- `AlgebraicGeometry.Etale.satisfiesBaseChange_projectiveLine`: the projective line over
  any base satisfies the base change property.
- `AlgebraicGeometry.Etale.satisfiesBaseChange_of_isProper_of_projectiveLine`: if the
  projective line over every base satisfies the base change property, then so does every
  proper morphism.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Blueprint `sk-thm-p1`: Curve calculations ⟹ PBC(ℙ¹).

For every scheme `S`, the projection `ℙ¹_S ⟶ S` satisfies the base change property
`AlgebraicGeometry.Etale.SatisfiesBaseChange`.

By `AlgebraicGeometry.Etale.satisfiesBaseChange_iff_satisfiesInjectiveAcyclicity` it
suffices to prove injective acyclicity for the projection. Over a strictly henselian base
the degree-zero comparison between a proper scheme and its closed fibre, fed through the
Mayer–Vietoris sequence of the two standard affine charts of the projective line, kills the
cohomology of an injective sheaf in degrees `≥ 2`, and the finite-étale machinery kills it
in degree `1`. Over a general base the stalk of the exchange morphism at a geometric point
is the pullback map `Hᵠ(ℙ¹_{κ(s̄)}, F) ⟶ Hᵠ(ℙ¹_{κ(t̄)}, F)` between separably closed
fields, an isomorphism by the invariance of the cohomology of a curve under extension of
separably closed base fields; geometric stalks are conservative. -/
theorem Etale.satisfiesBaseChange_projectiveLine (S : Scheme.{u}) :
    Etale.SatisfiesBaseChange Λ (ℙ(ULift.{u} (Fin 2); S) ↘ S) :=
  sorry

/-- Blueprint `sk-thm-reduction`: Reduction to ℙ¹.

If the projection `ℙ¹_S ⟶ S` satisfies the base change property
`AlgebraicGeometry.Etale.SatisfiesBaseChange` for every scheme `S`, then so does every
proper morphism of schemes.

The base change property is étale local on the target, so the target may be assumed affine.
Chow's lemma (`AlgebraicGeometry.ChowModification.nonempty_data`) then dominates a proper
`f : X ⟶ Y` by a projective one, `π : X̃ ⟶ X` proper surjective with a closed immersion
`X̃ ↪ ℙⁿ_Y` over `Y`. Closed immersions are finite, and finite morphisms satisfy base change
because their direct image is computed by a finite product of stalks. The finite surjective
symmetric-product morphism `(ℙ¹_S)ⁿ ⟶ ℙⁿ_S` passes the hypothesis from `ℙ¹` to `ℙⁿ`.
Finally the base change property composes and cancels along proper surjections, which
disposes of `π`. -/
theorem Etale.satisfiesBaseChange_of_isProper_of_projectiveLine
    (h : ∀ S : Scheme.{u}, Etale.SatisfiesBaseChange Λ (ℙ(ULift.{u} (Fin 2); S) ↘ S))
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    Etale.SatisfiesBaseChange Λ f :=
  sorry

end AlgebraicGeometry
