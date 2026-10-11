/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Reduction
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk

/-!

# The projective line, and the reduction of proper base change to it

The proof of the proper base change theorem has two halves. The geometric half is the single
computation that the projection `ℙ¹_S ⟶ S` (`AlgebraicGeometry.ProjectiveLine`) satisfies
the base change property `AlgebraicGeometry.Etale.HasTorsionBaseChange` for every base
scheme `S`; it rests on the cohomology of curves over a separably closed field. The formal
half deduces the general theorem from that one case, using Chow's lemma to dominate an
arbitrary proper morphism by a projective one.

Both halves are stated here and combined into
`AlgebraicGeometry.Etale.hasTorsionBaseChange_of_isProper`, from which
`AlgebraicGeometry.Etale.isIso_baseChange_of_isProper` of
`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper` is derived.

## The proof of the projective-line case

By `AlgebraicGeometry.Etale.hasTorsionBaseChange_of_hasInjectiveAcyclicity` it suffices to
prove injective acyclicity for the projection, which is
`AlgebraicGeometry.Etale.hasInjectiveAcyclicity_projectiveLine` of
`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk`. The
Lean proof checks that the exchange morphism is an isomorphism at every geometric point, since
geometric stalks are conservative. There, by
`AlgebraicGeometry.Etale.exists_addEquiv_sheafFiber_baseChangeHomologyMap_projectiveLine`, the
stalk is the pullback map `Hᵠ(ℙ¹_{κ(s̄)}, F) ⟶ Hᵠ(ℙ¹_{κ(t̄)}, F)` between two separably closed
fields. That map is bijective by the invariance of the cohomology of a curve under extension
of separably closed base fields. The strictly henselian route of
`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian`
(Mayer–Vietoris on the two standard charts, finite étale lifting) is not used by the Lean
proof; it is the intended proof of the `sorry`ed stalk statement, through the comparison of
`ℙ¹` over a strictly henselian ring with its closed fibre.

## The proof of the reduction

The base change property is étale local on the target, so the target may be assumed affine.
Chow's lemma then dominates a proper `f : X ⟶ Y` by a projective one: `π : X̃ ⟶ X` proper
surjective with a closed immersion of `X̃` into `ℙⁿ_Y` over `Y`. Closed immersions are
finite, and finite morphisms satisfy base change unrestrictedly
(`AlgebraicGeometry.Etale.isBaseChangeIso_of_isFinite`, whence
`AlgebraicGeometry.Etale.hasTorsionBaseChange_of_isBaseChangeIso`). The finite surjective
symmetric-product morphism `(ℙ¹_S)ⁿ ⟶ ℙⁿ_S` passes the hypothesis from `ℙ¹` to `ℙⁿ`.
Finally the base change property composes and cancels along proper surjections, which
disposes of `π`.

## Prerequisites not yet formalised

The reduction is stated without a noetherian hypothesis, matching
`AlgebraicGeometry.Etale.isIso_baseChange_of_isProper`. The Chow factorisation available in
this repository, `AlgebraicGeometry.ChowModification.nonempty_data` together with
`AlgebraicGeometry.ChowModification.isClosedImmersion_toProjectiveSpace`, assumes a
noetherian base. Closing the gap is the blueprint's `lemma:weil-pbc-chow-factorization`,
which removes the hypothesis by a finite-presentation envelope and noetherian approximation;
it is a prerequisite of the proof below and is not formalised yet.

The reduction also absorbs several steps which the blueprint keeps separate — target
locality, stability under composition, and cancellation along a proper surjection (Stacks
Project, Tags 0A4D and 0A4C) — none of which is stated on its own here.

## Main statements

- `AlgebraicGeometry.Etale.hasTorsionBaseChange_projectiveLine`: the projective line over
  any base satisfies the base change property.
- `AlgebraicGeometry.Etale.hasTorsionBaseChange_of_projectiveLine_of_isProper`: if the
  projective line over every base satisfies the base change property, then so does every
  proper morphism.
- `AlgebraicGeometry.Etale.hasTorsionBaseChange_of_isProper`: every proper morphism
  satisfies the base change property.

## References

- Stacks Project, Lemma 59.91.10, the reduction to the projective line,
  <https://stacks.math.columbia.edu/tag/0A4F>
- Stacks Project, Theorem 59.91.11, whose proof is the projective-line computation,
  <https://stacks.math.columbia.edu/tag/095T>
- [SGA 4, Exp. XII, Théorème 5.1]

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **The projective line satisfies base change**: for every scheme `S`, the projection
`ℙ¹_S ⟶ S` satisfies `AlgebraicGeometry.Etale.HasTorsionBaseChange`, that is, for every
cartesian square

```
ℙ¹_T --g'--> ℙ¹_S
  |            |
  p'           p
  v            v
  T ---g-----> S
```

the derived base change map is an isomorphism on every bounded below complex with torsion
cohomology. This is the geometric half of the proof of proper base change; see the module
docstring, and Stacks Project, Tag 095T, whose proof it is.
(blueprint: `prop:weil-pbc-projective-line`) -/
theorem Etale.hasTorsionBaseChange_projectiveLine (S : Scheme.{u}) :
    Etale.HasTorsionBaseChange Λ (ProjectiveLine S ↘ S) :=
  Etale.hasTorsionBaseChange_of_hasInjectiveAcyclicity Λ _ fun _ _ ↦
    Etale.hasInjectiveAcyclicity_projectiveLine _ S

/-- **Proper morphisms satisfy base change**: the two halves of the proof combined. -/
theorem Etale.hasTorsionBaseChange_of_isProper {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    Etale.HasTorsionBaseChange Λ f :=
  Etale.hasTorsionBaseChange_of_projectiveLine_of_isProper Λ
    (Etale.hasTorsionBaseChange_projectiveLine Λ) f

end AlgebraicGeometry
