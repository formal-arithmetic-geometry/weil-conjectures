/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.AlgebraicGeometry.ChowLemma
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.SymmetricProduct
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Stability

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

By `AlgebraicGeometry.Etale.hasTorsionBaseChange_iff_hasInjectiveAcyclicity` it suffices to
prove injective acyclicity for the projection. Over a strictly henselian base the
degree-zero comparison between a proper scheme and its closed fibre, fed through the
Mayer–Vietoris sequence of the two standard affine charts of the projective line, kills the
cohomology of an injective sheaf in degrees `≥ 2`, and the finite-étale machinery kills it
in degree `1`. Over a general base the stalk of the exchange morphism at a geometric point
is the pullback map `Hᵠ(ℙ¹_{κ(s̄)}, F) ⟶ Hᵠ(ℙ¹_{κ(t̄)}, F)` between separably closed fields,
an isomorphism by the invariance of the cohomology of a curve under extension of separably
closed base fields; geometric stalks are conservative.

## The proof of the reduction

The base change property is étale local on the target
(`AlgebraicGeometry.Etale.hasTorsionBaseChange_of_jointlySurjective`), so the target may be
assumed affine. Chow's lemma then dominates a proper `f : X ⟶ Y` by a projective one
(`AlgebraicGeometry.exists_isClosedImmersion_projectiveSpace_of_isProper`): `π : X̃ ⟶ X`
proper surjective with a closed immersion `i` of `X̃` into `ℙⁿ_Y` over `Y`, and the graph
`(π, i) : X̃ ⟶ ℙⁿ_X` is a closed immersion over `X`
(`AlgebraicGeometry.ProjectiveSpace.isClosedImmersion_liftBaseChange`). Closed immersions are
finite, and finite morphisms satisfy base change
(`AlgebraicGeometry.Etale.hasTorsionBaseChange_of_isFinite`). The finite surjective
symmetric-product morphism `(ℙ¹_S)ⁿ ⟶ ℙⁿ_S`
(`AlgebraicGeometry.ProjectiveSpace.symmetricProduct`) passes the hypothesis from `ℙ¹` to
`ℙⁿ` (`AlgebraicGeometry.Etale.hasTorsionBaseChange_projectiveSpace_of_projectiveLine`).
Finally the base change property composes
(`AlgebraicGeometry.Etale.HasTorsionBaseChange.comp`) and cancels along proper surjections
(`AlgebraicGeometry.Etale.HasTorsionBaseChange.of_comp_of_surjective`), which disposes of
`π`. These stability properties are in
`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Stability`.

The reduction is stated without a noetherian hypothesis, matching
`AlgebraicGeometry.Etale.isIso_baseChange_of_isProper`, so it uses the general form of the
Chow factorisation over an affine base (the blueprint's `lemma-weil-pbc-chow-factorization`)
rather than `AlgebraicGeometry.ChowModification.isClosedImmersion_toProjectiveSpace`, which
assumes a noetherian base.

## Main statements

- `AlgebraicGeometry.Etale.hasTorsionBaseChange_projectiveLine`: the projective line over
  any base satisfies the base change property.
- `AlgebraicGeometry.Etale.hasTorsionBaseChange_projectiveSpace_of_projectiveLine`: if the
  projective line over every base satisfies the base change property, then so does every
  projective space.
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
  sorry

/-- **Products of projective lines satisfy base change**: if the projection `ℙ¹_S ⟶ S`
satisfies the base change property for every scheme `S`, then so does the product projection
`(ℙ¹_T)ⁿ ⟶ T`, which is the composite of `n` projective-line projections over the successive
bases `T, ℙ¹_T, …`. -/
theorem Etale.hasTorsionBaseChange_powOver_of_projectiveLine
    (h : ∀ S : Scheme.{u}, Etale.HasTorsionBaseChange Λ (ProjectiveLine S ↘ S))
    (T : Scheme.{u}) (n : ℕ) :
    Etale.HasTorsionBaseChange Λ (ProjectiveLine.powOver T n) := by
  induction n with
  | zero => exact Etale.hasTorsionBaseChange_of_isFinite Λ (𝟙 T)
  | succ n ih => exact (h _).comp Λ ih

/-- **Reduction of projective space to products of lines**: if the projection `ℙ¹_S ⟶ S`
satisfies the base change property for every scheme `S`, then so does the projection
`ℙⁿ_T ⟶ T` for every scheme `T` and every `n`. The product projection `(ℙ¹_T)ⁿ ⟶ T` has the
property by composition, and factors through the finite surjective symmetric-product
morphism `σₙ : (ℙ¹_T)ⁿ ⟶ ℙⁿ_T`, which has it as a finite morphism; cancellation along `σₙ`
concludes.
(blueprint: `lem-weil-pbc-reduction-projective-space`) -/
theorem Etale.hasTorsionBaseChange_projectiveSpace_of_projectiveLine
    (h : ∀ S : Scheme.{u}, Etale.HasTorsionBaseChange Λ (ProjectiveLine S ↘ S))
    (T : Scheme.{u}) (n : ℕ) :
    Etale.HasTorsionBaseChange Λ (ℙ(ULift.{u} (Fin (n + 1)); T) ↘ T) := by
  have := ProjectiveSpace.isFinite_symmetricProduct T n
  have := ProjectiveSpace.surjective_symmetricProduct T n
  refine Etale.HasTorsionBaseChange.of_comp_of_surjective Λ
    (f := ProjectiveSpace.symmetricProduct T n) (Etale.hasTorsionBaseChange_of_isFinite Λ _) ?_
  rw [ProjectiveSpace.symmetricProduct_over]
  exact Etale.hasTorsionBaseChange_powOver_of_projectiveLine Λ h T n

/-- The affine case of `AlgebraicGeometry.Etale.hasTorsionBaseChange_of_projectiveLine_of_isProper`:
Chow's factorization `f ∘ π = p ∘ i`, the closed immersion `i_X = (π, i) : X' ⟶ ℙⁿ_X` over
`X`, composition and cancellation along `π`. -/
theorem Etale.hasTorsionBaseChange_of_projectiveLine_of_isProper_of_isAffine
    (h : ∀ S : Scheme.{u}, Etale.HasTorsionBaseChange Λ (ProjectiveLine S ↘ S))
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [IsAffine Y] :
    Etale.HasTorsionBaseChange Λ f := by
  obtain ⟨X', π, n, i, hπ, hs, hi, w⟩ := exists_isClosedImmersion_projectiveSpace_of_isProper f
  -- `π ≫ f = i ≫ p_Y` satisfies the base change property
  have hπf : Etale.HasTorsionBaseChange Λ (π ≫ f) := by
    rw [← w]
    exact (Etale.hasTorsionBaseChange_of_isFinite Λ i).comp Λ
      (Etale.hasTorsionBaseChange_projectiveSpace_of_projectiveLine Λ h Y n)
  -- `π = i_X ≫ p_X` satisfies the base change property
  have hπ' : Etale.HasTorsionBaseChange Λ π := by
    let iX := ProjectiveSpace.liftBaseChange (g := f) π i w.symm
    have : IsClosedImmersion iX := inferInstance
    rw [← ProjectiveSpace.liftBaseChange_over (g := f) π i w.symm]
    exact (Etale.hasTorsionBaseChange_of_isFinite Λ iX).comp Λ
      (Etale.hasTorsionBaseChange_projectiveSpace_of_projectiveLine Λ h X n)
  exact Etale.HasTorsionBaseChange.of_comp_of_surjective Λ hπ' hπf

/-- **Reduction of proper base change to the projective line**: if the projection
`ℙ¹_S ⟶ S` satisfies `AlgebraicGeometry.Etale.HasTorsionBaseChange` for every scheme `S`,
then so does every proper morphism of schemes.

The proof is Chow's lemma: after reducing to an affine base by target locality
(`AlgebraicGeometry.Etale.hasTorsionBaseChange_of_jointlySurjective`), a proper
`f : X ⟶ Y` is dominated by a projective one,

```
       X̃ ------------> ℙⁿ_Y
       |                |
     π |                | pₙ
       v                v
       X ------ f ----> Y
```

with `π` proper surjective and the horizontal arrow a closed immersion over `Y`
(`AlgebraicGeometry.exists_isClosedImmersion_projectiveSpace_of_isProper`); the base change
property for `pₙ` comes from that of `ℙ¹` by the symmetric-product morphism
(`AlgebraicGeometry.Etale.hasTorsionBaseChange_projectiveSpace_of_projectiveLine`), and
transfers to `f` because it composes and cancels along proper surjections.
(blueprint: `prop-weil-pbc-reduction-to-projective-line`) -/
@[stacks 0A4F]
theorem Etale.hasTorsionBaseChange_of_projectiveLine_of_isProper
    (h : ∀ S : Scheme.{u}, Etale.HasTorsionBaseChange Λ (ProjectiveLine S ↘ S))
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    Etale.HasTorsionBaseChange Λ f :=
  Etale.hasTorsionBaseChange_of_jointlySurjective Λ f Y.affineCover.f
    (fun y ↦ ⟨Y.affineCover.idx y, Y.affineCover.covers y⟩)
    fun _ ↦ Etale.hasTorsionBaseChange_of_projectiveLine_of_isProper_of_isAffine Λ h _

/-- **Proper morphisms satisfy base change**: the two halves of the proof combined. -/
theorem Etale.hasTorsionBaseChange_of_isProper {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    Etale.HasTorsionBaseChange Λ f :=
  Etale.hasTorsionBaseChange_of_projectiveLine_of_isProper Λ
    (Etale.hasTorsionBaseChange_projectiveLine Λ) f

end AlgebraicGeometry
