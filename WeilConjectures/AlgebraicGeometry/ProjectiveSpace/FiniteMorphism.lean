/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.CoordinateSection
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfAmple

/-!
# Finite morphisms and projective morphisms

A projective morphism is presented, as in the blueprint's H-projective convention
(`def-pc-projective-morphism`), by a closed immersion `i : X ⟶ ℙ(n; S)` over `S` with a finite
type `n` of homogeneous coordinates.

* A projective morphism whose geometric fibres are finite sets is finite
  (`lem-fin-projective-finite-fibres`).
* A projective family over a Noetherian domain whose generic fibre has dimension `≤ 0` is finite
  over a nonempty open of the base (`lem-fin-projective-generically-finite`).
* A scheme finite over a projective scheme over an affine base is projective over that base
  (`lem-fin-finite-over-projective`).

The first two are consequences of Zariski's main theorem in the form
`AlgebraicGeometry.exists_isFinite_morphismRestrict_of_finite_preimage_singleton` (a proper
morphism is finite over a neighbourhood of every point with finite fibre), rather than of the
Serre-vanishing argument of the blueprint. The third embeds `Y` by the pullback of `𝒪(1)` along
the finite morphism, whose coordinate sections have affine non-vanishing loci covering `Y`.

## Main statements

- `AlgebraicGeometry.ProjectiveSpace.isFinite_of_finite_pullback`
- `AlgebraicGeometry.ProjectiveSpace.exists_isFinite_morphismRestrict_of_generic_fibre`
- `AlgebraicGeometry.ProjectiveSpace.exists_isClosedImmersion_of_isFinite`
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProjectiveSpace

variable {n : Type u} [Finite n]

/-- Blueprint `lem-fin-projective-finite-fibres`: Projective morphisms with finite fibres are
finite.

Let `f : D ⟶ T` be projective, i.e. `f = π ∘ i` for a closed immersion `i : D ⟶ ℙ(n; T)`. If
every geometric fibre `D ×_T Spec Ω`, for `Ω` algebraically closed, has only finitely many
points, then `f` is finite. The blueprint assumes `T` Noetherian; this is not needed. -/
theorem isFinite_of_finite_pullback {D T : Scheme.{u}} (f : D ⟶ T) (i : D ⟶ ℙ(n; T))
    [IsClosedImmersion i] (hi : i ≫ ℙ(n; T) ↘ T = f)
    (hfib : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T),
      Finite (pullback f t : Scheme.{u})) :
    IsFinite f := by
  sorry

/-- Blueprint `lem-fin-projective-generically-finite`: A projective family with finite generic
fibre is generically finite.

Let `A` be a Noetherian domain with fraction field `K` and `f : D ⟶ Spec A` projective. If the
generic fibre `D_K = D ×_{Spec A} Spec K` has dimension at most zero, then `f` is finite over a
nonempty open `U` of `Spec A`. -/
theorem exists_isFinite_morphismRestrict_of_generic_fibre {A : Type u} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] {D : Scheme.{u}} (f : D ⟶ Spec (.of A)) (i : D ⟶ ℙ(n; Spec (.of A)))
    [IsClosedImmersion i] (hi : i ≫ ℙ(n; Spec (.of A)) ↘ Spec (.of A) = f)
    (hD : topologicalKrullDim (pullback f
      (Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A)))) : Scheme.{u}) ≤ 0) :
    ∃ U : (Spec (.of A)).Opens, U ≠ ⊥ ∧ IsFinite (f ∣_ U) := by
  sorry

/-- Blueprint `lem-fin-finite-over-projective`: Finite covers of projective schemes are
projective.

Let `S` be affine, `f : T ⟶ S` projective, i.e. `f = π ∘ i` for a closed immersion
`i : T ⟶ ℙ(n; S)`, and `h : Y ⟶ T` finite. Then `h ≫ f` is projective: there is a closed
immersion `j : Y ⟶ ℙ(m; S)` over `S` for a finite type `m`.

The blueprint assumes `S` Noetherian and argues over an affine open of `S`; with the
H-projective convention (a closed immersion into `ℙ(m; S)` itself) the global statement needs
the base to be affine, and Noetherianity is not used. -/
theorem exists_isClosedImmersion_of_isFinite {S T Y : Scheme.{u}} [IsAffine S] (f : T ⟶ S)
    (i : T ⟶ ℙ(n; S)) [IsClosedImmersion i] (hi : i ≫ ℙ(n; S) ↘ S = f) (h : Y ⟶ T)
    [IsFinite h] :
    ∃ (m : Type u) (_ : Finite m) (j : Y ⟶ ℙ(m; S)),
      IsClosedImmersion j ∧ j ≫ ℙ(m; S) ↘ S = h ≫ f := by
  sorry

end AlgebraicGeometry.ProjectiveSpace
