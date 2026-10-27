module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Sheaf.AlgebraicGeometry.NoetherianImageBoundaryDvr

/-!
# DVR uniqueness closes the diagonal over a Noetherian base

Source: Stacks Project, limits.tex, Tag 0207
(lemma-Noetherian-dvr-valuative-separation), implication (3) to (1),
finite-type Noetherian diagonal argument.
(blueprint: lem-sfb-noetherian-dvr-closed-diagonal)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A finite-type morphism to a Noetherian scheme has closed-immersion diagonal if
any two maps from a DVR spectrum agreeing over the base and on its fraction-field
spectrum coincide.

Source: Stacks Project, limits.tex, Tag 0207
(lemma-Noetherian-dvr-valuative-separation), implication (3) to (1),
finite-type Noetherian diagonal argument.
(blueprint: lem-sfb-noetherian-dvr-closed-diagonal)

Proof:
1. Set Y = X ×_S X. The scheme X is Noetherian by
   [lem-weil-pbc-finite-type-over-noetherian]. Its projection Y → X is finite type
   by [lem-sfb-finite-type-composition-base-change](2), so Y is also Noetherian.
   The diagonal Δ is an immersion by [lem-weil-pbc-diagonal-immersion].
2. By [lem-weil-pbc-immersion-base-change-lft](2), Δ is locally of finite type.
   The inverse image of an affine open of Y is an open subscheme of X, hence
   Noetherian and quasi-compact by [lem-weil-pbc-noetherian-open-subscheme-noetherian].
   Thus Δ is quasi-compact and finite type [def-weil-finite-type-morphism].
3. If the diagonal image is not closed, choose y in its closure outside its image.
   Apply [lem-sfb-noetherian-image-boundary-dvr] to Δ to obtain a DVR A with
   fraction field K and maps a : Spec K → X and v : Spec A → Y such that
   j ≫ v = a ≫ Δ and v sends the closed point to y.
4. Compose v with the two projections to obtain h₁ and h₂. The fibre-product
   relation gives h₁ ≫ f = h₂ ≫ f, and the diagonal projection identities give
   j ≫ h₁ = a = j ≫ h₂. The hypothesis gives h₁ = h₂. By the universal property
   [def-pc-fibre-product], v = h₁ ≫ Δ. Its closed-point image then lies in the
   image of Δ, contradicting the choice of y. Hence the diagonal image is closed.
5. An immersion with closed image is a closed immersion by
   [lem-weil-pbc-immersion-closed-image-closed-immersion]. -/
theorem isClosedImmersion_diagonal_of_dvr_uniqueness
    {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [QuasiCompact f] [IsLocallyNoetherian S] [CompactSpace S]
    (huniq : ∀ (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
      (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
      (h₁ h₂ : Spec (CommRingCat.of A) ⟶ X),
      h₁ ≫ f = h₂ ≫ f →
        Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ h₁ =
          Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ h₂ → h₁ = h₂) :
    IsClosedImmersion (pullback.diagonal f) := by
  sorry

end AlgebraicGeometry
