module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing

import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Sheaf.AlgebraicGeometry.NoetherianImageBoundaryDvr

/-!
# DVR lifts close an immersion in a proper domination diagram

Source: Stacks Project, limits.tex, Tag 0208, equation-solid and the final contradiction,
with an arbitrary Noetherian separated ambient scheme in place of projective space.
(blueprint: lem-sfb-dvr-proper-domination-closed-immersion)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- An immersion into a Noetherian scheme separated over the base is closed if its source
is quasi-compact and proper over a scheme satisfying existence of DVR lifts over that base.

Source: Stacks Project, limits.tex, Tag 0208 (lemma-Noetherian-dvr-valuative-proper),
equation-solid and final contradiction, extracted for an arbitrary ambient scheme.
(blueprint: lem-sfb-dvr-proper-domination-closed-immersion)

Proof:
1. The locally Noetherian scheme P is quasi-separated
   [lem-weil-pbc-locally-noetherian-quasi-separated]. Since Y is quasi-compact, i is
   quasi-compact [lem-weil-pbc-qcqs-morphism-permanence]. An immersion is locally of
   finite type [lem-weil-pbc-immersion-base-change-lft], so i is of finite type
   [def-weil-finite-type-morphism].
2. If the image of i were not closed, choose p in its closure outside its image.
   The boundary-DVR lemma [lem-sfb-noetherian-image-boundary-dvr] gives a DVR A with
   fraction field K, u : Spec K → Y and v : Spec A → P, whose generic restrictions
   agree after i and whose closed point maps to p.
3. Apply the assumed DVR existence for f to a = u ≫ π and b = v ≫ q. The square
   commutes by comm, so obtain h : Spec A → X with h ≫ f = b and j ≫ h = u ≫ π.
4. Properness of π gives w : Spec A → Y with w ≫ π = h and j ≫ w = u
   [lemma-nagata-proper-valuative-criterion-existence-api], since a DVR is a valuation
   ring [def-sc-discrete-valuation-ring].
5. The two maps w ≫ i and v agree generically and over S. Separatedness of q makes
   them equal [lemma-nagata-separated-valuation-lift-unique]. At the closed point,
   p therefore belongs to the image of i, a contradiction.
6. The image is closed, so the immersion is a closed immersion
   [lem-weil-pbc-immersion-closed-image-closed-immersion]. -/
theorem isClosedImmersion_of_proper_domination_of_dvr_lifts
    {X Y P S : Scheme.{u}} (f : X ⟶ S) (π : Y ⟶ X) (i : Y ⟶ P) (q : P ⟶ S)
    (comm : i ≫ q = π ≫ f) [IsProper π] [IsSeparated q] [IsImmersion i]
    [CompactSpace Y] [IsLocallyNoetherian P] [CompactSpace P]
    (hDVR : ∀ (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
      (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
      (a : Spec (CommRingCat.of K) ⟶ X) (b : Spec (CommRingCat.of A) ⟶ S),
      a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ b →
      ∃ h : Spec (CommRingCat.of A) ⟶ X,
        h ≫ f = b ∧ Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ h = a) :
    IsClosedImmersion i := by
  sorry

end AlgebraicGeometry
