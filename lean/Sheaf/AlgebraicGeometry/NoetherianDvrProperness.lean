module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

import Mathlib.AlgebraicGeometry.ValuativeCriterion
import WeilConjectures.AlgebraicGeometry.ChowLemma
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace

/-!
# Noetherian DVR criterion for properness

Source: Stacks Project, limits.tex, Tag 0208, equivalence (1) and (3).
(blueprint: lem-sfb-noetherian-dvr-properness)
-/

public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- For a finite-type morphism to a locally Noetherian scheme, properness is equivalent to
unique lifting of every square from a DVR and its fraction field. There is no excellence,
finite-type condition on the DVR, or generic-image restriction.

Source: Stacks Project, limits.tex, Tag 0208, equivalence (1) and (3).
(blueprint: lem-sfb-noetherian-dvr-properness)

Proof:
1. Properness gives the unique lift by the valuative criterion
   [lemma-nagata-proper-separated-valuation-extension], since every DVR is a valuation ring.
2. Conversely, pass to an affine Noetherian open cover of S [pqf-def-locnoeth]. Finite type
   survives base change [lem-sfb-finite-type-composition-base-change]. Lifting survives because
   the lift to X and the prescribed map to the open base induce a unique map to the fibre
   product [def-pc-fibre-product]. Properness is local on the target
   [lemma-nagata-projective-target-local]. Thus assume S affine Noetherian; X is Noetherian
   [lem-weil-pbc-finite-type-over-noetherian].
3. The fibre square T = X ×_S X is Noetherian by finite-type base change and composition.
   Its diagonal is an immersion [lem-weil-pbc-diagonal-immersion], hence locally of finite
   type [lem-weil-pbc-immersion-base-change-lft]. Since X is quasi-compact and T is
   quasi-separated [lem-weil-pbc-locally-noetherian-quasi-separated], the diagonal is
   quasi-compact [lem-weil-pbc-qcqs-morphism-permanence], hence of finite type.
4. A boundary point of the diagonal image yields a DVR square for the diagonal by
   [lem-sfb-noetherian-image-boundary-dvr]. Its two projections to X agree on the generic
   point and over S, so unique lifting for f makes them equal. The square then factors
   through the diagonal, contradicting the boundary point. Its image is closed, and
   [lem-weil-pbc-immersion-closed-image-closed-immersion] makes the diagonal closed.
   Thus f is separated [def-weil-proper-morphism].
5. Chow's lemma [lem-weil-pbc-chow-noetherian] gives a proper surjective map π : X' → X
   and an immersion i : X' → P into projective space over S, with i followed by q : P → S
   equal to π followed by f. The map q is proper
   [lemma-nagata-projective-space-base-change-proper]. Both X' and P are Noetherian by
   finite-type composition and [lem-weil-pbc-finite-type-over-noetherian]. Birationality of
   π is not needed, because the hypothesis tests every DVR square.
6. The immersion i is locally of finite type and quasi-compact, since X' is quasi-compact
   and P is quasi-separated [lem-weil-pbc-qcqs-morphism-permanence]. If its image is not
   closed, [lem-sfb-noetherian-image-boundary-dvr] gives u : Spec K → X' and v : Spec R → P
   agreeing after restriction and i, with the closed point sent outside the image of i.
7. Apply existence of lifting for f to πu and qv to get h : Spec R → X. Properness of π
   gives a lift w : Spec R → X' extending u and mapping to h
   [lemma-nagata-proper-separated-valuation-extension]. The maps iw and v agree over S
   and on Spec K, so separatedness of q makes them equal
   [lemma-nagata-separated-valuation-lift-unique]. Their closed-point images contradict
   the choice of v. Hence the image of i is closed.
8. The immersion i is closed [lem-weil-pbc-immersion-closed-image-closed-immersion], so
   qi = fπ is proper [lem-weil-pbc-closed-immersion-proper]. Universal closedness descends
   along the surjection π [lem-weil-pbc-image-universally-closed]. Together with separatedness
   and finite type this proves f proper [def-weil-proper-morphism]; step 2 returns to S. -/
theorem isProper_iff_unique_dvr_lift {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] [QuasiCompact f] :
    IsProper f ↔
      ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
        (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
        (a : Spec (CommRingCat.of K) ⟶ X) (b : Spec (CommRingCat.of R) ⟶ S),
        a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ b →
          ∃! l : Spec (CommRingCat.of R) ⟶ X,
            l ≫ f = b ∧ Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ l = a := by
  sorry

end AlgebraicGeometry
