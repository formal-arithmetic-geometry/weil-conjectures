/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.AlgebraicGeometry.StableVersalLevelChart
import Sheaf.AlgebraicGeometry.UnpointedStableCoarseProjective
import Sheaf.AlgebraicGeometry.SmoothCurveAbelianLevelRigidification
import Sheaf.AlgebraicGeometry.FiniteEtaleNormalGenericComponents
import WeilConjectures.RingTheory.PowerSeriesNormalDomain

/-! # Freeness on normalized full abelian-level branches of a stable deformation

Source: Pikaart--de Jong, Moduli of curves with non-abelian level structure,
§§2.3.3 and 2.3.6, printed p.11; Deligne, Le lemme de Gabber, Proposition 3.5
(blueprint: lem-sfb-stable-level-versal-branch-freeness).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- A stable curve has an effective formal chart with its natural automorphism action,
and the action on the geometric closed fibre of its normalized full frame cover is free.
No invertibility hypothesis is imposed on the automorphism group's order.

Source: Pikaart--de Jong §§2.3.3 and 2.3.6; Deligne, Proposition 3.5
(blueprint: lem-sfb-stable-level-versal-branch-freeness).

Proof plan:
1. The smooth DM structure from `lem-sfb-unpointed-stable-coarse-projective`, finite
Isom spaces from `lem-sfb-stable-isom-finite-unramified`, and the completed-groupoid
presentation `lem-sfb-dm-effective-formal-stabilizer-chart` give an effective marked
formal deformation. The nodal local-to-global theorem
`lem-sfb-nodal-deformation-smoothing-parameters` supplies `3g-3` parameters, with local
node equations xy=t_i and exactly their union as discriminant. This includes d=0.
2. Completed source and target maps identify every arrow component with the formal
base, giving its H-action and the quotient description along the residual gerbe.
Finite Isom spaces algebraize the compatible family isomorphisms: a map into the
inverse limit of A/m^q is a map into A. Uniqueness gives the group law, without averaging.
3. Apply `lem-sfb-smooth-curve-abelian-level-rigidification` on the principal smooth open.
Its full frame functor is represented by a finite etale scheme, with tautological frame.
Base change of cohomology gives the natural action and its frame-preserving equation.
4. `lem-weil-pbc-power-series-normal-domain` makes A normal Noetherian. Apply
`lem-sfb-finite-etale-normal-generic-components`. The integral closure in each component
field is normal and finite by `lem-weil-pbc-integral-closure-finite-extension-normal`
and `lem-weil-pbc-noetherian-normal-separable-integral-closure-finite`. The integral
closure in the product is the product of those closures: project monic equations one
way, multiply the finitely many equations the other way. Clearing denominators shows
that its restriction to the smooth open is exactly the frame cover, densely on each
component. The generic evaluations specify the canonical inclusion used in `Chart`.
5. The action permutes the generic fields. Applying each base automorphism to the
coefficients of a monic equation preserves integrality; applying its inverse gives
equality. This extends the cover action to the specified normalization.
6. By `lem-sfb-stable-relative-picard-kummer` the pulled-back stable curve has a
separated smooth semiabelian Picard object. A primitive root and Kummer comparison
turn the tautological cohomology frame into the Picard torsion frame on the dense
smooth open. `lem-sfb-normal-base-torsion-frame-extension` extends it uniquely to an
equivariant injection into the constant rank-2g module. At a nodal fibre only an
injection is claimed, since the Picard torsion rank may decrease.
7. At a fixed geometric closed point, equivariance and trivial action on constant
labels imply trivial action on Picard torsion. Apply
`lem-sfb-stable-picard-torsion-faithfulness`, valid for singular stable curves in every
characteristic prime to ell. Faithfully flat descent along the geometric residue
field extension gives h=1 on C itself. Conversely the identity fixes every point.
Every step uses only invertibility of ell, including for wild automorphism groups. -/
theorem stable_level_versal_branch_freeness (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (g : ℕ) (hg : 2 ≤ g)
    (C : StablePointedModuli.Fiber (Spec (.of Ω)) g 0 (Over.mk (𝟙 _)))
    (d : ℕ)
    (hnodes : {x : (StablePointedModuli.fiberCurve C).left |
      ¬ ((StablePointedModuli.fiberCurve C).hom.stalkMap x).hom.FormallySmooth}.encard = d)
    (ℓ : ℕ) (hprime : ℓ.Prime) (hthree : 3 ≤ ℓ) (hinvertible : IsUnit (ℓ : Ω)) :
    ∃ D : StableVersalLevel.Chart Ω g d ℓ C,
      ∀ (K : Type u) [Field K] [IsAlgClosed K] [Algebra Ω K]
        (b : Spec (.of K) ⟶ Spec (.of (StableVersalLevel.branchRing
          (D.coverMap ≫ (StableVersalLevel.smoothOpen Ω g d D.nodeBound).ι)))),
        b ≫ StableVersalLevel.branchProjection
            (D.coverMap ≫ (StableVersalLevel.smoothOpen Ω g d D.nodeBound).ι) =
          Spec.map (CommRingCat.ofHom (algebraMap Ω K)) ≫ StableVersalLevel.closed Ω g →
        ∀ h : Aut (StablePointedModuli.fiberCurve C),
          b ≫ (D.normalAction h).hom.left = b ↔ h = 1 := by
  sorry

end AlgebraicGeometry
