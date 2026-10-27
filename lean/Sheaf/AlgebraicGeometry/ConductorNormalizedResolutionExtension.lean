/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.AlgebraicGeometry.ConductorResolutionPreparation
import Sheaf.AlgebraicGeometry.ConductorResolutionComparison
import Sheaf.AlgebraicGeometry.NormalizedResolutionComparisonLaws

/-! # Extending normal-input resolution by the conductor stage

Source: ILO VIII 2.2.3--2.2.9, 2.3.4--2.3.5(i), 2.3.12(i).
(blueprint: lem-trf-conductor-extension-of-normalized-resolution).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Extend any given smooth-functorial normal-input rule by exactly the conductor stage.
The output rule includes coherent nonempty nowhere dense centers, regular termination,
triviality on the empty scheme, canonical cartesian smooth comparisons, ordered unit-stage
deletion by isomorphisms, identities, composition and no deletion for surjective maps.
Source: ILO VIII 2.2.3--2.2.9, 2.3.4--2.3.5(i), 2.3.12(i), pp.90--93
(blueprint: lem-trf-conductor-extension-of-normalized-resolution).

Proof (node steps 1--8):
1. Finite-type rational inputs are Noetherian; all smooth maps here are quasi-compact,
using lem-weil-pbc-finite-type-over-noetherian and
lem-weil-pbc-noetherian-open-subscheme-noetherian.
2. Use lem-trf-conductor-smooth-base-change and lem-trf-normalized-blowup-calculus for
the conductor geometry and normal preparation, as in rationalConductor_geometry.
3. For nonunit conductor prepend P(X) → X to N(P(X)); for unit conductor omit it and
transport along P(X) ≅ X. A proper ideal has a nonempty zero scheme because a proper
stalk ideal lies in its maximal ideal. The tail gives regular termination. The empty
input has unit conductor, empty preparation and trivial N; length-zero tails are allowed.
4. For a smooth h use rationalConductor_smoothBaseChange to identify P(Y) with the
pullback of P(X); its induced map is smooth, so N's comparison applies.
5. If D_X is unit, omit both initial stages. If both conductors are nonunit, retain
the conductor stage. If only D_Y is unit, delete its pulled-back stage: Y is normal,
so the unit normalized blowup is an isomorphism by the normalized-blowup calculus.
6. Apply N's comparison to the smooth normal-input map. Induct through the finite tail,
extending the same next ideal and forming the same normalized blowup. Preserve all
nonunit ideals in order; unit tail stages have normal bases and hence are isomorphisms.
7. Conductor and normalized-blowup comparisons respect identities and composition.
Together with N's laws these identify actual level maps. Ideal extension is associative
and units stay unit, so two successive ordered deletions equal one deletion for a composite.
8. For surjective h a point above a conductor-center point has proper extended conductor
stalk, since the stalk map is local. Thus that stage survives. Surjective base change
(lem-weil-pbc-surjective-base-change) makes P(Y) → P(X) surjective, so N deletes no tail
stage. This includes the empty-to-empty case and disconnected inputs. -/
theorem conductor_normalizedResolution_extension
    (N : SmoothNormalizedResolutionRule NormalRationalResolutionInput.{u}
      (fun X ↦ X.val.scheme)) :
    ∃ H : SmoothNormalizedResolutionRule RationalResolutionInput.{u} (fun X ↦ X.scheme),
      ∀ X : RationalResolutionInput.{u}, Nonempty (IsRationalConductorResolutionExtension X
        (N.tower (normalConductorPreparedRationalInput X)) (H.tower X)) := by
  classical
  let T := fun X : RationalResolutionInput.{u} ↦
    rationalConductorTower X (N.tower (normalConductorPreparedRationalInput X))
  choose C hC using rationalConductorTower_comparison N
  obtain ⟨hcomp, hcompmap, hsurj⟩ :=
    normalizedResolutionComparison_laws RationalResolutionInput (fun X ↦ X) T C
  refine ⟨{
    tower := T
    comparison := C
    empty := ?_
    identityIndex := ?_
    identityMap := ?_
    compositionIndex := hcomp
    compositionMap := hcompmap
    surjective_no_deletion := hsurj }, ?_⟩
  · intro X hx
    have hu : conductorIdeal X.scheme = ⊤ :=
      (rationalConductor_geometry X).unit_iff.mpr (fun x ↦ (hx.false x).elim)
    have hp : IsEmpty (normalConductorPreparedRationalInput X).val.scheme :=
      ⟨fun x ↦ hx.false ((conductorIdeal X.scheme).normalizedBlowupMap x)⟩
    simpa only [T, rationalConductorTower, dif_pos hu] using
      N.empty (normalConductorPreparedRationalInput X) hp
  · intro X hr i
    exact ((hC X X (𝟙 X.scheme) hr
      (normalizedResolutionIdentityComparison (T X))).1 i).symm
  · intro X hr i
    have hid := (hC X X (𝟙 X.scheme) hr
      (normalizedResolutionIdentityComparison (T X))).2 i
    exact hid.symm.trans
      (heq_of_eq (normalizedResolutionIdentityComparison_levelMap (T X) i))
  · intro X
    exact rationalConductorTower_extension X _

end AlgebraicGeometry
