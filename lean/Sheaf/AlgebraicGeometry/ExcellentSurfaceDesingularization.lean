/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Sheaf.AlgebraicGeometry.FunctionField
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.RingTheory.ExcellentRing
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback
public import Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.ProjectiveBundleToHProjective
import Sheaf.AlgebraicGeometry.RegularNormalDecomposition
import Sheaf.AlgebraicGeometry.ExcellentNormalSurfaceLocalData
import Sheaf.AlgebraicGeometry.ExcellentNormalizedBlowupTower
import Sheaf.AlgebraicGeometry.NormalizedBlowupCompletionDescent
import Sheaf.AlgebraicGeometry.SurfaceResolutionNormalizedRefinement
import Sheaf.DeligneLaumon.CompleteNormalSurfaceResolution

/-!
# Projective resolution of excellent integral surfaces

Source: Stacks Project, Resolution of Surfaces, Tag 0BGP, proof of (4) implies (3);
Morphisms, Tag 087S; ILO, Exposé XVII, §3.4.1, first paragraph
(blueprint: lem-per-excellent-surface-desingularization).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- An excellent integral Noetherian surface admitting an ample invertible module has a
regular integral H-projective birational resolution, unchanged over its regular locus.
Here `IsHProjective` is the closed-immersion factorization into finite projective space,
and `functionFieldMap` is the actual generic stalk map of the resolution morphism.

Source: Stacks Project, Tag 0BGP, proof of (4) implies (3), with Tag 087S for the finite
projective-space factorization; ILO XVII §3.4.1
(blueprint: lem-per-excellent-surface-desingularization).

Proof plan:
1. Normalize Y. The length-zero case of lem-per-excellent-normalized-blowup-tower makes
   the normalization finite, integral, normal, Noetherian, excellent and two dimensional,
   with unchanged function field. Excellence makes the regular locus R open, and
   rem-pc-regular-normal makes it normal; normalization is therefore an isomorphism over R.
2. By lem-per-excellent-normal-surface-local-data the normalization has finitely many
   closed singular points x_i. Their local rings and completions are normal Noetherian
   local domains of dimension two, and the completions are complete. None lies over R.
3. Apply lem-per-complete-normal-surface-resolution to each completion, then
   lem-per-surface-resolution-normalized-refinement to obtain finite proper normalized
   point-blowup towers with regular endpoints and centers over the closed point.
4. Descend each tower using lem-per-normalized-blowup-completion-descent. Normality of
   the completion was checked in step 2. The descended towers are proper and have regular
   endpoints by that lemma's completion comparison.
5. Apply lem-per-local-normalized-blowups-globalize to the distinct closed x_i. The
   resulting global tower is an isomorphism away from them. Every endpoint local ring is
   either a regular local ring of that open or one of the regular local endpoint rings.
   Thus its endpoint V is regular, using def-weil-regular-scheme.
6. Concatenate with the normalization. By lem-per-excellent-normalized-blowup-tower,
   V is integral and the composite r is projective in the projective-bundle sense and
   induces an isomorphism of function fields. The given ample invertible module permits
   lem-trf-projective-bundle-to-h-projective, giving precisely `IsHProjective r`.
7. The tower centers avoid the preimage of R. Restrict its isomorphism off the x_i to
   that preimage, and compose with the normalization isomorphism over R. This gives the
   asserted isomorphism over the entire regular locus. If there are no singular points,
   the global tower is the identity and the same argument applies. -/
theorem exists_projective_regular_resolution_of_excellent_surface
    (Y : Scheme.{u}) [IsIntegral Y] [IsNoetherian Y]
    (hExcellent : ∀ U : Y.affineOpens, IsExcellent Γ(Y, U))
    (hDim : topologicalKrullDim Y = 2)
    (hAmple : ∃ (L : Y.Modules) (hL : L.IsInvertible), @Scheme.Modules.IsAmple Y L hL) :
    ∃ (V : Scheme.{u}) (_ : IsIntegral V) (r : V ⟶ Y),
      IsRegularScheme V ∧ IsHProjective r ∧
      (∃ hη : r (genericPoint V) = genericPoint Y, IsIso (r.functionFieldMap hη)) ∧
      ∃ U : Y.Opens,
        (∀ y : Y, y ∈ U ↔ IsRegularLocalRing (Y.presheaf.stalk y)) ∧ IsIso (r ∣_ U) := by
  sorry

end AlgebraicGeometry
