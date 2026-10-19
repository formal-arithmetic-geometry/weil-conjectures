/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.Compactification.StrictTransform
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.OrdinaryResolutionRule
import WeilConjectures.AlgebraicGeometry.FinitePushforwardCoherent
import Sheaf.AlgebraicGeometry.NoetherianQuasicoherentSubmodules
import WeilConjectures.Compactification.StrictTransformBlowup
import WeilConjectures.Blowup.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Regularizing an embedded curve by blowups at singular closed points

Source: Stacks Project, Resolution of Surfaces, Tags 0BI4 and 0BI5
(blueprint: lem-per-surface-curve-regularization-by-blowups).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- An integral closed curve with finite normalization in a Noetherian scheme has a regular
successive strict transform after finitely many blowups at reduced singular closed points.
`OrdinaryBlowupTower` retains the actual ideals, blowup identifications and transition maps.
The family `C` retains the successive strict transforms, with their embeddings `ι`; the
isomorphism at each step commutes with the embedding into the actual ambient blowup.
Radicality and singleton support specify the reduced closed point as a closed subscheme.
Length zero is allowed, and regularity is the locally Noetherian scheme predicate.

Source: Stacks Project, Tags 0BI4 and 0BI5
(blueprint: lem-per-surface-curve-regularization-by-blowups).

Proof plan, following the seven steps of the node:
1. A closed subscheme of a Noetherian scheme is Noetherian: on a finite affine cover
   its rings are quotients of Noetherian rings. This uses def-weil-closed-immersion,
   def-weil-pbc-noetherian-ring, pqf-def-locnoeth and def-weil-pbc-quasi-compact-scheme.
2. By lem-per-finite-curve-normalization-regular, the normalization N is an integral
   Noetherian regular curve, finite and birational over Y. Its structure sheaf has coherent
   pushforward by lem-weil-pbc-finite-pushforward-coherent.
3. Starting with N over Y, repeatedly apply lem-per-singular-curve-point-blowup-step
   at a singular point of the current integral curve. Such a point is closed in dimension
   one. The resulting nonisomorphic blowup is finite and birational, and N factors through
   it by a finite birational morphism. Maintain this invariant under composition, using
   the affine characterization in def-weil-finite-integral-morphism.
4. Each intermediate curve gives a coherent subalgebra of the fixed pushforward from N,
   by lem-weil-pbc-finite-pushforward-coherent. The generic-field inclusions make these
   inclusions injective (def-pc-integral-scheme). They are strict: equality on each affine
   of Y would identify the corresponding finite algebras and make the blowup an isomorphism.
5. The increasing sequence terminates by lem-weil-pbc-noetherian-acc-quasi-coherent.
   Thus some intrinsic curve is regular. If Y is regular initially, use length zero.
6. Blow up the same reduced point in each ambient scheme. The center remains closed by
   lem-weil-pbc-closed-immersion-comp. Its ideal is finitely generated on Noetherian affines.
   By thm-nagata-global-blowup-proper, def-weil-proper-morphism and
   lem-weil-pbc-finite-type-over-noetherian the ambient blowup is Noetherian. The extended
   center ideal on the curve is its reduced point ideal. The comparison
   thm-nagata-strict-transform-is-blowup identifies its intrinsic blowup with the strict
   transform. It is closed in the new ambient scheme by def-nagata-strict-transform,
   lem-weil-pbc-closed-immersion-base-change and lem-weil-pbc-closed-immersion-comp.
7. The final embedded strict transform is isomorphic to the regular intrinsic curve.
   Every center is reduced and was singular on the current curve, giving all clauses. -/
theorem exists_surface_curve_regularization_by_blowups
    (X Y : Scheme.{u}) [IsNoetherian X] [IsIntegral Y]
    (j : Y ⟶ X) [IsClosedImmersion j]
    (hDim : topologicalKrullDim Y = 1) [IsFinite Y.fromNormalization] :
    ∃ A : OrdinaryBlowupTower X,
      ∃ C : Fin (A.length + 1) → Scheme.{u},
        ∃ ι : ∀ i, C i ⟶ A.level i,
          ∃ e₀ : C 0 ≅ Y,
            ι 0 ≫ A.initial.hom = e₀.hom ≫ j ∧
            (∀ i, IsClosedImmersion (ι i)) ∧
            (∀ i : Fin A.length, ∃ p : C i.castSucc,
              IsClosed ({p} : Set (C i.castSucc)) ∧
              ¬ IsRegularLocalRing ((C i.castSucc).presheaf.stalk p) ∧
              (A.center i).radical = A.center i ∧
              ((A.center i).support : Set (A.level i.castSucc)) = {ι i.castSucc p} ∧
              ∃ e : C i.succ ≅ (A.center i).strictTransform (ι i.castSucc),
                e.hom ≫ strictTransformMap (ι i.castSucc) (A.center i).blowupMap
                    (A.center i).support.compl =
                  ι i.succ ≫ (A.blowupIso i).hom) ∧
            IsRegularScheme (C (Fin.last A.length)) := by
  sorry

end AlgebraicGeometry
