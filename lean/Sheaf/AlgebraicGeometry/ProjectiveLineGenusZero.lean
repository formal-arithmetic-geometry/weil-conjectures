/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.Curve
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Sheaf.Topology.RingedSpaceModuleCohomology
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits
import WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveLine
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # The projective line is a genus-zero smooth proper connected curve

Source: Stacks Project, varieties.tex, Tag 0B2P, lemma-projective-space-smooth;
curves.tex, Tag 0C6U, proposition-projective-line, (1) implies (2) and (7)
(blueprint: lem-asd-projective-line-genus-zero).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProjectiveSpace

/-- The base-change projective line is a smooth proper connected curve, has genus zero,
and has vanishing first cohomology of its structure sheaf.
Source: Stacks Project, Tag 0B2P, lemma-projective-space-smooth, and Tag 0C6U,
proposition-projective-line, (1) implies (2) and (7)
(blueprint: lem-asd-projective-line-genus-zero).

Proof plan:
1. Identify the two degree-zero localization charts of the integral Proj with Z[t]
   and Z[s] by homogeneous monomial fractions (def-nagata-affine-proj). Base change
   gives k[t] and k[s] (lem-weil-pbc-fibre-product-affine-spectra), with overlap
   s = t inverse. They give the standard projective-line model (def-sc-p1-standard).
2. Each chart is affine one-space. Apply sbc-lem-affine-space-smooth and the
   affine-local criterion of def-sbc-smooth-morphisms to obtain smoothness of
   relative dimension one.
3. Both polynomial charts are irreducible because their coordinate rings are domains.
   Their overlap contains t = 1, so their union is nonempty and connected.
   lem-sbc-smooth-fixed-dimension-over-field gives dimension one.
4. lemma-nagata-projective-space-base-change-proper gives properness, including
   separatedness and finite type (def-weil-proper-morphism). Together with steps
   2 and 3 this gives the connected-curve clauses of def-sc-curves.
5. Apply lem-sc-p1-monomial(ii) at twist zero. The two local generators of O(0)
   have identity transition, identifying it with the structure sheaf. Transport
   vanishing of H1 to module cohomology. By def-sc-genus (equivalently Serre
   duality for the recorded differential-form genus), its genus is zero. -/
theorem isConnectedCurve_smooth_proper_genus_zero (k : Type u) [Field k] [IsAlgClosed k] :
    IsConnectedCurve (ProjectiveSpace (ULift.{u} (Fin 2)) (Spec (.of k)) ↘ Spec (.of k)) ∧
    Smooth (ProjectiveSpace (ULift.{u} (Fin 2)) (Spec (.of k)) ↘ Spec (.of k)) ∧
    IsProper (ProjectiveSpace (ULift.{u} (Fin 2)) (Spec (.of k)) ↘ Spec (.of k)) ∧
    (ProjectiveSpace (ULift.{u} (Fin 2)) (Spec (.of k)) ↘ Spec (.of k)).genus = 0 ∧
    Subsingleton ((RingedSpace.moduleCohomology
      (ProjectiveSpace (ULift.{u} (Fin 2)) (Spec (.of k))).toRingedSpace 1).obj
      (Scheme.Modules.unit (ProjectiveSpace (ULift.{u} (Fin 2)) (Spec (.of k))))) := by
  sorry

end AlgebraicGeometry.ProjectiveSpace
