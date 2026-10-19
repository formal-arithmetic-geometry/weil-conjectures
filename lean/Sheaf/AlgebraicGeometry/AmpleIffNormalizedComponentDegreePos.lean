/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Irreducible

import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.Noetherian.Defs
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import Sheaf.AlgebraicGeometry.FiniteSurjectiveAmpleReflection
import Sheaf.AlgebraicGeometry.ProperIntegralCurveAmpleDegree
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme

/-!
# Ampleness and degrees on normalized components of a proper curve

Source: Stacks Project, Varieties, Tag 0B5Y
(blueprint: lem-trf-fibre-degree-ample-criterion), using finite normalization from
Tag 0BXR and the proper integral curve criterion of Tag 0B5X.

An integral closed subscheme whose image is an irreducible component is its unique
reduced induced scheme structure. The components of `X` and `X` reduced coincide.
Thus the quantified `C` below are precisely the components in the node, with no
condition on zero-dimensional components. The normalization is the recorded canonical
normalization in the component's function field, and its field structure is the
composite of its normalization map, its inclusion, and the structure map of `X`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- An invertible module on a proper scheme of dimension at most one is ample exactly
when its pullback to every normalized one-dimensional reduced component has positive degree.

Source: Stacks Project, Varieties, Tag 0B5Y, with Tag 0BXR for finite normalization and
Tag 0B5X for the integral-curve degree criterion
(blueprint: lem-trf-fibre-degree-ample-criterion).

Proof, following the node's six steps:
1. Properness gives finite type over the Noetherian field. By
   `lem-weil-pbc-finite-type-over-noetherian` and
   `lem-weil-pbc-noetherian-finite-components`, there are finitely many components.
   `lem-weil-pbc-reduced-induced-closed-subscheme` gives their reduced structures,
   integral by `def-pc-integral-scheme`. Their dimensions are at most one. By
   `lem-weil-pbc-scheme-sober`, the zero-dimensional components are isolated closed points.
2. Their inclusions are finite by `lem-weil-pbc-closed-immersion-finite`, and proper
   over the field by `lem-weil-pbc-finite-proper` and `lem-weil-pbc-proper-composition`.
   `lem-sc-normalization-exists` gives finite surjective normalizations of the curve
   components, still proper, integral, and one-dimensional, over the original field.
   Integrality follows from the integral closure inside their function fields.
3. Form the finite disjoint union of these normalizations and the reduced point components.
   Its map to `X` is finite by `lem-weil-pbc-finite-composition` and
   `lem-weil-pbc-finite-coproduct`, and surjective since the components cover `X`.
   It is proper by `lem-weil-pbc-finite-proper` and `lem-weil-pbc-proper-composition`.
   Apply `lem-trf-finite-surjective-ample-reflection` over the Noetherian field.
   If `X` is empty, both the ample-locus and degree conditions hold vacuously.
4. On a finite disjoint union, ampleness is equivalent to ampleness on every summand:
   restrict witnessing sections in one direction; extend them by zero in the other.
   The affine nonvanishing loci stay affine on restriction along the closed summand
   inclusions, by `lem-weil-pbc-closed-immersion-finite`. Compactness is preserved.
5. A reduced zero-dimensional integral component is the spectrum of a field. A nonzero
   basis section of its invertible module has affine nonvanishing locus the whole point,
   so every invertible module there is ample; these components impose no degree condition.
6. `lem-weil-pbc-invertible-pullback-tensor` gives invertibility and composition for
   the pullback to each normalized curve. Apply `lem-trf-proper-integral-curve-ample-degree`
   to it, with degree as in `def-pc-degree-line-bundle`. Combine the summand equivalences
   with finite-surjective reflection. No smoothness or perfectness of the field is used. -/
theorem isAmple_iff_normalizedComponentDegree_pos
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] (hdim : topologicalKrullDim X ≤ 1)
    (M : X.Modules) [M.IsInvertible] :
    IsAmple X M ↔
      ∀ (C : Scheme.{u}) [IsIntegral C] (i : C ⟶ X),
        IsClosedImmersion i → Set.range i ∈ irreducibleComponents X →
        topologicalKrullDim C = 1 →
        0 < @Scheme.Modules.degree k _ C.normalization
          ⟨C.fromNormalization ≫ i ≫ (X ↘ Spec (.of k))⟩
          ((Scheme.Modules.tensorPullback (C.fromNormalization ≫ i)).obj M) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
