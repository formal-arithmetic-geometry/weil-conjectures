/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.Irreducible
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.Topology.PresheafModuleStalkFunctor
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme

/-! # Common affine neighbourhoods of points of local dimension at most one

Source: Stacks Project, Varieties, Tag 09NN,
proposition-finite-set-of-points-of-codim-1-in-affine
(blueprint: lem-trf-codimension-one-points-affine-neighbourhood).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace AlgebraicGeometry

/-- Finitely many points with Noetherian local rings of dimension at most one lie in a
common affine open of a separated scheme whose quasi-compact opens have finitely many
irreducible components. The point family may be empty or have repetitions.

Source: Stacks Project, Varieties, Tag 09NN,
proposition-finite-set-of-points-of-codim-1-in-affine
(blueprint: lem-trf-codimension-one-points-affine-neighbourhood).

Proof, following the five steps of the DAG:
1. If r = 0 use the empty affine open Spec(0). Otherwise choose affine opens around
   the selected points (def-pc-scheme and def-weil-affine-spectrum). Their finite union W
   is quasi-compact by lem-weil-pbc-affine-scheme-qcqs, so it has finitely many irreducible
   components. Restriction identifies its selected local rings with those of Z
   (def-weil-pbc-module-stalk). It suffices to work inside W.
2. Give each component C its reduced induced structure using
   lem-weil-pbc-reduced-induced-closed-subscheme. It is integral by def-pc-integral-scheme.
   W and C are separated: their inclusions into Z are monomorphisms, hence their
   diagonals are pullbacks of the closed diagonal of Z. Use def-weil-open-immersion,
   def-weil-closed-immersion and lem-weil-pbc-closed-immersion-base-change.
3. At each selected point on C the closed immersion gives a surjection A to B of
   local rings. Indeed a germ in B is represented by a section which lifts locally
   along the surjection of structure sheaves. For every ideal J of B, finite generators
   of its inverse image in the Noetherian ring A map to generators of J. Thus B is
   Noetherian. Inverse images of prime ideals preserve strict inclusions under a
   surjection, so dim B <= dim A <= 1 (def-weil-pbc-noetherian-ring and
   def-weil-pbc-krull-dimension-ring). This applies also to points on several components.
4. Apply lem-trf-integral-codimension-one-affine-neighbourhood (Tag 09NJ) on every C
   to the finite set of selected points on C, using the hypotheses just checked.
   This supplies affine opens V_C containing these points, including the empty case.
5. Apply lem-trf-componentwise-finite-set-affine-neighbourhood (Tag 09NM) to W and
   the V_C. The resulting affine open of W is an affine open of Z and contains every
   selected point. -/
theorem exists_isAffineOpen_containing_codimensionOne_points
    (Z : Scheme.{u}) [Z.IsSeparated]
    (hcomponents : ∀ U : Z.Opens, IsCompact (U : Set Z) →
      (irreducibleComponents U).Finite)
    (r : ℕ) (z : Fin r → Z)
    (hnoetherian : ∀ i : Fin r, IsNoetherianRing (Z.presheaf.stalk (z i)))
    (hdimension : ∀ i : Fin r, ringKrullDim (Z.presheaf.stalk (z i)) ≤ 1) :
    ∃ U : Z.Opens, IsAffineOpen U ∧ ∀ i : Fin r, z i ∈ U := by
  sorry

end AlgebraicGeometry
