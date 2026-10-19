/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q157
-/
module

public import Sheaf.AlgebraicGeometry.NodalNormalizationQuotient
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Topology.KrullDimension

/-! # Euler characteristic of a nodal curve from its normalization

Source: Stacks Project, Varieties, Tag 0C1R (lemma-prepare-delta-invariant), and Curves,
Tag 0CBW (lemma-split-node) (blueprint: lem-trf-nodal-curve-normalization-euler).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/- The normalization exact sequence contributes one copy of the residue field at every
nonsmooth point. Euler additivity and affine pushforward identify the Euler characteristic
of the original curve with the sum of the component Euler characteristics minus that
number. Each smooth proper connected normalized component has Euler characteristic
`1 - genus`, because its structure-sheaf cohomology vanishes above degree one, has
degree-zero dimension one, and degree-one dimension its genus. -/
/-- For a proper reduced connected nodal curve, the structure-sheaf Euler characteristic
is the number of irreducible components minus the number of internal nodes minus the sum
of the genera of the normalized components.

Source: Stacks Project, Varieties, Tag 0C1R (lemma-prepare-delta-invariant), normalization
exact sequence; Curves, Tag 0CBW (lemma-split-node), completed split-node model
(blueprint: lem-trf-nodal-curve-normalization-euler).

Proof:
1. Apply `nodal_normalization_quotient` to the finite nonsmooth locus. It supplies the
   coherent short exact sequence from the structure sheaf to the pushforward of the
   componentwise normalization and gives Euler characteristic equal to the number of
   nonsmooth points.
2. Euler additivity and the affine cohomology edge isomorphisms for the finite
   normalization and component inclusions identify the Euler characteristic of the curve
   with the sum of the Euler characteristics of its normalized components, minus the
   nonsmooth-point count.
3. Each normalized component is smooth, proper, connected, and one-dimensional. Its
   higher structure-sheaf cohomology vanishes, degree zero has dimension one, and degree
   one has dimension its genus, so its Euler characteristic is `1 - genus`.
4. Summing these values gives the displayed formula. A self-node contributes exactly one
   copy in the normalization quotient and is therefore counted once.
-/
theorem nodal_curve_normalization_euler
    (k : Type u) [Field k] [IsAlgClosed k]
    (B : Scheme.{u}) [B.Over (Spec (.of k))]
    [IsProper (B ↘ Spec (.of k))] [IsReduced B] [ConnectedSpace B]
    (hpure : ∀ Z : Set B, Z ∈ irreducibleComponents B → topologicalKrullDim Z = 1)
    (hnodal : ∀ x : B, x ∉ (B ↘ Spec (.of k)).smoothLocus →
      Nonempty (AdicCompletion (IsLocalRing.maximalIdeal (B.presheaf.stalk x))
        (B.presheaf.stalk x) ≃+*
          (MvPowerSeries (Fin 2) k ⧸ Ideal.span
            {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) * MvPowerSeries.X 1})))
    (N : Set B) (hN : N = {x : B | x ∉ (B ↘ Spec (.of k)).smoothLocus})
    (v : ℕ) (components : Fin v ≃ irreducibleComponents B)
    (Z : Fin v → Scheme.{u}) [∀ a : Fin v, IsIntegral (Z a)]
    (j : ∀ a : Fin v, Z a ⟶ B) [∀ a : Fin v, IsClosedImmersion (j a)]
    (hcomponents : ∀ a : Fin v, Set.range (j a) = (components a).1)
    (hnormalizations : ∀ a : Fin v,
      IsProper ((Z a).fromNormalization ≫ j a ≫ B ↘ Spec (.of k)) ∧
      Smooth ((Z a).fromNormalization ≫ j a ≫ B ↘ Spec (.of k)) ∧
      ConnectedSpace (Z a).normalization) :
    Scheme.Modules.eulerChar k (Modules.unit B) =
      (v : ℤ) - (N.ncard : ℤ) -
        ∑ a : Fin v,
          (((Z a).fromNormalization ≫ j a ≫ B ↘ Spec (.of k)).genus : ℤ) := by
  sorry

end AlgebraicGeometry.Scheme
