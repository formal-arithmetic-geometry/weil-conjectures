/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q136
-/
module

public import WeilConjectures.AlgebraicGeometry.Ample
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Sober
public import Mathlib.CategoryTheory.Endomorphism
import Sheaf.AlgebraicGeometry.AmpleFinitePrincipalAffine
import WeilConjectures.Mathlib.Topology.KrullDimension

/-! # Two ample affine section opens avoiding an orbit boundary

Source: Stacks Project, Properties, Lemma 09NV, applied twice, with the Noetherian
component and dimension argument in the DAG proof; preparation for de Jong, §3.4(b).
(blueprint: lem-sfb-ample-orbit-affine-pair).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Two positive tensor powers of an ample invertible module admit affine section opens
containing all component generic points, with the second containing the full finite-group
orbit of the first open's boundary. No linearization of the module is required.

Source: Stacks Project, Properties, Lemma 09NV, applied twice, and the Noetherian
component and dimension argument in the DAG proof; preparation for de Jong, §3.4(b).
(blueprint: lem-sfb-ample-orbit-affine-pair).

Proof:
1. The Noetherian scheme has Noetherian underlying space
   (`lem-weil-pbc-noetherian-scheme-closed-subsets-minimal`). Its irreducible components
   form a finite cover (`lem-sc-noetherian-closed-subset-finite-components`). Sobriety
   (`lem-weil-pbc-scheme-sober`) gives a unique generic point of each component, so their
   set is finite and, since the scheme is nonempty, nonempty. Sobriety also gives T0.
2. Apply `lem-sc-ample-finite-principal-affine` (09NV) to these generic points and the
   whole scheme. Obtain a positive-power section with affine locus U containing them.
3. Its closed complement Z misses every component generic point. If irreducible closed
   subsets A strictly contained in B existed in Z, irreducibility of B and the finite
   component cover would put B in a component C. Since the generic point of C is outside
   Z, B is strictly smaller than C. The chain A < B < C contradicts dimension at most one
   (`def-kun-topological-krull-dimension`). Thus Z has dimension at most zero, including
   the empty case. Apply `lem-sc-zero-dim-noetherian-closed-finite` to see that Z is finite
   and that every point of Z is closed in the original scheme.
4. Each inverse image of Z under a group element is finite, since the automorphism is
   bijective. Their finite union T is finite. Pullback under h reindexes the union by
   multiplication by h, hence leaves T unchanged; faithfulness is unnecessary.
5. Apply `lem-sc-ample-finite-principal-affine` again to the finite union of the generic
   points and T. The resulting positive-power section has affine locus V containing
   both. These inclusions give all the remaining assertions.
-/
theorem exists_ample_orbit_affine_pair
    (Y : Scheme.{u}) [Nonempty Y] [IsLocallyNoetherian Y] [CompactSpace Y]
    (hdim : topologicalKrullDim Y ≤ 1)
    (L : Y.Modules) [L.IsInvertible] (hL : IsAmple Y L)
    {G : Type v} [Group G] [Finite G] (ρ : G →* Aut Y) :
    (genericPoints Y).Finite ∧ (genericPoints Y).Nonempty ∧
      ∃ p q : ℕ, 0 < p ∧ 0 < q ∧
        ∃ (s : (L.tensorPow p).val.presheaf.obj (Opposite.op ⊤))
          (t : (L.tensorPow q).val.presheaf.obj (Opposite.op ⊤))
          (U V : Y.Opens),
          (U : Set Y) = nonvanishingLocus (L.tensorPow p) s ∧
          (V : Set Y) = nonvanishingLocus (L.tensorPow q) t ∧
          IsAffineOpen U ∧ IsAffineOpen V ∧
          genericPoints Y ⊆ (U : Set Y) ∩ (V : Set Y) ∧
          ((U : Set Y)ᶜ).Finite ∧
          (∀ z : Y, z ∈ (U : Set Y)ᶜ → IsClosed ({z} : Set Y)) ∧
          ∃ T : Set Y, T = ⋃ g : G, (ρ g).hom ⁻¹' (U : Set Y)ᶜ ∧
            T.Finite ∧ (∀ h : G, (ρ h).hom ⁻¹' T = T) ∧ T ⊆ (V : Set Y) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
