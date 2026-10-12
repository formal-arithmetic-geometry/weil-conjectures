/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
import Sheaf.AlgebraicGeometry.GenericFiniteSchemeSplitting
import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance

/-! # Generic splitting over a Noetherian scheme

Source: the proof of `lem-weil-pbc-finite-module-generic-reflection`, step 1,
using Stacks Project Tags 095K, 0959 and 04DZ.
(blueprint: lem-weil-pbc-generic-finite-noetherian-scheme-splitting)
-/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A finite morphism splits into universal homeomorphisms on an etale cover of a
smaller dense open. This assertion concerns schemes alone and has no sheaf hypothesis.

Source: `lem-weil-pbc-finite-module-generic-reflection`, proof step 1;
Stacks Project Tags 095K, 0959 and 04DZ.
(blueprint: lem-weil-pbc-generic-finite-noetherian-scheme-splitting)

Proof: Reduce the Noetherian target. Its finitely many irreducible components have
pairwise disjoint dense affine integral opens, after removing their intersections.
Intersect these opens with V. Apply `exists_dense_open_finite_scheme_splitting` to
its finite source over each such affine, and intersect with the dense splitting open.
The union of the resulting opens contains each generic point and is dense in the
reduced target, hence in the original target; it is contained in V. On each component
use the etale surjective cover supplied by the affine theorem. Etale schemes lift
uniquely across the nilpotent reduction immersion (04DZ); the lifted cover remains
surjective since reduction does not change points. The disjoint clopen components of
the reduced source lift uniquely to those of the original source. Each component map
is still a universal homeomorphism: both vertical reduction maps are universal
homeomorphisms, and universal injectivity, surjectivity and integrality are unchanged
by these nilpotent thickenings. Compose the lifted etale covers with their component
open immersions to obtain a cover of U. Pullbacks of the restricted morphism have the
asserted finite disjoint partitions. For the empty target take U empty and an empty
cover. Empty inverse images have the empty partition, whose union is top. -/
theorem exists_dense_open_finite_noetherian_scheme_splitting
    {X Y : Scheme.{u}} [IsNoetherian Y] (f : X ⟶ Y) [IsFinite f]
    (V : Y.Opens) (hV : Dense (V : Set Y)) :
    ∃ U : Y.Opens, U ≤ V ∧ Dense (U : Set Y) ∧
      ∃ 𝒯 : Cover.{u} etalePrecoverage U.toScheme, ∀ i,
        ∃ (n : ℕ) (W : Fin n → (pullback (𝒯.f i) (f ∣_ U)).Opens),
          (⨆ j, W j) = ⊤ ∧ Pairwise (fun j k ↦ Disjoint (W j) (W k)) ∧
          ∀ j, IsUniversalHomeomorphism
            ((W j).ι ≫ pullback.fst (𝒯.f i) (f ∣_ U)) := by sorry

end AlgebraicGeometry.Scheme
