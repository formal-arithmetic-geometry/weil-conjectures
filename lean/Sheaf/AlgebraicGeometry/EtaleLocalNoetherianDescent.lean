/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q52
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Noetherian

import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.Algebra.DirectSum.Module

/-!
# Descent of local Noetherianity along an etale covering

Source: Stacks Project, Descent, Tag 034C (descent direction), specialized to etale
coverings using Topologies, Tag 021N
(blueprint: lem-trf-etale-local-noetherian-descent).
-/

@[expose] public section

universe u v

open CategoryTheory

namespace AlgebraicGeometry

/-- Local Noetherianity descends along a jointly surjective family of etale morphisms.
Source: Stacks Project, Descent, Tag 034C; Topologies, Tags 021N and 0218
(blueprint: lem-trf-etale-local-noetherian-descent).

Proof plan:
1. For each affine open `W` of `T`, base change the covering to `W`
   (lem-weil-pbc-etale-covering-base-change). Identify each base change with the open
   preimage of `W` (lem-weil-pbc-open-preimage-fibre-product), and refine to finitely
   many affine opens `U_j` of the covering schemes
   (lem-weil-pbc-etale-covering-affine-refinement). Their rings `A_j` are Noetherian
   by pqf-lem-affine-open-locnoeth.
2. Write `R` for the sections of `W`. Etaleness implies flatness
   (def-weil-etale-morphism); the affine flatness criterion
   (lem-weil-pbc-flat-morphism-affine-criterion) and finite-product flatness
   (lem-weil-pbc-finite-product-flat-modules) make `R` to the product of the `A_j`
   flat. Joint surjectivity and the projections of that product give a surjection
   on prime spectra (def-weil-affine-spectrum). Thus this map is faithfully flat
   (lem-weil-pbc-flat-surjective-spectrum-faithfully-flat). The finite product is
   Noetherian by the componentwise ideal argument, so faithfully flat descent
   (lem-weil-pbc-faithfully-flat-descent-noetherian) makes `R` Noetherian.
3. Apply the affine-open-cover characterization of local Noetherianity
   (pqf-def-locnoeth) to conclude that `T` is locally Noetherian. -/
theorem isLocallyNoetherian_of_etale_cover
    {T : Scheme.{u}} {A : Type v} (Tₐ : A → Scheme.{u}) (t : ∀ a, Tₐ a ⟶ T)
    [∀ a, Etale (t a)] [∀ a, IsLocallyNoetherian (Tₐ a)]
    (hcover : ∀ x : T, ∃ a : A, ∃ y : Tₐ a, t a y = x) :
    IsLocallyNoetherian T := by
  sorry

end AlgebraicGeometry
