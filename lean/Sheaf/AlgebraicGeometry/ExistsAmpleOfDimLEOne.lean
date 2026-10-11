/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.Ample

/-! # Ample invertible modules in dimension at most one

Source: Stacks Project, Varieties, Lemma 0A25 and Proposition 09NZ
(blueprint: lem-sc-dim-one-ample-invertible).
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- A separated finite-type scheme over a field of topological dimension at most one
has an ample invertible module, including when the scheme is empty.
Source: Stacks Project, Varieties, Lemma 0A25, using Proposition 09NZ
(blueprint: lem-sc-dim-one-ample-invertible).

Proof:
1. A field is Noetherian, and its spectrum is Noetherian. Finite type over this spectrum
makes `X` Noetherian (`lem-weil-pbc-finite-type-over-noetherian`).
2. Separatedness over the affine base gives absolute separatedness
(`lem-sc-separated-over-affine-scheme-separated`).
3. The reduction `Z` is reduced and its closed immersion into `X` is a universal
homeomorphism (`lem-weil-pbc-reduction-universal-homeomorphism`). It is finite
(`lem-weil-pbc-closed-immersion-finite`), so the composite to the field spectrum remains
separated and finite type (`lem-weil-pbc-finite-over-separated-finite-type`). Thus `Z`
is Noetherian and separated; the homeomorphism preserves topological Krull dimension.
4. Apply `lem-sc-reduced-dim-le-one-ample` to obtain an ample invertible module `N` on `Z`.
5. Noetherianity gives minimal closed subsets
(`lem-weil-pbc-noetherian-scheme-closed-subsets-minimal`). Lift `N` to an invertible
module `L` on `X` by `lem-sc-pic-lift-closed-immersion-dim-le-one`. The pullback of `L`
is isomorphic to `N`; this isomorphism matches sections of all tensor powers and their
nonvanishing loci, so the pullback is ample.
6. Apply `lem-sc-ample-on-reduction-noetherian` to the closed immersion, which is a
homeomorphism, to conclude that `L` is ample on `X`.
-/
theorem exists_isAmple_of_dim_le_one {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hdim : topologicalKrullDim X ≤ 1) :
    ∃ L : X.Modules, ∃ hL : L.IsInvertible, @IsAmple X L hL := by
  sorry

end AlgebraicGeometry.Scheme.Modules
