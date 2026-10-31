/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Finiteness of closed subsets consisting of closed points

Source: Stacks Project, Properties Lemma 28.5.7 (Tag 0BA8), together with
Schemes Lemma 26.11.1 (Tag 01IS).
(blueprint: lem-sc-noetherian-closed-points-finite)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- A closed subset of a Noetherian scheme consisting of closed points is finite.
Source: Stacks Project, Tags 0BA8 and 01IS.
(blueprint: lem-sc-noetherian-closed-points-finite)

Proof:
1. By `lem-sc-noetherian-closed-subset-finite-components`, the closed subset `E`
   is the union of finitely many irreducible closed components.
2. By `lem-sc-scheme-sober` (Tag 01IS), each component has a generic point `ξ`
   belonging to it, and the component equals the closure of `{ξ}`. Since `ξ ∈ E`,
   the hypothesis makes `{ξ}` closed in `X`, so its closure is `{ξ}`.
3. Thus `E` is the union of finitely many singletons, hence is finite. -/
theorem finite_of_isClosed_of_closed_points (X : Scheme.{u})
    [IsLocallyNoetherian X] [CompactSpace X] (E : Set X) (hE : IsClosed E)
    (hpoints : ∀ x ∈ E, IsClosed ({x} : Set X)) : E.Finite := by
  let : IsNoetherian X := ⟨⟩
  obtain ⟨S, hS, hSc, hSi, rfl⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hE
  refine hS.sUnion fun Z hZ ↦ ?_
  obtain ⟨x, hx⟩ := QuasiSober.sober (hSi Z hZ) (hSc Z hZ)
  have hxE : x ∈ ⋃₀ S := Set.mem_sUnion.mpr ⟨Z, hZ, hx.mem⟩
  have hZeq : Z = {x} := hx.def.symm.trans (hpoints x hxE).closure_eq
  rw [hZeq]
  exact Set.finite_singleton x

end AlgebraicGeometry
