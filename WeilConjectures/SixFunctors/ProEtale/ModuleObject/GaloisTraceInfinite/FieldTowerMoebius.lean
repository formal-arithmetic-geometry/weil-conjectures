/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisTraceInfinite.FieldTower
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisTraceInfinite.MoebiusDecomposition
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisTraceInfinite.TowerProjector
public import WeilConjectures.FieldTheory.Galois.FiniteGaloisIntermediateField
public import WeilConjectures.Mathlib.Combinatorics.Enumerative.IncidenceAlgebra

/-!
# The Möbius decomposition of the Galois tower of a field extension

Let `Ω/L` be a Galois extension, `h : G ⟶ Spec L` and `T` the Galois tower of `Ω/L` over `G`
(`AlgebraicGeometry.ProEtale.galoisTower`), with finite levels `G ×_L j` for the finite Galois
subextensions `j` and Galois groups `Gal(j/L)`. Let `M` be a `Λ_G`-module object such that
`M_∞ = g_{∞*} g_∞^* M` is the colimit of the finite levels `M_j`, the orders `|Gal(j/L)|` being
invertible.

For a finite Galois subextension `k`, the images `N j k ≤ Gal(j/L)` of `Gal(Ω/k)` form a compatible
family of normal subgroups (`AlgebraicGeometry.ProEtale.galoisTower_transport_comp_levelAvg`),
whose projector `π_k : M_∞ ⟶ M_∞` (`AlgebraicGeometry.ProEtale.GaloisTower.proj`) is the
projector onto the `Gal(Ω/k)`-invariants. By the Galois correspondence `π_k ≫ π_m = π_(k ⊓ m)`
(`AlgebraicGeometry.ProEtale.galoisTower_proj_comp_proj`); moreover `π_j` is the identity on the
image of the level `j`, `π_⊥ = τ ≫ u`, and `π_k ≫ ∑_{a ∈ Gal(k/L)} σ_a = |Gal(k/L)| • π_⊥` for
lifts `σ_a ∈ Gal(Ω/L)` of the elements of `Gal(k/L)`.

The Möbius components `e_k = ∑_{m ≤ k} μ(m, k) π_m` (`IncidenceAlgebra.moebiusComponent`) then
form a Möbius decomposition of `g_{∞*} g_∞^* K` for a complex `K`
(`AlgebraicGeometry.ProEtale.exists_galoisTowerMoebiusDecomposition`).
-/

@[expose] public section

universe u

open CategoryTheory Category Limits Preadditive

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry

open FiniteGaloisIntermediateField ProEtale

variable {L Ω : Type u} [Field L] [Field Ω] [Algebra L Ω] {G : Scheme.{u}}
  (h : G ⟶ Spec (.of L))

end AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing GaloisTower FiniteGaloisIntermediateField IncidenceAlgebra

variable {L Ω : Type u} [Field L] [Field Ω] [Algebra L Ω] [IsGalois L Ω] {G : Scheme.{u}}
  (h : G ⟶ Spec (.of L)) (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
  [IsCommMonObj Λ]
  (hd : ∀ (j : (galoisTower Ω h).J)
    (N : CategoryTheory.Mod (Sheaf (ProEt.topology G) Ab.{u + 1}) (condensedRingObj Λ G)),
      IsIso (Fintype.card ((galoisTower Ω h).Γ j) • 𝟙 N))
  (M : CategoryTheory.Mod (Sheaf (ProEt.topology G) Ab.{u + 1}) (condensedRingObj Λ G))

set_option hygiene false in
/-- The projector `π_k : M_∞ ⟶ M_∞` onto the `Gal(Ω/k)`-invariants. -/
local notation3 "𝒫[" M ", " hc ", " k "]" => GaloisTower.proj (galoisTower Ω h) Λ M hd hc
  (fun x_proj ↦ restrictFixingSubgroup x_proj k) (galoisTower_transport_comp_levelAvg h Λ hd M k)

section Projectors

variable {M} (hc : IsColimit ((galoisTower Ω h).moduleCocone Λ M))

end Projectors

variable (K : CochainComplex
    (CategoryTheory.Mod (Sheaf (ProEt.topology G) Ab.{u + 1}) (condensedRingObj Λ G)) ℤ)
  (hc : ∀ n, IsColimit ((galoisTower Ω h).moduleCocone Λ (K.X n)))

end AlgebraicGeometry.ProEtale
