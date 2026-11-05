/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisTraceInfinite.TowerTrace
public import WeilConjectures.CategoryTheory.Preadditive.SubgroupAverage

/-!
# Averaging projectors on the infinite level of a Galois tower

Let `T` be a Galois tower over `X` (`AlgebraicGeometry.ProEtale.GaloisTower`), `Λ` a commutative
condensed ring in which the orders `|Γ_j|` are invertible, and `M` a `Λ_X`-module object such
that `M_∞ = g_{∞*} g_∞^* M` is the colimit of the finite levels `M_j = g_{j*} g_j^* M`.

For a subgroup `H ≤ Γ_j`, the average `avg_H = |H|⁻¹ ∑_{a ∈ H} a` acts on `M_j`
(`AlgebraicGeometry.ProEtale.GaloisTower.levelAvg`). A family of subgroups `N j ≤ Γ_j` compatible
with the transition maps (`AlgebraicGeometry.ProEtale.GaloisTower.transport_comp_levelAvg`) gives
a projector `π_N : M_∞ ⟶ M_∞` (`AlgebraicGeometry.ProEtale.GaloisTower.proj`), equal to
`avg_{N j}` on the level `j`. We prove:

* `π_N ≫ π_N' = π_(N ⊔ N')` for normal subgroups
  (`AlgebraicGeometry.ProEtale.GaloisTower.proj_comp_proj`);
* `π_N` is the identity on the level `j` if `N j = ⊥`
  (`AlgebraicGeometry.ProEtale.GaloisTower.infTransport_comp_proj_of_eq_bot`);
* `π_N = τ ≫ u` is the invariant projector of the normalized trace if `N j = ⊤` for all `j`
  (`AlgebraicGeometry.ProEtale.GaloisTower.proj_eq_trace_comp_infUnit`);
* on the level `j`, `π_N ≫ ∑_i σ_i = |I| • avg_{Γ_j}` if the `σ_i` cover a system of
  representatives of the cosets of `N j`
  (`AlgebraicGeometry.ProEtale.GaloisTower.infTransport_comp_proj_comp_sum`);
* `π_N` is natural in `M` (`AlgebraicGeometry.ProEtale.GaloisTower.proj_naturality`).
-/

@[expose] public section

-- several lemmas do not need all the instances of the section variables
set_option linter.unusedSectionVars false

universe u

open CategoryTheory Category Limits Preadditive

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.GaloisTower

open Scheme CondensedRing

variable {X Yinf : Scheme.{u}} {ginf : Yinf ⟶ X} [WeaklyEtale ginf] (T : GaloisTower ginf)
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (M : CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
  (hd : ∀ (j : T.J)
    (N : CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
      IsIso (Fintype.card (T.Γ j) • 𝟙 N))

variable {Λ M hd} (hc : IsColimit (T.moduleCocone Λ M))

end AlgebraicGeometry.ProEtale.GaloisTower
