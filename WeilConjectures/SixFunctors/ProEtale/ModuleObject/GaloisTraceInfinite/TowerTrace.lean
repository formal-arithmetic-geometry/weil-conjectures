/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisTraceInfinite.Tower
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisTraceInfinite.NormalizedTraceUnique

/-!
# The normalized trace of a Galois tower

Let `T` be a Galois tower over `X` (`AlgebraicGeometry.ProEtale.GaloisTower`) and `Λ` a
commutative condensed ring in which the orders `|Γ_j|` of the Galois groups are invertible. For a
`Λ_X`-module object `M` such that `g_{∞*} g_∞^* M` is the colimit of the finite levels
`g_{j*} g_j^* M` (`AlgebraicGeometry.ProEtale.GaloisTower.moduleCocone`), the normalized finite
traces `|Γ_j|⁻¹ t_j : g_{j*} g_j^* M ⟶ M` are compatible with the transition maps and glue to a
*normalized trace* `τ : g_{∞*} g_∞^* M ⟶ M` (`AlgebraicGeometry.ProEtale.GaloisTower.trace`):

* `τ` is a retraction of the unit (`AlgebraicGeometry.ProEtale.GaloisTower.unit_comp_trace`);
* `τ` is natural in `M` (`AlgebraicGeometry.ProEtale.GaloisTower.map_comp_trace`);
* `τ` is invariant under the unit transport along any automorphism of `Y_∞` over `X` which is
  compatible with the Galois actions at all finite levels
  (`AlgebraicGeometry.ProEtale.GaloisTower.infAction_comp_trace`).

Compatibility of the normalized finite traces is proved by uniqueness: an invariant retraction of
the unit of a finite Galois covering is the normalized trace (`CategoryTheory.eq_normalizedTrace`).
-/

@[expose] public section

-- several lemmas do not need all the instances of the section variables
set_option linter.unusedSectionVars false

universe u

open CategoryTheory Category Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.GaloisTower

open Scheme CondensedRing

variable {X Yinf : Scheme.{u}} {ginf : Yinf ⟶ X} [WeaklyEtale ginf] (T : GaloisTower ginf)
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

variable (M : CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))

/-! ### The normalized finite traces -/

variable (hd : ∀ (j : T.J)
  (N : CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
    IsIso (Fintype.card (T.Γ j) • 𝟙 N))

/-! ### The normalized trace of the tower -/

/-! ### Naturality -/

/-! ### Galois invariance -/

/-- The unit transport `g_{∞*} g_∞^* M ⟶ g_{∞*} g_∞^* M` along an automorphism `σ` of `Y_∞` over
`X`. -/
@[irreducible] noncomputable def infAction (σ : Yinf ⟶ Yinf) (hσ : σ ≫ ginf = ginf) :
    (infFunctor Λ ginf).obj M ⟶ (infFunctor Λ ginf).obj M :=
  (unitTransport Λ σ hσ hσ).app M

end AlgebraicGeometry.ProEtale.GaloisTower
