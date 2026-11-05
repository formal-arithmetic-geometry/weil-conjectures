/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisTraceInfinite.UnitTransport
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Limits

/-!
# Towers of finite Galois coverings

A *Galois tower* over a scheme `X` (`AlgebraicGeometry.ProEtale.GaloisTower`) is a directed
system of finite étale Galois coverings `g_j : Y_j ⟶ X` with groups `Γ_j`, transition maps
`Y_{j'} ⟶ Y_j` over `X` along which the Galois actions lift, and a cone `π_j : Y_∞ ⟶ Y_j` over `X`
with `g_∞ : Y_∞ ⟶ X` weakly étale. The example is `Y_j = G ×_L L_j`, `Y_∞ = G ×_L Ω` for a
Galois extension `Ω/L` with finite Galois subextensions `L_j`.

For a commutative condensed ring `Λ` and a `Λ_X`-module object `M`, the unit transports along the
transition maps and along the `π_j` form a diagram `j ↦ g_{j*} g_j^* M` with a cocone to
`g_{∞*} g_∞^* M` (`AlgebraicGeometry.ProEtale.GaloisTower.moduleDiagram`,
`AlgebraicGeometry.ProEtale.GaloisTower.moduleCocone`). It is a colimit as soon as the
corresponding cocone of abelian sheaves of restrictions is
(`AlgebraicGeometry.ProEtale.GaloisTower.isColimitModuleCocone`).

Everything is stated for an abstract tower: the unit transports of module objects at concrete
pullback schemes are expensive for the kernel, and an abstract statement is instantiated once.
-/

@[expose] public section

-- several lemmas do not need all the instances of the section variables
set_option linter.unusedSectionVars false

universe u

open CategoryTheory Category Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme

namespace GaloisTower

attribute [instance] preorder isDirected nonempty weaklyEtale surjective quasiCompact
  group fintype

variable {X Yinf : Scheme.{u}} {ginf : Yinf ⟶ X} [WeaklyEtale ginf] (T : GaloisTower ginf)

/-! ### Abelian sheaves -/

/-! ### Module objects -/

open CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

variable (M : CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))

/-- The unit transport `g_{j*} g_j^* M ⟶ g_{j'*} g_{j'}^* M` along the transition map. -/
@[irreducible] noncomputable def transport {j j' : T.J} (h : j ≤ j') :
    (T.levelFunctor Λ j).obj M ⟶ (T.levelFunctor Λ j').obj M :=
  (unitTransport Λ (T.t h) (T.t_g h) (T.t_g h)).app M

/-- The unit transport `g_{j*} g_j^* M ⟶ g_{∞*} g_∞^* M` along the projection. -/
@[irreducible] noncomputable def infTransport (j : T.J) :
    (T.levelFunctor Λ j).obj M ⟶ (infFunctor Λ ginf).obj M :=
  (unitTransport Λ (T.π j) (T.π_g j) (T.π_g j)).app M

end GaloisTower

end AlgebraicGeometry.ProEtale
