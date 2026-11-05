/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarAmplitude
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdicFiniteness
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarIntegralAmplitude
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushPadicSubfieldFinite

/-!
# A uniform bound for the proper direct image of constructible `ℓ`-adic sheaves

Let `p : Z ⟶ Y` be a proper morphism to a `k`-scheme of finite type, `ℓ` invertible in `k`, and
`d` a bound for the dimensions of the geometric fibres of `p`. For the `ℓ`-adic coefficient rings
`Λ = 𝒪_E, E, ℚ̄_ℓ` (`E ⊆ ℚ̄_ℓ` a finite subextension), `Rp_*` sends every constructible
`Λ_Z`-module, placed in degree `0`, into degrees `≤ 2d`, with `d` independent of `E` (blueprints
`det-proper-heart-bound-torsion`, `det-proper-heart-bound-rational`):

* `exists_isLE_rightDerivedLowerStar_singleFunctor_padicIntegers`: for `𝒪_E`, from
  `isLE_rightDerivedLowerStar_singleFunctor_padicIntegers_of_isProper` (reduction modulo a
  uniformizer and the torsion bound `2d`);
* `exists_isLE_rightDerivedLowerStar_singleFunctor_continuousMapRingObj`: for `E`, a constructible
  `E`-module `N` being `E ⊗ᴸ K₀` for a bounded constructible `𝒪_E`-complex `K₀`
  (`isLE_rightDerivedLowerStar_singleFunctor_of_extendScalars`);
* `exists_isLE_rightDerivedLowerStar_singleFunctor_padicAlgClRingObj`: for `ℚ̄_ℓ`, in the same way
  from a finite subextension `E`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k ≠ ℓ)]
  {Z Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
  (p : Z ⟶ Y) [IsProper p]

/-! ### The uniform bound on constructible sheaves -/

end AlgebraicGeometry.ProEtale.CondensedRing
