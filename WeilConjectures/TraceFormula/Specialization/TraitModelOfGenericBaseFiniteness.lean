/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyFiniteness
public import WeilConjectures.TraceFormula.Specialization.TraitModelOfGenericBase

/-!

# Finiteness for trait models over a generic base

Let `M` be a trait model of an `F`-scheme `X₁` over the generic base `(F, X₁)`
(`NearbyCyclesModel.IsTraitModelOfGenericBase`): a model of finite type over the strictly
henselian trait `S = Spec k'⟦t⟧` whose generic fibre `𝒳_η = 𝒳 ×_S η` maps to `X₁` (by an open
immersion into `X₁ ×_F η`) compatibly with `ε`. Its nearby cycles `Ψ = Li^* Rj_* Lε^*` preserve
bounded constructible complexes
(`NearbyCyclesModel.IsTraitModelOfGenericBase.preservesBoundedConstructible`).

Unlike `NearbyCyclesModel.preservesBoundedConstructible_of_isTraitModel`, the identification `ε`
need not factor through the total space `𝒳`, only through the generic fibre `𝒳_η`, which is open
in `𝒳` as `η` is open in `S`. For bounded constructible `K` on `X₁`, let `A` be its pullback to
`𝒳_η` and `B = v_! A` its extension by zero along the open immersion `v : 𝒳_η ⟶ 𝒳`, bounded
constructible on `𝒳`. As `j : 𝒳_Ω ⟶ 𝒳` factors through `v`, `Lj^* B ≅ Lε^* K`, so
`Ψ K ≅ Li^* Rj_* Lj^* B` is bounded constructible by Deligne's finiteness theorem
(`NearbyCyclesModel.boundedConstructible_geometricNearbyCycles_obj`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {k' : Type u} [Field k'] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] {X' : Over (Spec (.of k'))}
  {F : Type u} [Field F]

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
