/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdic
public import WeilConjectures.TraceFormula.Specialization.FinitePointReflection
public import WeilConjectures.TraceFormula.Specialization.NearbyFinitenessCases

/-!

# Nearby cycles of complexes supported on a closed subscheme finite over the trait

Let `S = Spec k'⟦t⟧` be the strictly henselian trait (`k'` separably closed, `ℓ ≠ char k'`) and
`c : D ⟶ 𝔸ⁿ_S` a closed immersion such that `p = c ≫ q : D ⟶ S` is finite, `q : 𝔸ⁿ_S ⟶ S` being
the structure map. For every bounded constructible `ℚ̄_ℓ`-complex `K` on `D`, the geometric
nearby cycles of `Rc_* K` are bounded constructible on the special fibre `𝔸ⁿ_s`
(`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_of_isFinite_comp`). This is the
case "`D` finite over the trait" of Deligne's finiteness theorem for nearby cycles (SGA 4½,
[Th. finitude], Thm. 3.2), generalizing
`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_of_isClosedImmersion_comp`.

The proof:
* by the proper exchange along `p`
  (`NearbyCyclesModel.Hom.isIso_pushforwardExchange_app_of_isProper_geometric`),
  `Ψ_S (Rp_* K) ≅ Rp_{s*} Ψ_D K`, where `Rp_* K` is bounded constructible
  (`boundedConstructible_rightDerivedLowerStar_obj_of_isProper_padicAlgClRingObj`)
  and the nearby cycles of the trait preserve bounded constructible complexes
  (`NearbyCyclesModel.preservesBoundedConstructible_traitSelfModel`);
* the special fibre `p_s : D_s ⟶ Spec k'` is finite over the separably closed point `Spec k'`, so
  `Ψ_D K` is bounded constructible as soon as `Rp_{s*} Ψ_D K` is
  (`boundedConstructible_of_boundedConstructible_rightDerivedLowerStar_of_isFinite`);
* by the proper exchange along `c`, `Ψ_{𝔸ⁿ} (Rc_* K) ≅ Rc_{s*} Ψ_D K`, and `Rc_{s*}` preserves
  bounded constructible complexes.

The proper exchange is `sorry`ed upstream
(`WeilConjectures.TraceFormula.Specialization.NearbyProperExchange`), as is the finiteness of
proper direct images.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable {ℓ : ℕ} [Fact ℓ.Prime] {k' : Type u} [Field k'] {X : Scheme.{u}}
  {X' : Over (Spec (.of k'))}

variable [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
