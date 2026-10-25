/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.BoundedConstructible
public import WeilConjectures.TraceFormula.Specialization.TraitModel

/-!

# Deligne's finiteness theorem for nearby cycles

Over the strictly henselian trait `Spec k'⟦t⟧`, the nearby cycles of a model of finite type
preserve bounded constructible `ℚ̄_ℓ`-complexes
(`ProEtale.CondensedRing.NearbyCyclesModel.preservesBoundedConstructible_of_isTraitModel`).

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {k' : Type u} [Field k'] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]

/-- **Deligne's finiteness theorem for nearby cycles** (SGA 4½, [Th. finitude], Thm. 3.2; for
`ℚ̄_ℓ`-coefficients by passage to the limit, Bhatt–Scholze §6.8): over the strictly henselian
trait `Spec k'⟦t⟧`, `k'` separably closed, the nearby cycles `Ψ = Li^* Rj_* Lε^*` of a model of
finite type whose identification `ε = j ≫ e` factors through the total space preserve bounded
constructible complexes. The pullback `Le^*` to the total space preserves them, the complex
`Lj^* Le^* A` comes from the generic fibre, and `Li^* Rj_*` preserves such complexes by Deligne's
theorem. (Without the factorization of `ε`, `Ψ` would have to be finite on all bounded
constructible `ℚ̄_ℓ`-complexes on the geometric generic fibre, also those not defined over any
finite extension of the generic point, which Deligne's theorem does not cover.)

No blueprint node states this theorem; it is the analogue over the trait of
`lem-sfb-dc-lower-star-preserves`
(`ProEtale.CondensedRing.boundedConstructible_rightDerivedLowerStar_obj`, for morphisms of finite
type over a field). -/
theorem NearbyCyclesModel.preservesBoundedConstructible_of_isTraitModel {X : Scheme.{u}}
    {X' : Over (Spec (.of k'))} (M : NearbyCyclesModel X X'.left) (hM : M.IsTraitModel)
    (hε : ∃ e : M.total ⟶ X, M.j ≫ e = M.ε) :
    M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ) :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
