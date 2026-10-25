/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.Exchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.TraceFormula.Specialization.TraitModelRestrict

/-!

# The proper exchange of nearby cycles

For a proper morphism `t : 𝒳 ⟶ 𝒴` of total spaces of models of finite type over the strictly
henselian trait `Spec k'⟦t⟧` whose squares of geometric generic fibres and of special fibres are
cartesian, the pushforward exchange `χ_t : Ψ_𝒴 Rt_* ⟶ Rt_{s*} Ψ_𝒳`
(`NearbyCyclesModel.Hom.pushforwardExchange`) of the geometric models is an isomorphism on bounded
constructible complexes (blueprint `det-sp-nearby-cycles-exchanges` (2), "proper exchange",
`NearbyCyclesModel.Hom.isIso_pushforwardExchange_app_of_isProper`).

## Sorried input

The theorem is the blueprint node `det-sp-nearby-cycles-exchanges` (2) of the subsection
`sk-lem-tf-sp-constant-family`, stated here for `ℚ̄_ℓ`-coefficients; it is `sorry`ed, to be
proved with that node (proper base change along the inclusions of the geometric generic fibre and
of the special fibre, and the composition of direct images).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel.Hom

variable {ℓ : ℕ} [Fact ℓ.Prime] {k' : Type u} [Field k'] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]

/-- Blueprint `det-sp-nearby-cycles-exchanges` (2) (**proper exchange of nearby cycles**): let
`M` and `N` be models of finite type over the strictly henselian trait `Spec k'⟦t⟧`, and
`φ : M.geometric ⟶ N.geometric` a morphism of their geometric models whose morphism of total
spaces `t` is proper and whose squares of geometric generic fibres and of special fibres are
cartesian. Then the pushforward exchange `χ_t : Ψ_N Rt_* ⟶ Rt_{s*} Ψ_M` is an isomorphism on
bounded constructible `ℚ̄_ℓ`-complexes: by proper base change along `j_N` and `i_N`, both sides
are `i_N^* Rt_* Rj_{M*} j_M^*`. -/
theorem isIso_pushforwardExchange_app_of_isProper {X Y : Scheme.{u}}
    {X' Y' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
    {N : NearbyCyclesModel Y Y'.left} (hM : M.IsTraitModel) (hN : N.IsTraitModel)
    {t : M.total ⟶ N.total} {f' : X'.left ⟶ Y'.left} (φ : M.geometric.Hom N.geometric t f')
    (ht : φ.total = t) [IsProper t] (hj : IsPullback φ.generic M.j N.j t)
    (hi : IsPullback M.i f' t N.i)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology M.total) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) M.total)))
    (hK : boundedConstructible _ K) :
    IsIso ((φ.pushforwardExchange (Profinite.padicAlgClRingObj ℓ)).app K) :=
  sorry

end NearbyCyclesModel.Hom

end AlgebraicGeometry.ProEtale.CondensedRing
