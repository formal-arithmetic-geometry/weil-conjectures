/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperNoetherianBase
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.WeaklyEtale
public import WeilConjectures.TraceFormula.Specialization.NearbyDualizingMap
public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethGlobal
public import WeilConjectures.SixFunctors.NearbyCycles.PushforwardExchangeSquare

/-!

# The proper exchange of a proper trait model over the base

Let `M` be a trait model of a `k`-scheme `X` over the base (`NearbyCyclesModel.IsTraitModelOfBase`)
with proper total space, whose geometric generic fibre is all of `X ×_k Spec Ω`. The proper
exchange `χ_a : Ψ_S Ra_* ⟶ Ra'_* Ψ_M` of the structure morphism `a : X ⟶ Spec k`
(`NearbyCyclesModel.IsTraitModelOfBase.pushforwardExchange`) is an isomorphism on bounded
constructible complexes (`NearbyCyclesModel.IsTraitModelOfBase.isIso_pushforwardExchange_app`).
The proof works on the ambient derived categories
(`NearbyCyclesModel.IsTraitModelOfBase.isIso_pushforwardExchange_app_ambient`) and then restricts
to `Dᵇc` through `NearbyCyclesModel.Hom.boundedConstructiblePushforwardExchange_app_hom`.

The proof compares `χ_a` with the proper exchange of the model `M` of its geometric generic fibre
over the trait as a model of `Spec Ω` (`NearbyCyclesModel.IsTraitModelOver.toTraitGeneric`,
invertible by blueprint `det-sp-nearby-cycles-exchanges` (2),
`NearbyCyclesModel.IsTraitModelOver.isIso_pushforwardExchange_toTraitGeneric_app`): by the square
law of the pullback exchanges, the two differ by `Ψ_S` of the base change morphism
`Lε^* Ra_* ⟶ Rg_* Lε^*` of the cartesian square of generic fibres, which is invertible by proper
base change (blueprint `sk-thm-sfb-proper-base-change`,
`ProEtale.CondensedRing.isIso_baseChangeMap_app_padicAlgCl_of_isProper`), and
by pullback exchanges along identities (`NearbyCyclesModel.pushforwardExchange_square_aux`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### Restriction to bounded constructible complexes -/

namespace NearbyCyclesModel

section Restricted

variable (ℓ : ℕ) [Fact ℓ.Prime] {k k' : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [Field k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)]
  {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {X' Y' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {M : NearbyCyclesModel X.left X'.left} {N : NearbyCyclesModel Y.left Y'.left}
  {f : X ⟶ Y} {f' : X' ⟶ Y'}

end Restricted

end NearbyCyclesModel

/-! ### The proper exchange of a proper trait model -/

namespace NearbyCyclesModel

variable (k : Type u) [Field k] (k' : Type u) [Field k'] [Algebra k k']

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

variable {k k'} (ℓ : ℕ) [Fact ℓ.Prime]
  {X : Over (Spec (.of k))} {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X.left X'.left}
  {q : M.total ⟶ trait k'} {g : M.generic ⟶ Spec (.of (traitGenericField k'))}

set_option hygiene false in
/-- The condensed field `ℚ̄_ℓ`. -/
local notation "𝐐" => Profinite.padicAlgClRingObj ℓ

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
