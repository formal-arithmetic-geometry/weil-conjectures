/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.BoundedConstructibleUnitIdentity
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.WeaklyEtale
public import WeilConjectures.CategoryTheory.Adjunction.ExchangeRightPaste

/-!

# Nearby cycles and weakly étale pullback

Let `φ : M ⟶ N` be a morphism of models (`NearbyCyclesModel.Hom`) whose morphism of total spaces
`t : 𝒳_M ⟶ 𝒳_N` is weakly étale (for instance an open immersion) and whose square of geometric
generic fibres
```
𝒳_{M,η̄} --g--> 𝒳_{N,η̄}
   |j_M            |j_N
   v               v
  𝒳_M  ----t---->  𝒳_N
```
is cartesian. Then the pullback exchange `α_f : Lf'^* Ψ_N ⟶ Ψ_M Lf^*`
(`NearbyCyclesModel.Hom.pullbackExchange`) is an isomorphism
(`NearbyCyclesModel.Hom.isIso_pullbackExchange_of_weaklyEtale`; blueprint
`det-sp-nearby-cycles-exchanges` (1), "nearby-cycle open pullback"). Indeed `α_f` is assembled
from two pullback comparisons, which are isomorphisms, and from the mate of the pullback comparison
of the square of geometric generic fibres, which is the base change morphism
`Lt^* Rj_{N*} ⟶ Rj_{M*} Lg^*` (`NearbyCyclesModel.Hom.baseChangeMap_commSq_j_eq_mateEquiv`),
invertible by weakly étale base change
(`ProEtale.CondensedRing.isIso_baseChangeMap_of_weaklyEtale`).

The pullback exchange restricts to bounded constructible complexes
(`NearbyCyclesModel.Hom.boundedConstructiblePullbackExchange`, defined in
`WeilConjectures.SixFunctors.NearbyCycles.BoundedConstructibleUnitIdentity`), where it is again an
isomorphism in the weakly étale case
(`NearbyCyclesModel.Hom.isIso_boundedConstructiblePullbackExchange_of_weaklyEtale`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

namespace Hom

section Abstract

end Abstract

section Ambient

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {f : X ⟶ Y} {f' : X' ⟶ Y'} (φ : M.Hom N f f')

end Ambient

section BoundedConstructible

variable (ℓ : ℕ) [Fact ℓ.Prime] {k k' : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [Field k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)]
  {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {X' Y' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {M : NearbyCyclesModel X.left X'.left} {N : NearbyCyclesModel Y.left Y'.left}
  {f : X ⟶ Y} {f' : X' ⟶ Y'}
  (φ : M.Hom N f.left f'.left)
  (hM : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
  (hN : N.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))

end BoundedConstructible

end Hom

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
