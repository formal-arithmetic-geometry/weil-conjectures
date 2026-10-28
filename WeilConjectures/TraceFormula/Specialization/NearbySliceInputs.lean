/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.AffineSpaceSliceModel
public import WeilConjectures.SixFunctors.NearbyCycles.CartesianModel

/-!

# The two inputs of the slice step of Deligne's finiteness theorem

Let `S = Spec k'⟦t⟧` with `k'` separably closed of characteristic `p ≠ ℓ`, `K = k'(x)^alg`,
`T = Spec K⟦t⟧`, and let `φ = NearbyCyclesModel.affineSpaceSliceHom k' n i` be the morphism of
geometric models over the coordinate generic slice `h : 𝔸ⁿ_T ⟶ 𝔸ⁿ⁺¹_S`. Write `X = 𝔸ⁿ⁺¹_S`,
`X_T = 𝔸ⁿ_T`, `Ω = (Frac k'⟦t⟧)^alg` and `Ω_K = (Frac K⟦t⟧)^alg`. The morphism `φ` factors
through its cartesian model (`NearbyCyclesModel.Hom.cartesianModel`), whose generic fibre is
`X_T ×_S Spec Ω = X_Ω ×_X X_T`:
```
X_T ×_T Ω_K ──π──→ X_T ×_S Ω ──h'──→ X_Ω
      │                │               │ j
      └─────── X_T ────┴──────h──────→ X
```
The slice step (`NearbyCyclesModel.isSplitMono_pullbackExchange_app_affineSpaceSliceHom`) is
deduced from the two statements of this file through
`NearbyCyclesModel.Hom.isSplitMono_pullbackExchange_app_of_cartesian`:

* **(M1)** `NearbyCyclesModel.isIso_pullbackExchange_app_fromCartesian_affineSpaceSliceHom`: the
  base change `Lh^* Rj_* ⟶ Rj'_* Lh'^*` along the cartesian right-hand square is invertible on
  bounded constructible complexes from `X`, after restriction to the special fibre. On stalks
  at a geometric point `x̄` of `𝔸ⁿ_K`, with `S'` the strict localization of `𝔸¹_S` at the generic
  point of its special fibre and `X' = X ×_{𝔸¹_S} S'`, both sides are the invariants
  `RΓ(P, Ψ_{X'/S'}(B)_x̄)` under the pro-`p` kernel `P` of `I_{S'} ⟶ I_S`: for the left side by
  weakly étale localization along `S' ⟶ 𝔸¹_S`, for the right side by the invariance of nearby
  cycles under the extension of strictly henselian traits `T ⟶ S'` (SGA 4½, [Th. finitude], 3.7),
  since `I_T ⟶ I_{S'}` maps the kernel of `I_T ⟶ I_S` onto `P`.
* **(M2)** `NearbyCyclesModel.isSplitMono_pullbackExchange_app_toCartesian_affineSpaceSliceHom`:
  the change of generic fibres `π : X_T ×_T Ω_K ⟶ X_T ×_S Ω` is, up to a universal
  homeomorphism, a torsor under the kernel of `I_T ⟶ I_S`, a pro-`p` group (the uniformizer `t`
  identifies the tame quotients), so the unit `G ⟶ Rπ_* Lπ^* G` is split by the normalized trace
  (averaging over the finite `p`-group quotients, `p` invertible in `ℚ̄_ℓ`; SGA 4½,
  [Th. finitude], proof of Lemme 3.3). The pullback exchange of `toCartesian` is `i^* Rj'_*` of
  this unit.

## Unfinished

Both statements are `sorry`ed. (M2) is proved on `trace2/nearby-prop-averaging` (the pro-`p`
averaging splitting). (M1) needs the invariance of nearby cycles under extensions of strictly
henselian traits for pro-étale `ℚ̄_ℓ`-sheaves (SGA 4½, [Th. finitude], 3.7), which in turn rests
on the finiteness theorem in lower dimension and on the comparison of `I_T` and `I_{S'}`. The
completed trait `T = Spec K⟦t⟧` is not weakly étale over `𝔸¹_S` (its residue field `K` is a
purely inseparable extension of `k'(x)^sep` and `K⟦t⟧` is not ind-étale over the strict
henselization), so neither weakly étale base change
(`ProEtale.CondensedRing.isIso_baseChangeMap_of_weaklyEtale`) nor smooth base change applies to
the square directly.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable {ℓ : ℕ} [Fact ℓ.Prime] {k' : Type u} [Field k'] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]

/-- **(M1) Base change along the cartesian slice square** (SGA 4½, [Th. finitude], 3.7, with
weakly étale localization along the strict localization of `𝔸¹_S`): for a bounded constructible
complex `B` on `𝔸ⁿ⁺¹_S`, the pullback exchange of the second factor
`cartesianModel φ ⟶ (affineSpaceModel k' (n + 1)).geometric` of the morphism of models over the
coordinate generic slice, whose square of generic fibres is cartesian, is an isomorphism at `B`.
See the module docstring; `sorry`ed. -/
theorem isIso_pullbackExchange_app_fromCartesian_affineSpaceSliceHom (n : ℕ) (i : Fin (n + 1))
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (affineSpaceModel k' (n + 1)).total)
      Ab.{u + 1}) (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
        (affineSpaceModel k' (n + 1)).total))}
    (hB : boundedConstructible _ B) :
    IsIso (((affineSpaceSliceHom k' n i).fromCartesian.pullbackExchange
      (Profinite.padicAlgClRingObj ℓ)).app B) :=
  sorry

/-- **(M2) The pro-`p` averaging splitting on the slice** (SGA 4½, [Th. finitude], proof of
Lemme 3.3; proved on `trace2/nearby-prop-averaging`): for a bounded constructible complex `B` on
`𝔸ⁿ⁺¹_S`, the pullback exchange of the first factor
`(affineSpaceModel (traitSliceField k') n).geometric ⟶ cartesianModel φ` of the morphism of
models over the coordinate generic slice is a split monomorphism at `B`: it is `i^* Rj'_*`
of the unit `G ⟶ Rπ_* Lπ^* G` of the change of generic fibres `π`, a torsor under a pro-`p`
group up to a universal homeomorphism, which is split by averaging since `p ≠ ℓ`. See the module
docstring; `sorry`ed. -/
theorem isSplitMono_pullbackExchange_app_toCartesian_affineSpaceSliceHom (n : ℕ)
    (i : Fin (n + 1))
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (affineSpaceModel k' (n + 1)).total)
      Ab.{u + 1}) (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
        (affineSpaceModel k' (n + 1)).total))}
    (hB : boundedConstructible _ B) :
    IsSplitMono (((affineSpaceSliceHom k' n i).toCartesian.pullbackExchange
      (Profinite.padicAlgClRingObj ℓ)).app B) :=
  sorry

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
