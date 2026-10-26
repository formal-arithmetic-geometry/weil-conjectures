/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.ProperExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperGeneralBase
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.TraceFormula.Specialization.TraitModelRestrict
public import WeilConjectures.Tactic.ExactModProofs

/-!

# The proper exchange of nearby cycles

For a morphism `φ : M ⟶ N` of nearby cycles models over a proper `f` whose morphism of total spaces
is proper and whose squares of special fibres and of identifications `ε` are cartesian, the
pushforward exchange `χ_f : Ψ_N Rf_* ⟶ Rf'_* Ψ_M` (`NearbyCyclesModel.Hom.pushforwardExchange`) is
an isomorphism on bounded constructible complexes (blueprint `det-sp-nearby-cycles-exchanges` (2),
"proper exchange", `NearbyCyclesModel.Hom.isIso_pushforwardExchange_app_of_isProper`). For the
geometric models of models of finite type over the trait `Spec k'⟦t⟧`, whose identifications are
the inclusions of the geometric generic fibres, this is
`NearbyCyclesModel.Hom.isIso_pushforwardExchange_app_of_isProper_geometric`.

The proof follows the blueprint. The component of `χ_f` at `K` is
`Li_N^* Rj_{N*}` of the base change morphism of the square of identifications, followed by the
composition of direct images `Rj_{N*} Rg_* ≅ Rt_* Rj_{M*}` and by the base change morphism of the
square of special fibres at `Rj_{M*} Lε_M^* K`
(`NearbyCyclesModel.Hom.pushforwardExchange_app`). The first is invertible by proper base change
for `f` (`ProEtale.CondensedRing.isIso_baseChangeMap_app_of_isProper_padicAlgCl`), the last by
proper base change for the morphism of total spaces
(`NearbyCyclesModel.Hom.isIso_baseChangeMap_commSq_i_app_of_isProper`).

## Sorried input

`NearbyCyclesModel.Hom.isIso_baseChangeMap_commSq_i_app_of_isProper` is the proper base change
step `ī^* Rt̄_* ≃ Rt_{s*} ī'^*` of the proof of blueprint `det-sp-nearby-cycles-exchanges` (2),
applied to the generic direct image `Rj_{M*} Lε_M^* K`, which is not bounded constructible. The
blueprint applies proper base change for bounded below complexes with torsion coefficients
(blueprint `thm-weil-pbc-bounded-below`); for `ℚ̄_ℓ`-coefficients the base change morphism is
only known to be invertible after derived completion, and the comparison with the ordinary
pullback uses the finiteness of nearby cycles (SGA 4½, [Th. finitude]). It is `sorry`ed.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel.Hom

variable {ℓ : ℕ} [Fact ℓ.Prime] {k' : Type u} [Field k']

/-- **Proper base change along the special fibre for the generic direct image** (the step
`ī^* Rt̄_* ≃ Rt_{s*} ī'^*` of the proof of blueprint `det-sp-nearby-cycles-exchanges` (2); there
by blueprint `thm-weil-pbc-bounded-below` for torsion coefficients; SGA 7 XIII 2.1.7): if the
morphism `t` of total spaces of a morphism of models is proper and the square of special fibres is
cartesian, the base change morphism `Li_N^* Rt_* ⟶ Rf'_* Li_M^*` is invertible at the generic
direct image `Rj_{M*} Lε_M^* K` of a bounded constructible `ℚ̄_ℓ`-complex `K`. -/
theorem isIso_baseChangeMap_commSq_i_app_of_isProper
    {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} (φ : M.Hom N f f') [IsProper φ.total]
    (hi : IsPullback M.i f' φ.total N.i)
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))}
    (hK : boundedConstructible _ K) :
    IsIso ((baseChangeMap (Profinite.padicAlgClRingObj ℓ) φ.commSq_i).app
      (R((M.j)_*⟦Profinite.padicAlgClRingObj ℓ⟧).obj
        (L((M.ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj K))) :=
  sorry

/-- **Proper base change for nearby cycles** (blueprint `det-sp-nearby-cycles-exchanges` (2),
proper half; SGA 7 XIII 2.1.7): if the morphism of total spaces and `f` are proper and the squares
of special fibres and of identifications `ε` are cartesian, the pushforward exchange
`χ_f : Ψ_N Rf_* ⟶ Rf'_* Ψ_M` is invertible on bounded constructible complexes: by proper base change
along `ε_N` and `i_N`, both sides are `i_N^* Rt_* Rj_{M*} Lε_M^*`
(`NearbyCyclesModel.Hom.pushforwardExchange_app`). (The `ε`-square cannot be dropped: `Rf_*` must
commute with the base change to the geometric generic fibre.) -/
theorem isIso_pushforwardExchange_app_of_isProper
    {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} (φ : M.Hom N f f') [IsProper φ.total] [IsProper f]
    (hi : IsPullback M.i f' φ.total N.i) (hε : IsPullback M.ε φ.generic f N.ε)
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))}
    (hK : boundedConstructible _ K) :
    IsIso ((φ.pushforwardExchange (Profinite.padicAlgClRingObj ℓ)).app K) := by
  have h₁ := isIso_baseChangeMap_app_of_isProper_padicAlgCl ℓ φ.commSq_ε hε K hK
  have h₂ := φ.isIso_baseChangeMap_commSq_i_app_of_isProper hi hK
  have h₃ := φ.isIso_pushforwardExchange_app_of_isIso_baseChangeMap
    (Profinite.padicAlgClRingObj ℓ) K (by exact_mod_proofs h₁) (by exact_mod_proofs h₂)
  exact_mod_proofs h₃
/-- **The proper exchange for geometric models** (blueprint `det-sp-nearby-cycles-exchanges` (2)):
let `M` and `N` be models over `Spec k'⟦t⟧`, and `φ : M.geometric ⟶ N.geometric` a morphism of
their geometric models whose morphism of total spaces `t` is proper and whose squares of geometric
generic fibres and of special fibres are cartesian. Then the pushforward exchange
`χ_t : Ψ_N Rt_* ⟶ Rt_{s*} Ψ_M` is an isomorphism on bounded constructible `ℚ̄_ℓ`-complexes. This
is `isIso_pushforwardExchange_app_of_isProper` for the geometric models, whose identifications `ε`
are the inclusions `j` of the geometric generic fibres. -/
theorem isIso_pushforwardExchange_app_of_isProper_geometric {X Y : Scheme.{u}}
    {X' Y' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
    {N : NearbyCyclesModel Y Y'.left} {t : M.total ⟶ N.total} {f' : X'.left ⟶ Y'.left}
    (φ : M.geometric.Hom N.geometric t f') (ht : φ.total = t) [IsProper t]
    (hj : IsPullback φ.generic M.j N.j t) (hi : IsPullback M.i f' t N.i)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology M.total) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) M.total)))
    (hK : boundedConstructible _ K) :
    IsIso ((φ.pushforwardExchange (Profinite.padicAlgClRingObj ℓ)).app K) := by
  have : IsProper φ.total := by rw [ht]; infer_instance
  exact φ.isIso_pushforwardExchange_app_of_isProper (by rw [ht]; exact hi) hj.flip hK

end NearbyCyclesModel.Hom

end AlgebraicGeometry.ProEtale.CondensedRing
