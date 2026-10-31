/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.AutActionTrivial
public import WeilConjectures.SixFunctors.NearbyCycles.GaloisAction

/-!

# Pullback exchanges of equivariant morphisms of models

Let `θ : M ⟶ N` be a morphism of models over `f, f'`, and `σ : M ⟶ M`, `τ : N ⟶ N` morphisms of
models over the identities with `σ ≫ θ = θ ≫ τ` on total spaces and geometric generic fibres.
Then the pullback exchange of `θ` intertwines the actions of `σ` and `τ` on nearby cycles
(`NearbyCyclesModel.Hom.pullbackExchange_app_comp_autAction_of_comm`):
```
α_θ(C) ≫ σ(Lf^* C) = Lf'^*(τ(C)) ≫ α_θ(C).
```
Both sides are the pullback exchange of the composite, by the composition law of pullback
exchanges (`NearbyCyclesModel.Hom.pullbackExchange_comp_app_of_eq`) applied to the two
factorizations. In particular if `τ` acts trivially (for instance by the invariance of nearby
cycles under change of trait, `NearbyCyclesModel.Hom.autAction_eq_id_of_isIso`), the exchange of
`θ` lands in the `σ`-invariants.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {f : X ⟶ Y} {f' : X' ⟶ Y'}

/-- **Pullback exchanges of equivariant morphisms of models intertwine the actions**: if
`σ ≫ θ = θ ≫ τ` on total spaces and geometric generic fibres, then
`α_θ(C) ≫ σ(Lf^* C) = Lf'^*(τ(C)) ≫ α_θ(C)`. -/
lemma Hom.pullbackExchange_app_comp_autAction_of_comm (θ : M.Hom N f f')
    (σ : M.Hom M (𝟙 X) (𝟙 X')) (τ : N.Hom N (𝟙 Y) (𝟙 Y'))
    (htot : σ.total ≫ θ.total = θ.total ≫ τ.total)
    (hgen : σ.generic ≫ θ.generic = θ.generic ≫ τ.generic)
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :
    (θ.pullbackExchange Λ).app C ≫ σ.autAction Λ (L((f)^*⟦Λ⟧).obj C) =
      (L((f')^*⟦Λ⟧)).map (τ.autAction Λ C) ≫ (θ.pullbackExchange Λ).app C :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
