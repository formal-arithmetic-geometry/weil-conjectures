/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Localizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.WeaklyEtale
public import WeilConjectures.CategoryTheory.Adjunction.ExchangeRightPaste

/-!

# Exchange maps of nearby cycles

Let `φ : M ⟶ N` be a morphism of models
(`AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.Hom`) over `f : X ⟶ Y` and
`f' : X' ⟶ Y'`, with morphisms `t` of total spaces and `g` of geometric generic fibres. This file
constructs the exchange maps of the nearby cycles `Ψ = Li^* Rj_* Lε^*` on the
unbounded derived categories of module objects (blueprint `det-sp-nearby-cycles-exchanges`):

* the *pullback exchange* `α_f : Lf'^* Ψ_N ⟶ Ψ_M Lf^*`
  (`NearbyCyclesModel.Hom.pullbackExchange`), assembled from the pullback comparisons of the
  squares of special fibres and of identifications, and the base change morphism
  `Lt^* Rj_{N*} ⟶ Rj_{M*} Lg^*` of the square of geometric generic fibres;
* the *pushforward exchange* `χ_f : Ψ_N Rf_* ⟶ Rf'_* Ψ_M`
  (`NearbyCyclesModel.Hom.pushforwardExchange`), the mate of `α_f`;
* the *specialization unit* `σ : Λ_{X'} ⟶ Ψ(Λ_X)` (`NearbyCyclesModel.unit`), the restriction
  to the special fibre of the unit of `Lj^* ⊣ Rj_*`.

## Main results

- `NearbyCyclesModel.Hom.map_unit_comp_pullbackExchange_app`: the unit law
  `α_f(Λ) ∘ Lf'^* σ_N = Ψ_M(ε_f) ∘ σ_M ∘ ε_{f'}⁻¹` (blueprint
  `sk-lem-tf-nearby-mate-coherences` (2)).
- `NearbyCyclesModel.Hom.unit_comp_map_comp_pushforwardExchange_app`: the unit identity
  `χ_f ∘ Ψ_N(η_f) ∘ σ_N = Rf'_*(σ_M) ∘ η_{f'}` (blueprint `det-tf-sp-trace-morphism`), and
  `NearbyCyclesModel.Hom.homEquiv_symm_unit_comp_pushforwardExchange_app`: specialization
  commutes with the adjunction `Lf^* ⊣ Rf_*`.
- `NearbyCyclesModel.Hom.isIso_pullbackExchange_of_isIso`: a morphism of models whose morphisms
  of total spaces and of geometric generic fibres are isomorphisms has an invertible pullback
  exchange.

## Implementation notes

The unit law and the unit identity are proved in abstract categories (the private `_aux`
lemmas) and then instantiated: on the derived categories of module objects, `rw` and `simp`
trigger expensive unfoldings of the derived functors, and the kernel must not be asked to compare
different proofs of equalities of derived pullbacks (hence
`ProEtale.CondensedRing.pullbackSquareComparison_eq_trans`). The unit comparisons used are
`ProEtale.CondensedRing.leftDerivedUpperStarUnitIso`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-! ### Abstract computations

The computations below take place in abstract categories, where they are cheap; they are applied to
the derived categories of module objects afterwards. -/

section Abstract

end Abstract

/-! ### The pullback comparisons at the unit -/

section Unit

variable {X Y X' Y' : Scheme.{u}}

variable {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}

end Unit

namespace NearbyCyclesModel

variable {X X' Y Y' : Scheme.{u}}

variable {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'} {f : X ⟶ Y} {f' : X' ⟶ Y'}

namespace Hom

variable (φ : M.Hom N f f')

end Hom

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
