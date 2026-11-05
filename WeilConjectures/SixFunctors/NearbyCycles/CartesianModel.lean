/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.EpiMono
public import WeilConjectures.SixFunctors.NearbyCycles.HomComp

/-!

# The cartesian model of a morphism of models

Let `φ : M ⟶ N` be a morphism of models over `f : X ⟶ Y` and `f' : X' ⟶ Y'`, with morphism
`t : 𝒳_M ⟶ 𝒳_N` of total spaces. The *cartesian model* of `φ`
(`NearbyCyclesModel.Hom.cartesianModel`) has the total space and special fibre of `M`, and
generic fibre the base change `𝒳_{N,η̄} ×_{𝒳_N} 𝒳_M` of the generic fibre of `N` along `t`.
The morphism `φ` factors as
```
M ──toCartesian──→ cartesianModel φ ──fromCartesian──→ N
```
where `toCartesian` (`NearbyCyclesModel.Hom.toCartesian`) is the identity on total spaces and
special fibres, and `fromCartesian` (`NearbyCyclesModel.Hom.fromCartesian`) has a cartesian
square of generic fibres.

By the composition law of the pullback exchanges, `α_φ` is a split monomorphism at `C` as soon
as `α_{fromCartesian}` is an isomorphism at `C` (a base change statement for `Rj_*` along the
cartesian square) and `α_{toCartesian}` is a split monomorphism at `L𝟙^* C` (a statement about
the change of generic fibres only):
`NearbyCyclesModel.Hom.isSplitMono_pullbackExchange_app_of_cartesian`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {f : X ⟶ Y} {f' : X' ⟶ Y'}

namespace Hom

variable (φ : M.Hom N f f')

end Hom

variable {Z Z' : Scheme.{u}} {P : NearbyCyclesModel Z Z'}

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
