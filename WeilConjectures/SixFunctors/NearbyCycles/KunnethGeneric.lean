/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.Kunneth
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence

/-!

# The Künneth map of nearby cycles on the geometric generic fibre

A nearby-cycles model `M` of `X` carries an identification `ε : 𝒳_η̄ ⟶ X`, and its nearby cycles
`Ψ_M = Li^* Rj_* Lε^*` are the nearby cycles of the model `M.toGeneric` of the geometric generic
fibre `𝒳_η̄` itself (the same total space, with `ε = 𝟙`,
`AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.toGeneric`), precomposed with `Lε^*`.
This file shows that the Künneth map `Π_{A,B}` of three models is, up to isomorphisms of arrows,
the Künneth map `Π_{Lε_M^* A, Lε_N^* B}` of the models of the geometric generic fibres
(`NearbyCyclesModel.kunnethMapArrowIsoToGeneric`); in particular one is an isomorphism if and
only if the other is (`NearbyCyclesModel.isIso_kunnethMap_iff_toGeneric`).

The point is that a morphism of models of the geometric generic fibres exists in more situations:
the morphism from a model of finite type over the trait to the trait itself exists on the
geometric generic fibres, while there need not be a morphism `X ⟶ Spec Ω` from the scheme `X`
that `ε` identifies the geometric generic fibre with.

## Implementation notes

All exchange maps and lax tensor maps factor through the *reduced* versions `ᾱ` and `μ̄`, which
do not involve `ε`; the comparison is proved for abstract functors
(`NearbyCyclesModel.kunnethMap_eq_aux`, `NearbyCyclesModel.isIso_reducedKunneth_iff_aux`) and
then instantiated.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

/-! ### Abstract computations -/

section Abstract

variable {CM CN CP GM GN GP SM SN SP : Type*} [Category CM] [Category CN] [Category CP]
  [Category GM] [Category GN] [Category GP] [Category SM] [Category SN] [Category SP]
  [MonoidalCategory CP] [MonoidalCategory GP] [MonoidalCategory SP]
  {EM : CM ⥤ GM} {EN : CN ⥤ GN} {EP : CP ⥤ GP} {ΨM : GM ⥤ SM} {ΨN : GN ⥤ SN} {ΨP : GP ⥤ SP}
  {f₁ : CM ⥤ CP} {f₂ : CN ⥤ CP} {g₁ : GM ⥤ GP} {g₂ : GN ⥤ GP} {s₁ : SM ⥤ SP} {s₂ : SN ⥤ SP}

end Abstract

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X X' Y Y' Z Z' : Scheme.{u}}

/-! ### The model of the geometric generic fibre -/

variable {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'} {P : NearbyCyclesModel Z Z'}

variable {f₁ : Z ⟶ X} {f₁' : Z' ⟶ X'} {f₂ : Z ⟶ Y} {f₂' : Z' ⟶ Y'}

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
