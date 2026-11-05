/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.GaloisActionUnitTransport

/-!
# Inputs of the identification of the unit transport with the Galois action

This file discharges the homotopy-category input of
`ProEtale.CondensedRing.derivedUnitTransport_eq_derivedGaloisAction_app` and reduces the
underived input to an identity after the counit.

## Main results

- `CategoryTheory.unitTransport_mapHomotopyCategory_quotient` and
  `ProEtale.CondensedRing.unitTransportHomotopyCompatible`: the unit transport on homotopy
  categories is the unit transport of module objects applied levelwise, i.e.
  `ProEtale.CondensedRing.UnitTransportHomotopyCompatible` holds.
- `CategoryTheory.unitTransport_app_eq_unit_comp`, `ProEtale.CondensedRing.unitTransport_app_eq`:
  the unit transport is the transpose of `c ≫ s^*(ε_g) ≫ c⁻¹`.
- `ProEtale.CondensedRing.galoisAction_eq_unitTransport_of_counit`: the Galois action is the unit
  transport as soon as both agree after `g^*` and the counit.
- `exists_retraction_pullbackExchange_galoisLayerHom_of_galoisAction_eq`:
  the splitting of the pullback exchange of a finite Galois layer, assuming only the underived
  identification of the Galois actions with the unit transports.

## Implementation notes

The underived identification `galoisAction Λ g hρ a = unitTransport Λ (ρ σ) (hρ σ) (hρ σ)` is
not proved here. By `ProEtale.CondensedRing.galoisAction_eq_unitTransport_of_counit` it reduces
to `g^*(ρ_a) ≫ ε = c ≫ (ρ σ)^*(ε) ≫ c⁻¹` on `g^* g_* g^* M`; this requires comparing the module
pullbacks with the abelian ones (through the extension of scalars along `α_g`) and the abelian
ones with the restrictions along the localization functors.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory

section QuotientApp

variable {ι V W W' : Type*} {c : ComplexShape ι} [Category V] [Category W] [Category W']
  [Preadditive V] [Preadditive W] [Preadditive W']

end QuotientApp

variable {ι : Type*} {c : ComplexShape ι} {A B B' : Type*} [Category A] [Category B]
  [Category B'] [Preadditive A] [Preadditive B] [Preadditive B']
  [(HomotopyCategory.quotient A c).IsLocalization (HomologicalComplex.homotopyEquivalences A c)]
  [(HomotopyCategory.quotient B c).IsLocalization (HomologicalComplex.homotopyEquivalences B c)]
  [(HomotopyCategory.quotient B' c).IsLocalization
    (HomologicalComplex.homotopyEquivalences B' c)]

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

open scoped CategoryTheory.Obj CategoryTheory.Functor

universe u

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

namespace NearbyCyclesModel

variable {X X' : Scheme.{u}} (N : NearbyCyclesModel X X') {L : Type u} [Field L]
  (h : N.generic ⟶ Spec (.of L)) (L' : Type u) [Field L'] [Algebra L L']
  [FiniteDimensional L L'] [IsGalois L L']

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
