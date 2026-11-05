/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.GaloisActionUnitTransportInputs
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.UnitRetraction

/-!
# The derived unit transport on acyclic complexes

Let `g : Y ⟶ X` be a morphism of schemes and `s : Y' ⟶ Y` with `s ≫ g = p₁`. For a bounded below
complex `K` of module objects over `Λ_X` such that every `g^*(Kⁿ)` is `g_*`-acyclic, the isomorphism
`Adjunction.derivedUnitIso : g_* g^* K ≅ Rg_* Lg^* K` identifies `Rg_* Lg^* K` with the complex
`g_* g^* K`. This file shows that under these identifications (for `g` and `p₁`), the derived unit
transport `Rg_* Lg^* ⟶ Rp₁_* Lp₁^*` along `s` (`ProEtale.CondensedRing.derivedUnitTransport`) is
the underived unit transport `ProEtale.CondensedRing.unitTransport` applied levelwise. No
finiteness or exactness of the pushforwards is needed.

## Main results

- `ProEtale.CondensedRing.derivedUnitIso_hom_comp_derivedUnitTransport`: the comparison for an
  arbitrary factorization `s ≫ g = p₁`.
- `ProEtale.CondensedRing.derivedUnitIso_hom_comp_derivedUnitTransport_self`: the case
  `s ≫ g = g`, e.g. for an automorphism `s` of `Y` over `X`: the derived action of `s` on
  `Rg_* Lg^* K` is, through `Adjunction.derivedUnitIso`, the levelwise action on `g_* g^* K`.

## Implementation notes

The proof applies the abstract comparison `CategoryTheory.unitTransport_derived_fac` on the image
of `K` in the homotopy category, together with
`ProEtale.CondensedRing.unitTransportHomotopyCompatible`, and the naturality of the derived unit
transport along the isomorphism `Qh(K) ≅ Q(K)`.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

open scoped CategoryTheory.Obj CategoryTheory.Functor

universe u

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

end AlgebraicGeometry.ProEtale.CondensedRing
