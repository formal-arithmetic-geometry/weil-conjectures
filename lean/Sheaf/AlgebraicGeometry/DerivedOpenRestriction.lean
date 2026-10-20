/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.BaseChange.Derived
import WeilConjectures.SixFunctors.BaseChange.EtaleDerived

/-!
# Derived direct image restricted to an open

Source: blueprint, sec-smooth-purity, sk-def-sf-operations,
lem-weil-pbc-derived-open-restriction (blueprint: lem-weil-pbc-derived-open-restriction);
Stacks Project, Tags 03S2, 03F3, 05TI and 05TH.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Restriction of derived direct image to an open subscheme is the derived direct image
of the restriction, naturally in the bounded-below complex of finite-ring module sheaves.
The transformation is the canonical derived exchange map, not an arbitrary isomorphism.
Source: blueprint, sec-smooth-purity, sk-def-sf-operations,
lem-weil-pbc-derived-open-restriction (blueprint: lem-weil-pbc-derived-open-restriction).

Proof:
1. For an etale `W → U`, inverse image along an open is restriction
   (`lem-weil-pbc-etale-inverse-image-restriction`). By `def-weil-pbc-direct-image`, both
   underived composites evaluate to `F(T ×_S W) = F(V ×_U W)`, naturally in `W` and `F`.
2. Identify the localized etale site with the etale site of the open
   (`lem-weil-pbc-etale-site-localization-open`). Restriction and its left adjoint,
   extension by zero, are exact (`lem-pur-site-restriction-module-adjunction-exact`).
   The adjunction identifies Hom into the restriction of an injective with Hom from
   extension by zero into that injective. Exactness therefore shows that restriction
   preserves injectives.
3. Choose a bounded-below injective resolution of the complex
   (`prop-weil-pbc-kinjective-resolutions-exist`). Exact restriction preserves this
   resolution and its injective terms. The sectionwise comparison in step 1, in every
   degree, computes the derived exchange map and is an isomorphism. The sectionwise
   construction is natural in the complex and compatible with successive restrictions
   and compositions. -/
theorem isIso_derivedBaseChangeMapPlus_of_openImmersion
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {T S U V : Scheme.{u}} (f : T ⟶ S) (a : U ⟶ S)
    (b : V ⟶ T) (fU : V ⟶ U) [IsOpenImmersion a]
    (sq : ChosenCartesianSquare b fU f a) :
    IsIso (derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq) := by
  exact isIso_derivedBaseChangeMapPlus_of_etale Λ
    (IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd)

end AlgebraicGeometry.Etale
