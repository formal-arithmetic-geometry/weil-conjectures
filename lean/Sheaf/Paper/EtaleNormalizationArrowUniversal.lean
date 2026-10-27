/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T3
-/
module

public import Sheaf.Paper.EtaleUniversalNormalization

/-! # Sourcewise universality for constant normalization arrows

Source: Stacks Project, Tags 06YY and 03ED.
(blueprint: lem-weil-pbc-etale-constant-arrow-universal-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- A universal constant coefficient arrow remains universal after restriction to an
etale source and transport through the canonical coefficient mate.

Source: Stacks Project, Tags 06YY and 03ED.
(blueprint: lem-weil-pbc-etale-constant-arrow-universal-transport).

The proof transports the initial structured arrow along the exact slice equivalence
and the coefficient mate. The mate is invertible by the inverse-image scalar
comparison, and the source and target constants are identified by the localization
comparison. Initial objects are preserved by these isomorphisms.
-/
theorem etaleNormalizationArrow_universal_of_constant
    (Y : Scheme.{t}) {R S : Type (t + 1)} [CommRing R] [CommRing S]
    (q : R →+* S)
    {E : DerivedCategory (ModuleCat.{t + 1} R)}
    {E' : DerivedCategory (ModuleCat.{t + 1} S)}
    (d : E ⟶ (normalizationModuleRestrict q).obj E')
    (h : Nonempty (StructuredArrow.IsUniversal (StructuredArrow.mk d)))
    (U : Y.Etale) :
    Nonempty (StructuredArrow.IsUniversal (StructuredArrow.mk
      (etaleIsomorphismNormalizationArrow Y q
        (normalizationConstantArrow Y.smallEtaleTopology q d) U))) := by
  sorry

end AlgebraicGeometry.Scheme
