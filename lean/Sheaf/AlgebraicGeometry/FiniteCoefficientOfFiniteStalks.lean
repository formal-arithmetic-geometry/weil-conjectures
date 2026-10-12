/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Finite coefficients of a finite-stalk module sheaf

Source: the normalization exact-sequence blueprint, unit `sk-thm-p1`, finite-coefficient
reduction in lem-weil-pbc-finite-pushforward-finite-stalk-module.
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- The canonical sectionwise annihilator of a constructible module sheaf with finite
stalks has finite quotient.

Source: normalization exact-sequence blueprint, finite-coefficient reduction in
`lem-weil-pbc-finite-pushforward-finite-stalk-module`, step 1.
(blueprint: lem-weil-pbc-finite-coefficient-of-finite-stalks)

Proof: Choose the finite module-constructible stratification. On each stratum discard
empty members of a trivializing etale cover. Identify each remaining constant value
with a geometric stalk, using a separably closed extension of the residue field of a
point of the member and inverse-image/stalk compatibility; it is finite by hypothesis.
Noetherian strata are quasi-compact, so choose finitely many cover members. Intersect
annihilators of these finitely many finite modules. This intersection equals the ideal
of scalars killing every section, the intersection of all section-module annihilators:
geometric stalks detect zero scalar endomorphisms, and constant values are stalks.
The quotient by this canonical ideal embeds into the finite
product of their endomorphism rings, so is finite. The ideal kills all geometric stalks
on all strata and hence the sheaf, as geometric stalks detect equality. In particular
it kills every section, on arbitrary etale objects, not just quasi-compact ones.
For the empty scheme use the unit ideal and empty
stratification. For the zero sheaf the quotient can likewise be the zero ring. -/
theorem finite_quotient_section_annihilator_of_finite_stalks
    (Λ : Type (u + 1)) [CommRing Λ]
    {X : Scheme.{u}} [IsNoetherian X]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : IsConstructibleSheaf F)
    (hfin : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
      Finite ((((pointSmallEtale s).ulift.{u + 1}).sheafFiber
        (A := ModuleCat.{u + 1} Λ)).obj F)) :
    Finite (Λ ⧸ ⨅ U : X.Etaleᵒᵖ, Module.annihilator Λ (F.obj.obj U)) := by
  sorry

end AlgebraicGeometry.Scheme
