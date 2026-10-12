/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K2
-/
module

public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.RingTheory.ProEtale.IndEtale
import Sheaf.AlgebraicGeometry.EtaleLocalRingTriples
import Sheaf.RingTheory.StrictHenselizationTriples

/-! # The strict henselization is ind-etale over an affine chart

Source: Stacks Project, Tag 04HX, proof, and Tags 04GW and 04GP.
(blueprint: lem-weil-pbc-strict-henselization-affine-chart-ind-etale).
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- The ring of a strict henselization is ind-etale over any affine neighbourhood
of its geometric point, with the algebra structure specified by its structural map.
Source: Stacks Project, Tag 04HX, proof, using Tags 04GW and 04GP.
(blueprint: lem-weil-pbc-strict-henselization-affine-chart-ind-etale).

Proof: Factor the geometric point through the open immersion i. Restrict affine
pointed etale neighbourhoods to those whose structural map factors through i.
`etale_local_ring_triples` proves this restriction cofinal and identifies its
coordinate-ring diagram with the etale residue-triples diagram. The small model
in `strictHenselizationDiagram` is equivalent to the affine pointed-neighbourhood
category by `strictHenselizationAffineInclusion_isEquivalence`.
`strictHenselization_triples` gives filteredness; take a small representative
category of triples. Regard each triple as an R-algebra via its structural map.
Every transition is R-linear. The ring colimit therefore has its compatible
R-algebra structure and is also the colimit in CommAlgCat R: an R-linear cocone
induces a ring map from the ring colimit, and its agreement with R is checked on
one stage; uniqueness follows from ring-colimit uniqueness. Cofinality identifies
this colimit with strictHenselizationRing s. The equations defining
strictHenselizationStructuralMap identify the induced R-map with the map a after
transport through e. Indeed their spectra agree after composing with i, which is
mono, and full faithfulness of Spec then gives equality of ring maps. Transport
the algebra colimit along this R-algebra isomorphism to A. This is exactly the
filtered etale colimit presentation required by Algebra.IndEtale.

Edge cases: no local or reduced hypothesis on R is used. The chart containing
the specified geometric point is nonempty, and the pointed-neighbourhood category
has an object, so no empty filtered diagram is asserted. The identification e is
arbitrary; the equation ha fixes the transported R-algebra structure. -/
theorem strictHenselization_indEtale_of_affine_chart
    {S : Scheme.{u}} {Ω A : Type u} [Field Ω] [IsAlgClosed Ω] [CommRing A]
    (s : Spec (.of Ω) ⟶ S) (R : CommRingCat.{u})
    (i : Spec R ⟶ S) [IsOpenImmersion i]
    (hs : s (IsLocalRing.closedPoint Ω) ∈ Set.range i)
    (e : Spec (.of A) ≅ strictHenselizationScheme s)
    (a : R →+* A)
    (ha : Spec.map (CommRingCat.ofHom a) ≫ i =
      e.hom ≫ strictHenselizationStructuralMap s) :
    letI : Algebra R A := a.toAlgebra
    Algebra.IndEtale R A := by sorry

end AlgebraicGeometry.Scheme
