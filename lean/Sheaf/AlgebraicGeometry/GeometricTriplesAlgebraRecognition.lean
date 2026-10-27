/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V7
-/
module

public import Sheaf.AlgebraicGeometry.GeometricTriplesComparisonMaps
public import Sheaf.RingTheory.IndEtaleUniverseTransport
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.Mathlib.RingTheory.Henselian

/-! # Recognition of the algebraic residue-triple colimit

Source: Stacks Project, Algebra, Tags 04GW, 04GP, 08HR and 08HT.
-/

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Algebraic recognition, before comparison with geometric neighbourhoods.
Source: Stacks Project, Algebra, Tags 04GW and 04GP, and Tags 08HR and 08HT.
(blueprint: lem-wf-geometric-triples-algebra-recognition).

Proof: The field-valued base point is the closed point. Its residue embedding
identifies its residue field with the chosen residue closure. Transport
strictHenselization_triples across this identification and then across uniqueness
of the specified colimit c. Thus c.pt is henselian local, its base map rho is
ind-etale and local, and qA is surjective with maximal-ideal kernel. Equip c.pt
with the A-algebra structure from rho. Present the ind-etale map to C by its
filtered etale diagram. For unequal universes use the canonical ULift ring
isomorphisms in IndEtaleAcrossUniverses to put the rings in a common universe;
transport the diagrams, local structure, and residue maps along these isomorphisms.
Apply map_into_henselian_colimit from C to c.pt with identity residue map on K,
and in the reverse direction from the triple colimit to C. Their composites have
the same base and residue maps as the identities; uniqueness in that theorem
makes them identities. The resulting ring equivalence preserves the base map.
The same uniqueness for maps from c.pt to C gives the final clause, among all
ring homomorphisms preserving the specified base and residue maps. The residue
identity forces locality, so no separate locality assumption on these maps is needed.
-/
theorem geometric_triples_algebra_recognition
    (A : CommRingCat.{u}) [IsLocalRing A]
    (K : Type u) [Field K]
    [Algebra (IsLocalRing.ResidueField A) K] [IsSepClosure (IsLocalRing.ResidueField A) K]
    (C : Type v) [CommRing C] [HenselianLocalRing C] [Algebra A C]
    [IsLocalHom (algebraMap A C)]
    (hC : RingHom.IndEtaleAcrossUniverses (algebraMap A C))
    (q : C →+* K) (hq : Function.Surjective q)
    (hker : RingHom.ker q = IsLocalRing.maximalIdeal C)
    (hqa : q.comp (algebraMap A C) = (geometricTriplesBaseResidue A K).hom)
    (c : Cocone (etaleResidueTriplesRingDiagram A (geometricTriplesResiduePoint A K).1 K
      (geometricTriplesResiduePoint A K).2)) (hc : IsColimit c)
    (qA : c.pt ⟶ .of K)
    (hqA : ∀ t, c.ι.app t ≫ qA = geometricTriplesTripleResidue t)
    (ρ : A ⟶ c.pt) (hρ : ∀ t, t.α ≫ c.ι.app t = ρ) :
    ∃ e : C ≃+* c.pt,
      e.toRingHom.comp (algebraMap A C) = ρ.hom ∧
      q.comp e.symm.toRingHom = qA.hom ∧
      ∀ f : c.pt →+* C,
        f.comp ρ.hom = algebraMap A C → q.comp f = qA.hom →
        f = e.symm.toRingHom := by sorry

end AlgebraicGeometry.Scheme
