/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GeometricTriplesComparisonMaps
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed

/-! # The geometric and residue-triple diagrams

Source: Stacks Project, Tag 04HX.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- The diagram comparison, without recognition of an arbitrary ind-etale algebra.
Source: Stacks Project, Tag 04HX, proof of lemma-describe-etale-local-ring;
Categories, Tags 0BUC and 04E7.
(blueprint: lem-wf-geometric-triples-diagram-comparison).

Proof: Apply etale_local_ring_triples to the identity chart of Spec A. The base
prime is the maximal ideal, since its field-valued map factors through the residue
field. The supplied relative-closure identification transports its relative closure
to K. Finite separability of the residue field of an etale point then gives the
first assertion. Compose its equivalence of affine pointed neighbourhoods and
residue triples with strictHenselizationAffineInclusion and with r. The equations
on chart maps and lifted points become GeometricTriplesRepresents. Each triple
is isomorphic to a representative, so these equations determine maps out of its
colimit. Colimit uniqueness gives g and its inverse, with the prescribed
coprojections. The identity neighbourhood gives the base map b and its chart
and triple formulas. Descend the evaluations to the geometric colimit; on each
representative the point equation says that this map is qA composed with g inverse
and K to Omega. This proves the evaluation formula. Every construction is through
the given equivalence r, so it works for each small representative category.
-/
theorem geometric_triples_diagram_comparison
    (A : CommRingCat.{u}) [IsLocalRing A]
    (K Ω : Type u) [Field K] [Field Ω]
    [Algebra (IsLocalRing.ResidueField A) K] [IsSepClosure (IsLocalRing.ResidueField A) K]
    [Algebra K Ω] [IsAlgClosed Ω]
    [Algebra (IsLocalRing.ResidueField A) Ω]
    [IsScalarTower (IsLocalRing.ResidueField A) K Ω]
    (hsep : ∀ z : Ω, z ∈ separableClosure (IsLocalRing.ResidueField A) Ω ↔
      z ∈ Set.range (algebraMap K Ω)) :
    (∀ (n : strictHenselizationNeighbourhoods (geometricTriplesPoint A K Ω))
      (z : ((AffineEtale.Spec (Spec A)).obj n.1).left.residueField
        (SpecToEquivOfField Ω _ n.2.left).1),
      (SpecToEquivOfField Ω _ n.2.left).2 z ∈ Set.range (algebraMap K Ω)) ∧
    ∀ (J : Type u) [SmallCategory J]
      (r : J ⥤ strictHenselizationNeighbourhoods (geometricTriplesPoint A K Ω))
      [r.IsEquivalence]
      (c : Cocone (etaleResidueTriplesRingDiagram A (geometricTriplesResiduePoint A K).1 K
        (geometricTriplesResiduePoint A K).2)) (hc : IsColimit c)
      (qA : c.pt ⟶ .of K)
      (hqA : ∀ t, c.ι.app t ≫ qA = geometricTriplesTripleResidue t),
      (∀ j : J, ∃ (t : EtaleResidueTriple A (geometricTriplesResiduePoint A K).1 K
        (geometricTriplesResiduePoint A K).2)
        (hB : t.B = (strictHenselizationCoordinateRings
          (geometricTriplesPoint A K Ω)).obj (op (r.obj j))),
        GeometricTriplesRepresents (r.obj j) t hB) ∧
      ∃ b : A ⟶ colimit (r.op ⋙ strictHenselizationCoordinateRings
          (geometricTriplesPoint A K Ω)),
        (∀ j : J, geometricTriplesChart (r.obj j) ≫
          colimit.ι (r.op ⋙ strictHenselizationCoordinateRings
            (geometricTriplesPoint A K Ω)) (op j) = b) ∧
        ∃ g : c.pt ⟶ colimit (r.op ⋙ strictHenselizationCoordinateRings
            (geometricTriplesPoint A K Ω)),
          GeometricTriplesCoprojections r c g ∧ ∃ (_ : IsIso g),
          (∀ t, t.α ≫ c.ι.app t ≫ g = b) ∧
          (∀ j : J, (inv g ≫ qA ≫ CommRingCat.ofHom (algebraMap K Ω)).hom.comp
            (colimit.ι (r.op ⋙ strictHenselizationCoordinateRings
              (geometricTriplesPoint A K Ω)) (op j)).hom =
                (geometricTriplesEvaluation (r.obj j)).hom) ∧
          ∀ g' : c.pt ⟶ colimit (r.op ⋙ strictHenselizationCoordinateRings
              (geometricTriplesPoint A K Ω)),
            GeometricTriplesCoprojections r c g' → g' = g := by sorry

end AlgebraicGeometry.Scheme
