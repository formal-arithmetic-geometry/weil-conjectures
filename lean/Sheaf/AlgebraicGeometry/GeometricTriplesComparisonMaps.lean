/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictHenselization
public import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples

/-! # Maps for geometric neighbourhoods and residue triples

Source: Stacks Project, Tags 04HX, 08HR and 08HT
(blueprint: def-wf-geometric-triples-comparison-maps).

The auxiliary definitions only spell out the canonical maps in the comparison.
Quantification over small representative equivalences expresses independence of representatives.
-/

@[expose] public section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- The prescribed map from the local ring to the chosen separable residue closure.
Source: Stacks Project, Tag 04HX
(blueprint: def-wf-geometric-triples-comparison-maps). -/
noncomputable def geometricTriplesBaseResidue (A : CommRingCat.{u}) [IsLocalRing A]
    (K : Type u) [Field K] [Algebra (IsLocalRing.ResidueField A) K] : A ⟶ .of K :=
  CommRingCat.ofHom ((algebraMap (IsLocalRing.ResidueField A) K).comp (IsLocalRing.residue A))

/-- The closed prime and its residue embedding, read from the field-valued point.
Source: Stacks Project, Tag 04HX
(blueprint: def-wf-geometric-triples-comparison-maps). -/
noncomputable def geometricTriplesResiduePoint (A : CommRingCat.{u}) [IsLocalRing A]
    (K : Type u) [Field K] [Algebra (IsLocalRing.ResidueField A) K] :=
  SpecToEquivOfField K (Spec A) (Spec.map (geometricTriplesBaseResidue A K))

/-- The given geometric point, induced by the composite through the residue closure.
Source: Stacks Project, Tag 04HX
(blueprint: def-wf-geometric-triples-comparison-maps). -/
noncomputable def geometricTriplesPoint (A : CommRingCat.{u}) [IsLocalRing A]
    (K Ω : Type u) [Field K] [Field Ω]
    [Algebra (IsLocalRing.ResidueField A) K] [Algebra K Ω] : Spec (.of Ω) ⟶ Spec A :=
  Spec.map (geometricTriplesBaseResidue A K ≫ CommRingCat.ofHom (algebraMap K Ω))

/-- The map `A → Γ(V)` of a ring-written pointed affine neighbourhood.
Source: Stacks Project, Tag 04HX
(blueprint: def-wf-geometric-triples-comparison-maps). -/
noncomputable def geometricTriplesChart {A : CommRingCat.{u}} {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] {x : Spec (.of Ω) ⟶ Spec A}
    (n : strictHenselizationNeighbourhoods x) : A ⟶ (strictHenselizationCoordinateRings x).obj
      (op n) :=
  (ΓSpecIso A).inv ≫ ((AffineEtale.Spec (Spec A)).obj n.1).hom.appTop

/-- The ring map on global sections induced by the lifted geometric point.
Source: Stacks Project, Tag 04HX
(blueprint: def-wf-geometric-triples-comparison-maps). -/
noncomputable def geometricTriplesEvaluation {A : CommRingCat.{u}} {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] {x : Spec (.of Ω) ⟶ Spec A}
    (n : strictHenselizationNeighbourhoods x) :
    (strictHenselizationCoordinateRings x).obj (op n) ⟶ .of Ω :=
  n.2.left.appTop ≫ (ΓSpecIso (.of Ω)).hom

/-- The residue map of a triple. Source: Stacks Project, Tag 04HX
(blueprint: def-wf-geometric-triples-comparison-maps). -/
noncomputable def geometricTriplesTripleResidue {A : CommRingCat.{u}} {p : Spec A}
    {K : Type u} [Field K] {χ : (Spec A).residueField p ⟶ .of K}
    (t : EtaleResidueTriple A p K χ) : t.B ⟶ .of K :=
  (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ

/-- The exact coordinate-ring and point equations identifying the triple of `V`.
The equality of rings identifies its prime and residue embedding with those of the lift,
since a field-valued map uniquely determines its prime and residue embedding.
Source: Stacks Project, Tag 04HX
(blueprint: def-wf-geometric-triples-comparison-maps). -/
def GeometricTriplesRepresents {A : CommRingCat.{u}} {p : Spec A}
    {K Ω : Type u} [Field K] [Field Ω] [IsAlgClosed Ω] [Algebra K Ω]
    {χ : (Spec A).residueField p ⟶ .of K} {x : Spec (.of Ω) ⟶ Spec A}
    (n : strictHenselizationNeighbourhoods x) (t : EtaleResidueTriple A p K χ)
    (hB : t.B = (strictHenselizationCoordinateRings x).obj (op n)) : Prop :=
  t.α ≫ eqToHom hB = geometricTriplesChart n ∧
    geometricTriplesTripleResidue t ≫ CommRingCat.ofHom (algebraMap K Ω) =
      eqToHom hB ≫ geometricTriplesEvaluation n

/-- Coprojection compatibility, imposed on ring maps before asserting invertibility.
Source: Stacks Project, Tag 04HX
(blueprint: def-wf-geometric-triples-comparison-maps). -/
def GeometricTriplesCoprojections {A : CommRingCat.{u}} {p : Spec A}
    {K Ω : Type u} [Field K] [Field Ω] [IsAlgClosed Ω] [Algebra K Ω]
    {χ : (Spec A).residueField p ⟶ .of K} {x : Spec (.of Ω) ⟶ Spec A}
    {J : Type u} [SmallCategory J] (r : J ⥤ strictHenselizationNeighbourhoods x)
    (c : Cocone (etaleResidueTriplesRingDiagram A p K χ))
    (g : c.pt ⟶ colimit (r.op ⋙ strictHenselizationCoordinateRings x)) : Prop :=
  ∀ (j : J) (t : EtaleResidueTriple A p K χ)
    (hB : t.B = (strictHenselizationCoordinateRings x).obj (op (r.obj j))),
    GeometricTriplesRepresents (r.obj j) t hB →
      c.ι.app t ≫ g = eqToHom hB ≫
        colimit.ι (r.op ⋙ strictHenselizationCoordinateRings x) (op j)

end AlgebraicGeometry.Scheme
