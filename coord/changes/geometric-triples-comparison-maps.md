# Geometric comparison auxiliary definitions

## Reason

The diagram comparison and algebraic recognition need the existing canonical maps
without importing the theorem they will prove. Move the eight auxiliary definitions
into Sheaf.AlgebraicGeometry.GeometricTriplesComparisonMaps and publicly reexport
that module from the original item. This avoids an import cycle. Names, universes,
signatures, and bodies of all eight definitions are unchanged. Only their docstring
blueprint tags now name the definition node. The original theorem signature and its
six original public imports are preserved verbatim. No target definition changes.

## Old

In lean/Sheaf/AlgebraicGeometry/GeometricTriplesColimitComparison.lean:

```lean
/-- The prescribed map from the local ring to the chosen separable residue closure.
Source: Stacks Project, Tag 04HX
(blueprint: lem-wf-geometric-triples-colimit-comparison). -/
noncomputable def geometricTriplesBaseResidue (A : CommRingCat.{u}) [IsLocalRing A]
    (K : Type u) [Field K] [Algebra (IsLocalRing.ResidueField A) K] : A ⟶ .of K :=
  CommRingCat.ofHom ((algebraMap (IsLocalRing.ResidueField A) K).comp (IsLocalRing.residue A))

/-- The closed prime and its residue embedding, read from the field-valued point.
Source: Stacks Project, Tag 04HX
(blueprint: lem-wf-geometric-triples-colimit-comparison). -/
noncomputable def geometricTriplesResiduePoint (A : CommRingCat.{u}) [IsLocalRing A]
    (K : Type u) [Field K] [Algebra (IsLocalRing.ResidueField A) K] :=
  SpecToEquivOfField K (Spec A) (Spec.map (geometricTriplesBaseResidue A K))

/-- The given geometric point, induced by the composite through the residue closure.
Source: Stacks Project, Tag 04HX
(blueprint: lem-wf-geometric-triples-colimit-comparison). -/
noncomputable def geometricTriplesPoint (A : CommRingCat.{u}) [IsLocalRing A]
    (K Ω : Type u) [Field K] [Field Ω]
    [Algebra (IsLocalRing.ResidueField A) K] [Algebra K Ω] : Spec (.of Ω) ⟶ Spec A :=
  Spec.map (geometricTriplesBaseResidue A K ≫ CommRingCat.ofHom (algebraMap K Ω))

/-- The map `A → Γ(V)` of a ring-written pointed affine neighbourhood.
Source: Stacks Project, Tag 04HX
(blueprint: lem-wf-geometric-triples-colimit-comparison). -/
noncomputable def geometricTriplesChart {A : CommRingCat.{u}} {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] {x : Spec (.of Ω) ⟶ Spec A}
    (n : strictHenselizationNeighbourhoods x) : A ⟶ (strictHenselizationCoordinateRings x).obj
      (op n) :=
  (ΓSpecIso A).inv ≫ ((AffineEtale.Spec (Spec A)).obj n.1).hom.appTop

/-- The ring map on global sections induced by the lifted geometric point.
Source: Stacks Project, Tag 04HX
(blueprint: lem-wf-geometric-triples-colimit-comparison). -/
noncomputable def geometricTriplesEvaluation {A : CommRingCat.{u}} {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] {x : Spec (.of Ω) ⟶ Spec A}
    (n : strictHenselizationNeighbourhoods x) :
    (strictHenselizationCoordinateRings x).obj (op n) ⟶ .of Ω :=
  n.2.left.appTop ≫ (ΓSpecIso (.of Ω)).hom

/-- The residue map of a triple. Source: Stacks Project, Tag 04HX
(blueprint: lem-wf-geometric-triples-colimit-comparison). -/
noncomputable def geometricTriplesTripleResidue {A : CommRingCat.{u}} {p : Spec A}
    {K : Type u} [Field K] {χ : (Spec A).residueField p ⟶ .of K}
    (t : EtaleResidueTriple A p K χ) : t.B ⟶ .of K :=
  (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ

/-- The exact coordinate-ring and point equations identifying the triple of `V`.
The equality of rings identifies its prime and residue embedding with those of the lift,
since a field-valued map uniquely determines its prime and residue embedding.
Source: Stacks Project, Tag 04HX
(blueprint: lem-wf-geometric-triples-colimit-comparison). -/
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
(blueprint: lem-wf-geometric-triples-colimit-comparison). -/
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

```

## New

The exact signatures and bodies in Old now occur in
lean/Sheaf/AlgebraicGeometry/GeometricTriplesComparisonMaps.lean, under the same
namespace and visibility. The original module publicly imports this new module.
The theorem geometric_triples_colimit_comparison stays in its original module,
with its exact original signature and a complete proof from the two lower lemmas.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.GeometricTriplesColimitComparison | V7 | Reexports the eight definitions and uses them with identical meanings. |
| Sheaf.AlgebraicGeometry.GeometricTriplesDiagramComparison | new in V7 delivery | Imports the shared maps to state the diagram comparison. |
| Sheaf.AlgebraicGeometry.GeometricTriplesAlgebraRecognition | new in V7 delivery | Imports the shared maps to state algebraic recognition. |

A source scan of all Lean files finds no current direct importer of the original
item. Therefore there is no existing downstream Lean file to adapt or compile.
Its DAG parents still need it: lem-wf-strict-henselization-finite-lifts,
lem-per-trait-test-strict-completion-input, and
lem-sfb-strict-birational-law-realization retain the same dependency and statement.
No existing module other than the assigned item is changed.

## Status

landed 20261026T092927-L-3480808 2026-10-26 (merge of deliver/V7/Sheaf.AlgebraicGeometry.GeometricTriplesColimitComparison)
