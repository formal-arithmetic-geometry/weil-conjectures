/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q61
-/
module

public import Sheaf.AlgebraicGeometry.BirationalValuationNeighbourhoodData
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.Topology.Constructions
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# Fibre-generic valuation sets of modifications

Source: Temkin, Stable modification of relative curves, §4.2, definitions preceding
Lemma 4.2.1, pp. 26--27 (blueprint: def-trf-modification-fibre-valuation-sets).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.RiemannZariski

/-- The disjoint union of the existing centred-valuation spaces over component generic points.
The residue field at such a point of a reduced scheme is its component function field.
Source: Temkin §4.2, p. 26 (blueprint: def-trf-modification-fibre-valuation-sets). -/
abbrev ComponentValuationSpace (C : Scheme.{u}) :=
  (g : genericPoints C) × ValuationPoint C (C.residueField g.1) (C.fromSpecResidueField g.1)

/-- The coproduct of the existing centre-projection topologies, with no identifications
between distinct components. Source: Temkin §4.2 and §3.2
(blueprint: def-trf-modification-fibre-valuation-sets). -/
@[instance_reducible] def componentValuationTopology (C : Scheme.{u}) :
    TopologicalSpace (ComponentValuationSpace C) :=
  @instTopologicalSpaceSigma (genericPoints C)
    (fun g ↦ ValuationPoint C (C.residueField g.1) (C.fromSpecResidueField g.1))
    (fun g ↦ valuationTopology C (C.residueField g.1) (C.fromSpecResidueField g.1))

/-- Gamma consists of valuations whose proper lift has a fibre-component generic centre.
The existential lift is characterized by its actual map over C; proper separatedness makes
it unique for a modification. Source: Temkin §4.2, p. 26
(blueprint: def-trf-modification-fibre-valuation-sets). -/
def modificationGamma {T C Y : Scheme.{u}} (c : C ⟶ T) (q : Y ⟶ C) :
    Set (ComponentValuationSpace C) :=
  {ν | ∃ l : Spec (.of ν.2.V) ⟶ Y, l ≫ q = ν.2.centre ∧
    ∃ (s : T) (z : (q ≫ c).fiber s), z ∈ genericPoints ((q ≫ c).fiber s) ∧
      (q ≫ c).fiberι s z = l (IsLocalRing.closedPoint ν.2.V)}

/-- Gamma-zero imposes closedness of the original centre on C, not on Y or its fibre.
Source: Temkin §4.2, p. 26 (blueprint: def-trf-modification-fibre-valuation-sets). -/
def modificationGammaZero {T C Y : Scheme.{u}} (c : C ⟶ T) (q : Y ⟶ C) :
    Set (ComponentValuationSpace C) :=
  {ν | ν ∈ modificationGamma c q ∧
    IsClosed ({ν.2.centre (IsLocalRing.closedPoint ν.2.V)} : Set C)}

/-- The reduced closed complement of the largest isomorphism open, the existing
`Scheme.Hom.maximalIsomorphismOpen` (blueprint: def-nagata-maximal-isomorphism-open).
The ideal is the actual vanishing ideal, so the construction has no existence choices.
Source: Temkin §4.2, definition of modification locus
(blueprint: def-trf-modification-fibre-valuation-sets). -/
def modificationLocusIdeal {C Y : Scheme.{u}} (q : Y ⟶ C) : C.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal
    ⟨((q.maximalIsomorphismOpen : C.Opens) : Set C)ᶜ,
      q.maximalIsomorphismOpen.isOpen.isClosed_compl⟩

end AlgebraicGeometry.RiemannZariski
