/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q25
-/
module

public import Sheaf.Paper.GeneralNearbySliceTest

/-!
# The category of geometric points and strict-local specializations

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose XIV, Definition 2.1.1,
printed pp. 209--210 (blueprint: def-per-geometric-specialization-category).

The category is induced from schemes over the base, using the existing strict-local
construction. Its arrows are converted to the published `SliceSpecialization` data;
no new construction of strict localizations or of specialization maps is made.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- Bundling the field and map of a geometric point, with no restriction on transcendence.
Source: ILO XIV, Definition 2.1.1
(blueprint: def-per-geometric-specialization-category). -/
structure StrictGeometricPointData (S : Scheme.{u}) where
  field : Type u
  [fieldStructure : Field field]
  [algebraicallyClosed : IsAlgClosed field]
  point : Spec (.of field) ⟶ S

attribute [instance] StrictGeometricPointData.fieldStructure
  StrictGeometricPointData.algebraicallyClosed

/-- The existing strict localization, regarded as a scheme over its base.
Source: ILO XIV, Definition 2.1.1
(blueprint: def-per-geometric-specialization-category). -/
def StrictGeometricPointData.localization {S : Scheme.{u}} (p : StrictGeometricPointData S) :
    Over S :=
  Over.mk (Scheme.strictHenselizationStructuralMap p.point)

/-- Geometric points with morphisms the maps of their strict localizations over the base.
Isomorphisms here concern strict localizations, rather than algebraically closed overfields.
Source: ILO XIV, Definition 2.1.1
(blueprint: def-per-geometric-specialization-category). -/
abbrev StrictGeometricPoint (S : Scheme.{u}) :=
  InducedCategory (Over S) (@StrictGeometricPointData.localization S)

namespace StrictGeometricPoint

/-- The underlying Zariski point. Source: ILO XIV, Definition 2.1.1
(blueprint: def-per-geometric-specialization-category). -/
def underlying {S : Scheme.{u}} (p : StrictGeometricPoint S) : S :=
  p.point (IsLocalRing.closedPoint p.field)

/-- The distinguished point in the existing strict localization, obtained by evaluation.
Source: ILO XIV, Definition 2.1.1; Stacks, Tag 04HX
(blueprint: def-per-geometric-specialization-category). -/
def closed {S : Scheme.{u}} (p : StrictGeometricPoint S) : p.localization.left :=
  (Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationPointEvaluation p.point)))
    (IsLocalRing.closedPoint p.field)

/-- An arrow as the already published geometric-specialization datum.
Source: ILO XIV, Definition 2.1.1
(blueprint: def-per-geometric-specialization-category). -/
def specializationSlice {S : Scheme.{u}} {p q : StrictGeometricPoint S} (a : p ⟶ q) :
    OrientedNearbyCycles.SliceSpecialization S where
  A := q.field
  B := p.field
  a := q.point
  b := p.point
  c := a.hom.left
  over := Over.w a.hom

/-- Codimension is the dimension of the reduced closure of the source in the target's
strict localization. Reduction does not change the underlying topological space.
Source: ILO XIV, Definitions 2.1.1--2.1.2
(blueprint: def-per-geometric-specialization-category). -/
def codimension {S : Scheme.{u}} {p q : StrictGeometricPoint S} (a : p ⟶ q) :
    WithBot ℕ∞ :=
  topologicalKrullDim
    (closure ({(specializationSlice a).c p.closed} : Set q.localization.left))

/-- An immediate geometric specialization has codimension one.
Source: ILO XIV, Definition 2.1.1
(blueprint: def-per-geometric-specialization-category). -/
def IsImmediate {S : Scheme.{u}} {p q : StrictGeometricPoint S} (a : p ⟶ q) : Prop :=
  codimension a = 1

end StrictGeometricPoint
end AlgebraicGeometry
