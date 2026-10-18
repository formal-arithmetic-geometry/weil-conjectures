/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N5
-/
module

public import Mathlib.CategoryTheory.Preadditive.Comma
public import Mathlib.RepresentationTheory.Invariants
public import WeilConjectures.RepresentationTheory.DiscreteContinuousRep

/-!
# Specialization triples of discrete continuous representations

Source: ILO, Travaux de Gabber, Expose XVII, section 1.2.2, printed p. 260
(blueprint: def-per-trait-specialization-triples).
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace AlgebraicGeometry.Etale

variable (Λ : Type v) [CommRing Λ] (H : Type u) [Group H]
  [TopologicalSpace H] [IsTopologicalGroup H]

/-- The existing full-subcategory inclusion of discrete continuous representations.
Source: ILO XVII 1.2.2 (blueprint: def-per-trait-specialization-triples). -/
abbrev traitDiscreteRepInclusion :
    Rep.DiscreteContinuousRep.{v, u, w} Λ H ⥤ Rep.{w} Λ H :=
  ObjectProperty.ι _

/-- Triples `(W,V,a)` with `W` trivial, `V` discrete continuous, and `a` equivariant.
Morphisms are exactly the commuting pairs, with an equivariant generic component.
This specializes Mathlib's comma category, without a second definition of representations.
Source: ILO XVII 1.2.2 (blueprint: def-per-trait-specialization-triples). -/
abbrev TraitSpecialization :=
  Comma (Rep.trivialFunctor Λ H) (traitDiscreteRepInclusion.{u, v, w} Λ H)

/-- The closed module of a specialization triple.
Source: ILO XVII 1.2.2 (blueprint: def-per-trait-specialization-triples). -/
abbrev traitSpecializationClosed : TraitSpecialization.{u, v, w} Λ H ⥤ ModuleCat.{w} Λ :=
  Comma.fst _ _

/-- The generic discrete continuous representation of a specialization triple.
Source: ILO XVII 1.2.2 (blueprint: def-per-trait-specialization-triples). -/
abbrev traitSpecializationGeneric :
    TraitSpecialization.{u, v, w} Λ H ⥤ Rep.DiscreteContinuousRep.{v, u, w} Λ H :=
  Comma.snd _ _

/-- The generic underlying module of a specialization triple.
Source: ILO XVII 1.2.2 (blueprint: def-per-trait-specialization-triples). -/
abbrev traitSpecializationModule : TraitSpecialization.{u, v, w} Λ H ⥤ ModuleCat.{w} Λ :=
  traitSpecializationGeneric Λ H ⋙ traitDiscreteRepInclusion Λ H ⋙
    forget₂ (Rep.{w} Λ H) (ModuleCat.{w} Λ)

/-- The generic invariant module of a specialization triple.
Source: ILO XVII 1.2.2 (blueprint: def-per-trait-specialization-triples). -/
noncomputable abbrev traitSpecializationInvariants :
    TraitSpecialization.{u, v, w} Λ H ⥤ ModuleCat.{w} Λ :=
  traitSpecializationGeneric Λ H ⋙ traitDiscreteRepInclusion Λ H ⋙ Rep.invariantsFunctor Λ H

/-- The actual arrow `a`, with codomain restricted to the invariants by the standard adjunction.
Source: ILO XVII 1.2.2 (blueprint: def-per-trait-specialization-triples). -/
noncomputable def traitSpecializationInvariantArrow (X : TraitSpecialization.{u, v, w} Λ H) :
    X.left ⟶ (traitSpecializationInvariants Λ H).obj X :=
  (Rep.invariantsAdjunction Λ H).homEquiv _ _ X.hom

/-- Trivial representations preserve addition definitionally, so their comma category
has Mathlib's preadditive structure.
Source: ILO XVII 1.2.2 (blueprint: def-per-trait-specialization-triples). -/
instance traitTrivialFunctorAdditive :
    (Rep.trivialFunctor Λ H : ModuleCat.{w} Λ ⥤ Rep.{w} Λ H).Additive where
  map_add := rfl

end AlgebraicGeometry.Etale
