/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs

/-! # Affine steps in the radicial generic field construction

Source: Stacks Project, Tags 0559 and 030R. -/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Topology
namespace AlgebraicGeometry

/-- A reduced affine family with geometrically irreducible generic fibre has a finitely
generated generic function field.
Source: Stacks Project, Tag 0559, second proof, the generic function field construction.
Proof: identify S and Z with Spec A and Spec B. At the generic point the base residue field
is Frac A, and the fibre ring is B localized at the nonzero elements of A. Localization
preserves reducedness. Geometric irreducibility implies irreducibility and nonemptiness,
so this reduced ring is a nonzero domain. Take its actual fraction field L. Finite
presentation gives a finite set of algebra generators of the fibre ring; they also generate
L as a field. The injection of the fibre ring into its fraction field gives a
scheme-theoretically dominant spectrum map j. Its composite to the base spectrum is the
spectrum of the induced field algebra map by contravariant functoriality.
The empty fibre is excluded by geometric irreducibility; a zero-dimensional fibre gives
its ordinary finite function field. No geometrically reduced hypothesis is used.
(blueprint: lem-sbc-generic-fibre-dominant-field) -/
theorem exists_generic_fibre_dominant_field
    {Z S : Scheme.{u}} [IsAffine Z] [IsReduced Z] [IsAffine S] [IsIntegral S]
    (g : Z ⟶ S) [Flat g] [LocallyOfFinitePresentation g]
    (η : S) (hη : IsGenericPoint η Set.univ)
    (hgeom : GeometricallyIrreducible (g.fiberToSpecResidueField η)) :
    ∃ (L : Type u) (hL : Field L) (aL : Algebra (S.residueField η) L),
      letI := hL
      letI := aL
      (⊤ : IntermediateField (S.residueField η) L).FG ∧
      ∃ j : Spec (.of L) ⟶ g.fiber η,
        IsSchemeTheoreticallyDominant j ∧
        j ≫ g.fiberToSpecResidueField η =
          Spec.map (CommRingCat.ofHom (algebraMap (S.residueField η) L)) := by sorry

end AlgebraicGeometry
