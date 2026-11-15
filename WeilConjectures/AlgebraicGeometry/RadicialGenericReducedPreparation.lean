/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism

import WeilConjectures.AlgebraicGeometry.RadicialPreparationConstruction
import WeilConjectures.AlgebraicGeometry.RadicialPreparationFibreComparison

/-! # Radicial preparation before the final generic-flat shrinking

## References

* Stacks Project, Tag 0559, second proof, reduction and inseparable extension.
* Stacks Project, Tag 0559, second proof, reductions through the finite purely inseparable
  extension; Tags 051T and 052A. Proof: the nonempty generic fibre implies that the generic point
  belongs to V. Factor through V and reduce source and base. Reduction preserves geometric fibre
  spaces, and an irreducible reduced base is integral. Apply generic flat finite presentation and
  shrink to a principal open, whose inverse image in the affine source is affine. The reduced flat
  source embeds in its generic fibre, a domain. Let K be the base fraction field and L the fraction
  field of the generic fibre. A finite purely inseparable K'/K makes the reduced tensor product of L
  with K' separably generated. For each generator b with b^q=a/d, replace b by db, whose q-th power
  is a*d^(q-1). Adjoin these scaled generators to the base ring. This finite integral radicial
  domain has fraction field K'.
-/

@[expose] public section

universe u
open CategoryTheory Topology
namespace AlgebraicGeometry

/-- Construct an affine radicial model with reduced source and geometrically reduced
 generic fibre; flatness and finite presentation are deferred to a subsequent shrinking. -/
theorem exists_radicial_generic_reduced_preparation
    {X T : Scheme.{u}} [IsAffine X] (f : X ⟶ T) [LocallyOfFiniteType f]
    (V : T.Opens) (hV : IsAffineOpen V) (himage : Set.range f ⊆ V)
    (η : T) (hη : IsGenericPoint η Set.univ)
    (hgeom : GeometricallyIrreducible (f.fiberToSpecResidueField η)) :
    ∃ (U : T.Opens), η ∈ U ∧ IsAffineOpen U ∧
      ∃ (S Y : Scheme.{u}) (q : S ⟶ U.toScheme) (g : Y ⟶ S),
        IsAffine S ∧ IsIntegral S ∧ IsAffine Y ∧ IsReduced Y ∧
        IsUniversalHomeomorphism q ∧ LocallyOfFiniteType g ∧
        ∃ η' : S, IsGenericPoint η' Set.univ ∧ (q ≫ U.ι) η' = η ∧
          GeometricallyReduced (g.fiberToSpecResidueField η') ∧
          ∀ s : S, GeometricallyIrreducible (g.fiberToSpecResidueField s) ↔
            GeometricallyIrreducible (f.fiberToSpecResidueField ((q ≫ U.ι) s)) := by
  obtain ⟨U, hηU, hUa, S, Y, q, g, hSa, hSi, hYa, hYr, hq, hfg, η', hη', hqη', hred, h, hh, hg⟩ :=
    exists_radicial_preparation_construction f V hV himage η hη hgeom
  have : IsUniversalHomeomorphism h := hh
  have hcmp (s : S) := exists_radicial_preparation_fibre_comparison f (q ≫ U.ι) h s
  rw [hg] at hcmp
  exact ⟨U, hηU, hUa, S, Y, q, g, hSa, hSi, hYa, hYr, hq, hfg,
    η', hη', hqη', hred, hcmp⟩

end AlgebraicGeometry
