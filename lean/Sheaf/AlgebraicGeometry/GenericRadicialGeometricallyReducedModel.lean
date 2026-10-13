/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism

import Sheaf.AlgebraicGeometry.GenericFlatFinitePresentation

/-! # A generically geometrically reduced model after a radicial base change

Source: Stacks Project, Tag 0559, second proof, reductions and inseparable extension.
-/

@[expose] public section

universe u
open CategoryTheory Topology
namespace AlgebraicGeometry

/-- Replace an affine family by a reduced flat finitely presented affine family
with geometrically reduced generic fibre, without changing geometric fibre spaces.

Source: Stacks Project, Tag 0559, second proof, through the paragraph preceding
its separating transcendence basis construction; Tags 051T and 052A.
Proof: nonemptiness of the generic fibre puts the generic point in V. Factor
through V and reduce both affine schemes. The base reduction is integral and
both reduction maps are universal homeomorphisms. Generic flat finite
presentation, followed by a basic-open shrinking, makes the reduced family flat
and finitely presented over an integral affine base. Flatness embeds its reduced
coordinate ring in its generic fibre ring, which is a domain. Let L be its
fraction field and K the base fraction field. Choose a finite purely inseparable
extension K'/K such that the reduction of L tensor K' is separably generated.
Scale each generator b with b^q=a/d to db: its q-th power is a*d^(q-1) in the
base ring. Adjoining these scaled generators gives a finite radicial integral
base algebra with fraction field K'. Its spectrum is a universal homeomorphism.
Base change the source and reduce it. Its generic fibre is now geometrically
reduced: its function field is separably generated, and its coordinate ring
embeds in that field after all field extensions. Apply generic flat finite
presentation again. Choose a basic open of the original affine base contained
in the image of this shrinking; pull everything back to it. The new base S
and source Y are affine, S is integral, and Y is reduced. The unique point above
the original generic point is generic. Reduction and radicial base change
preserve all geometric fibre spaces, giving the displayed equivalence at every
point of S. This construction also works in characteristic zero (take K'=K),
and in relative dimension zero. The generic fibre hypothesis excludes an empty
source.

(blueprint: lem-sbc-generic-radicial-geometrically-reduced-model) -/
theorem exists_generic_radicial_geometrically_reduced_model
    {X T : Scheme.{u}} [IsAffine X] (f : X ⟶ T) [LocallyOfFiniteType f]
    (V : T.Opens) (hV : IsAffineOpen V) (himage : Set.range f ⊆ V)
    (η : T) (hη : IsGenericPoint η Set.univ)
    (hgeom : GeometricallyIrreducible (f.fiberToSpecResidueField η)) :
    ∃ (U : T.Opens), η ∈ U ∧
      ∃ (S Y : Scheme.{u}) (q : S ⟶ U.toScheme) (g : Y ⟶ S),
        IsAffine S ∧ IsIntegral S ∧ IsAffine Y ∧ IsReduced Y ∧
        IsUniversalHomeomorphism q ∧ Flat g ∧ LocallyOfFinitePresentation g ∧
        ∃ η' : S, IsGenericPoint η' Set.univ ∧ (q ≫ U.ι) η' = η ∧
          GeometricallyReduced (g.fiberToSpecResidueField η') ∧
          ∀ s : S, GeometricallyIrreducible (g.fiberToSpecResidueField s) ↔
            GeometricallyIrreducible (f.fiberToSpecResidueField ((q ≫ U.ι) s)) := by sorry

end AlgebraicGeometry
