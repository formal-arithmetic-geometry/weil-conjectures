/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Defs.Filter
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
import Sheaf.AlgebraicGeometry.ProperTorsionProjectionFormula
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact

/-!
# The proper projection formula with the base factor first

Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/lem-amb-proper-coproducts-projection.md`
(blueprint: lem-amb-proper-coproducts-projection); Stacks Project, Tag 0F0G, and Tag 06YU.

The map is the specified composite of the canonical signed derived symmetry, the
adjoint-of-counit projection map, and direct image of the signed symmetry on the source.
The derived inverse image is the exact termwise inverse image through
`leftDerivedUpperStarIsoMapDerivedCategory`; no boundedness condition is imposed.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- The proper projection formula for ordinary unbounded small-etale module complexes, with
finite commutative coefficients and the tensor factors ordered as in the blueprint.
Source: Stacks Project, Tag 0F0G and the signed symmetry following Tag 06YU
(blueprint: lem-amb-proper-coproducts-projection).

Proof:
1. Finiteness of `A` implies additive torsion, including for the zero ring: two multiples
   `i * 1` and `j * 1`, with `i < j`, coincide, and `(j-i) * a = 0` for every `a`.
   By prop-weil-pbc-inverse-image-modules-exact the module inverse image is exact;
   applying it termwise preserves acyclic complexes and quasi-isomorphisms, without bounds.
2. Apply lem-kun-0f0g with `f = r`, `E = L`, and this `K`. Properness and the torsion
   condition give invertibility of the middle, adjoint-of-counit projection map. Its
   finite-coefficient specialization is also the existing upstream theorem
   `isIso_rightDerivedLowerStarProjectionMap_of_finite`. Neither a uniform cohomological
   dimension bound on `T` nor a Tor-amplitude condition on either complex is needed.
3. By lem-kun-tensor-sym, the first symmetry `s` and the source symmetry `t` are the
   canonical isomorphisms induced by the signed swap on K-flat complexes. The displayed
   composite is `s ≫ PF ≫ Rr_*(t)`. Its inverse is `Rr_*(t.inv) ≫ PF.inv ≫ s.inv`;
   functoriality and cancellation of the three inverse pairs give the result. -/
theorem isIso_proper_projection_formula_reordered
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {V T : Scheme.{u}} (r : V ⟶ T) [IsProper r]
    [IsLocallyNoetherian V] [CompactSpace V] [IsLocallyNoetherian T] [CompactSpace T]
    (L : DerivedCategoryModule A V) (K : DerivedCategoryModule A T) :
    IsIso (
      ((derivedTensorSymmetry (ModuleCat.{u + 1} A) T).hom.app K).app
          ((lowerStar (ModuleCat.{u + 1} A) r).rightDerivedFunctor.obj L) ≫
        ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) r).app L).app K ≫
        (lowerStar (ModuleCat.{u + 1} A) r).rightDerivedFunctor.map
          (((derivedTensorSymmetry (ModuleCat.{u + 1} A) V).hom.app L).app
            ((upperStar (ModuleCat.{u + 1} A) r).leftDerivedFunctor.obj K))) := by
  sorry

end AlgebraicGeometry.Etale
