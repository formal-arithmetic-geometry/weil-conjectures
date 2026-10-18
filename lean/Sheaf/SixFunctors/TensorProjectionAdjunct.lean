/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q84
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison

/-!
# Adjoint of a tensor-projected morphism

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
`sk-lem-geo-p1-cohomology/thm-amb-p1-decomposition.proof.md`
(blueprint: lem-amb-tensor-projection-adjunct).

The statement records the mate calculation for the symmetrized ordinary derived projection
map.  The proof is postponed: it expands the projection-map mate, uses the canonical inverse
image tensor comparison and its symmetry compatibility, then uses bifunctoriality of derived
tensor.
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/--
Source: the final tensor/projection-formula sentence of
`thm-amb-p1-decomposition.proof.md` (blueprint: lem-amb-tensor-projection-adjunct).

For an arbitrary scheme morphism and commutative coefficient ring, the adjoint of the
symmetrized projection map after tensoring with `a` is tensoring the adjoint of `a` with the
fixed inverse-image factor.  The proof expands the mate of the canonical projection map,
uses the natural inverse-image tensor comparison and the signed tensor symmetry, and then
uses the derived tensor bifunctor law.  No properness, boundedness, finiteness, torsion or
invertibility hypothesis is used.
-/
theorem tensorProjectionAdjunct
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K M : DerivedCategoryModule Λ Y) (E : DerivedCategoryModule Λ X)
    (a : M ⟶ (R((f)_*[ModuleCat.{u + 1} Λ])).obj E) :
    ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).homEquiv
        (((derivedTensor (ModuleCat.{u + 1} Λ) Y).obj K).obj M)
        (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj
          ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)).obj E)).symm
      (((derivedTensor (ModuleCat.{u + 1} Λ) Y).obj K).map a ≫
        ((derivedTensorSymmetry (ModuleCat.{u + 1} Λ) Y).hom.app K).app
          ((R((f)_*[ModuleCat.{u + 1} Λ])).obj E) ≫
        ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) f).app E).app K ≫
        (R((f)_*[ModuleCat.{u + 1} Λ])).map
          (((derivedTensorSymmetry (ModuleCat.{u + 1} Λ) X).hom.app E).app
            ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K))) =
      ((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} Λ) f).app K).app M ≫
        ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj
          ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)).map
          ((L((f)^*[ModuleCat.{u + 1} Λ])).map a ≫
            (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).counit.app E) := by
  sorry


end AlgebraicGeometry.Etale
