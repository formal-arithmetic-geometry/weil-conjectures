/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.PurEtaleScalarMateProjection
public import Sheaf.AlgebraicGeometry.ProperProjectionFormula
public import Mathlib.Topology.Defs.Filter
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorComparison
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.SixFunctors.TensorProjectionAdjunct
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison

/-! # Proper finite coefficient extension

Source: Stacks Project, `literature/stacks-project/more-etale.tex`, Tag 0GL6,
remark-Rf-lower-shriek-change-of-rings, proper case.
(blueprint: lem-asd-proper-finite-coefficient-extension).

The theorem records the canonical unbounded coefficient-change comparison, its
adjunction normalization, and the identification after restriction of scalars
with the coefficient-first proper projection morphism.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Etale
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- Canonical unbounded proper direct-image comparison for a finite coefficient extension.

Source: Stacks Project, Tag 0GL6, with the counit-transpose normalization of Tag 0B56
and the direct-image composition comparison of Tag 0D6E.
(blueprint: lem-asd-proper-finite-coefficient-extension).

Proof: use the canonical scalar extension and pullback comparison, and take their mate
under the two canonical derived inverse-image/direct-image adjunctions.  Exact restriction
of scalars is conservative and the proper projection theorem makes the coefficient-first
projection morphism invertible.  The canonical restricted direct-image comparison and the
canonical scalar/tensor comparisons identify the restricted mate with that projection;
therefore every component of the mate is invertible.  The mate construction is natural in
all objects, and its defining equation is exactly the displayed counit transpose.  No
flatness of the coefficient map or boundedness of the derived object is used.
-/
theorem properFiniteCoefficientExtension
    {R A : Type (u + 1)} [CommRing R] [CommRing A] [Finite R] [Finite A]
    (φ : R →+* A) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] [IsNoetherian X] [IsNoetherian Y] :
    (∀ L : DerivedCategoryModule R X,
      IsIso ((scalarMate φ f).app L)) ∧
    (∀ L : DerivedCategoryModule R X,
      ((derivedTensorSymmetry (ModuleCat.{u + 1} R) Y).hom.app
          (scalarCoefficient φ Y)).app
            (R((f)_*[ModuleCat.{u + 1} R]).obj L) ≫
        (scalarTensorIso φ Y).inv.app
          (R((f)_*[ModuleCat.{u + 1} R]).obj L) ≫
        (Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ).map
          ((scalarMate φ f).app L) ≫
        (scalarRestrictionDirectImageMap φ f).app
          ((scalarExtension φ X).obj L) ≫
        R((f)_*[ModuleCat.{u + 1} R]).map
          ((scalarTensorIso φ X).hom.app L ≫
            ((derivedTensorSymmetry (ModuleCat.{u + 1} R) X).hom.app L).app
              (scalarCoefficient φ X)) =
      ((derivedTensorSymmetry (ModuleCat.{u + 1} R) Y).hom.app
          (scalarCoefficient φ Y)).app
            (R((f)_*[ModuleCat.{u + 1} R]).obj L) ≫
        ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} R) f).app L).app
          (scalarCoefficient φ Y) ≫
        R((f)_*[ModuleCat.{u + 1} R]).map
          (((derivedTensor (ModuleCat.{u + 1} R) X).obj L).map
              ((scalarCoefficientPullbackIso φ f).hom) ≫
            ((derivedTensorSymmetry (ModuleCat.{u + 1} R) X).hom.app L).app
              (scalarCoefficient φ X))) ∧
    (∀ L : DerivedCategoryModule R X,
      (scalarMate φ f).app L =
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).homEquiv
          ((scalarExtension φ Y).obj
            (R((f)_*[ModuleCat.{u + 1} R]).obj L))
          ((scalarExtension φ X).obj L)
          ((scalarPullbackIso φ f).hom.app
              (R((f)_*[ModuleCat.{u + 1} R]).obj L) ≫
            (scalarExtension φ X).map
              ((derivedUpperStarLowerStarAdjunction
                (ModuleCat.{u + 1} R) f).counit.app L))) := by
  sorry

end AlgebraicGeometry.Etale
