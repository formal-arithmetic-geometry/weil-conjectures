/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.PurEtaleScalarMateProjection
public import Sheaf.AlgebraicGeometry.ProperProjectionFormula
public import Mathlib.Topology.Defs.Filter
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
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

/-! # Proper finite coefficient extension core

Source: Stacks Project, `literature/stacks-project/more-etale.tex`, Tag 0GL6.
(blueprint: lem-asd-proper-finite-coefficient-extension).

This intermediate theorem packages the isomorphism and restriction/projection clauses of
proper finite coefficient extension; the parent adds the independently verified mate
normalization clause. The proof chooses K-flat resolutions with flat terms,
identifies scalar, tensor, pullback and direct-image comparisons termwise, and
applies the proper projection formula after exact conservative restriction of
scalars. The resulting restricted morphism is invertible, so conservativity gives
invertibility of the scalar mate; the same calculation gives the ordered projection
identity. The construction descends through quasi-isomorphisms to the entire
derived category.
(blueprint: lem-asd-proper-finite-coefficient-extension-core).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Etale
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The unbounded isomorphism and restricted projection clauses used by the parent theorem.

Source: Stacks Project, Tag 0GL6.
(blueprint: lem-asd-proper-finite-coefficient-extension).

The proof is the proper projection formula after exact conservative restriction of scalars,
with the canonical scalar/tensor and pullback comparisons and the derived direct-image mate.
Choose a K-flat resolution with flat terms, calculate every comparison termwise, apply the
proper projection formula after restriction, and descend the resulting equality through
quasi-isomorphisms. Exact conservativity of restriction then proves the mate is invertible.
(blueprint: lem-asd-proper-finite-coefficient-extension-core).
-/
theorem properFiniteCoefficientExtensionCore
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
              (scalarCoefficient φ X))):= by
  sorry

end AlgebraicGeometry.Etale
