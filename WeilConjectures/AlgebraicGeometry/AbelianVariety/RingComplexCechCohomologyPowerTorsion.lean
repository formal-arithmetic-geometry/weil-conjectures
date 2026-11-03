/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ring.RingHomExtensionDefsSupplement
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
import WeilConjectures.CategoryTheory.Ring.RingHomExtensionDefsSupplement
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.CategoryTheory.SimplexPresentationFaithful
import WeilConjectures.AlgebraicGeometry.AbelianVariety.ModuleCupGodementRelations
import WeilConjectures.Topology.RingedSpaceModuleCohomology
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.DoubleComplexTotal
import WeilConjectures.CategoryTheory.CanonicalFiltration
import WeilConjectures.AlgebraicGeometry.AlternatingCechTotalComplex
import Mathlib.Topology.Sheaves.Flasque
import WeilConjectures.AlgebraicGeometry.AlternatingCechRestrictionHomotopy
import WeilConjectures.Topology.Sheaves.CechFlasque
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import WeilConjectures.AlgebraicGeometry.InjectiveAlternatingCechRowAugmentation
import WeilConjectures.AlgebraicGeometry.InjectiveTermsAlternatingCechAugmentation
import WeilConjectures.AlgebraicGeometry.QCohAlternatingCechResolutionQuasiIso
import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Topology.Sheaves.Abelian
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import Mathlib.CategoryTheory.Abelian.Exact
import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Types.Products
import WeilConjectures.AlgebraicGeometry.AbelianVariety.RingComplexOrderedCechCoordinates
import WeilConjectures.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing
import WeilConjectures.AlgebraicGeometry.Cohomology.Flasque
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.Ring.RingHomExtensionTransportSupplement
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.RingTheory.Flat.Localization
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # Element-power torsion in ordered localization-model cohomology -/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private abbrev point : (Discrete PUnit.{u + 1})ᵒᵖ := op ⟨PUnit.unit⟩

private noncomputable local instance pointEval_isEquivalence (A : CommRingCat.{u}) :
    (pointEval A).IsEquivalence := (pointEquivalence A).isEquivalence_functor

private local instance pointEval_additive (A : CommRingCat.{u}) :
    (pointEval A).Additive where
  map_add := by intros; rfl

end AlgebraicGeometry
