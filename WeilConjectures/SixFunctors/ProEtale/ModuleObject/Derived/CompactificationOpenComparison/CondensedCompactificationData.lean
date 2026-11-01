/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactificationReindexing.CondensedCompactificationReindexing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.Endofunctor.CyclicDerivedHomData
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
public import Mathlib.CategoryTheory.Triangulated.TStructure.Heart
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import WeilConjectures.CategoryTheory.SmoothBaseChange.CohomologyInWeakSerreSubcategory
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import WeilConjectures.WeilSheaf.StrictWeilComplexNotFaithful
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportLinePull
import WeilConjectures.AlgebraicGeometry.PurityTransport.Coefficient.TransportCoefficients
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteCoefficientEncodingDataSupplement
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteRestrictionEncodingSupplement
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportRoot
public import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionDataSupplement
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.AlgebraicGeometry.SixFunctors.PointProEtaleSectionsExactOfUniverses
public import WeilConjectures.AlgebraicGeometry.IntegralCtfEqualsBc
public import WeilConjectures.SmoothPurity.CondensedWeilModules
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.Compactification.BoundaryRefinement
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteCoefficientTriangulated
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import WeilConjectures.CategoryTheory.Constant.ConstantModuleFiniteTypeReflection
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.Data.ZMod.Basic
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Localizing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.WeaklyEtale
import WeilConjectures.CategoryTheory.Adjunction.ExchangeRightPaste
import WeilConjectures.SixFunctors.FiniteFieldDatum.FrobeniusSquareCartesian

/-! # Condensed compactification and Frobenius data

Source: latest blueprint, part-weights-riemann-hypothesis/sec-deligne-laumon-general/
sec-quasi-finite-maps-and-curves-preserving-irreducibility/sk-l-dl-general-quasifinite/
lem-zl-quasi-finite.proof.md, first paragraph, and part-six-operations/
sec-six-functors-basics/sec-brown-construction/sec-construction-of-rf/
sk-prop-sf-comp-coherence/det-sf-comp-coherence-refinement.proof.md
(blueprint: def-zl-condensed-compactification-data).

The comparison is normalized by the existing native refinement arrows. Open restriction
is the existing proper/open exchange, whose two factors are adjunction mates. All endpoints
are ordinary derived categories of internal modules over the actual condensed coefficient.
The context record only bundles the hypotheses; it imposes no absolute separatedness.
-/

@[expose] public noncomputable section
set_option autoImplicit false
-- Check the native derived proofs sequentially to limit peak memory.
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false

universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.CompactificationOpenComparison

open CompactificationReindexing

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory derivedUpperStarLowerStarAdjunction
  leftDerivedUpperStarTensor leftDerivedUpperStarComp pullbackSquareComparison

attribute [instance] Model.finiteX Model.compactX Model.qsX Model.finiteY Model.compactY
  Model.qsY Model.separated Model.finite Model.compact

/-- The middle model has its induced structure morphism over k0.
Source: latest blueprint refinement proof, compactification diagrams
(blueprint: def-zl-condensed-compactification-data). -/
abbrev middle₀ {D : WeilConjectures.FiniteFieldDatum.{u}} (M : Model D)
    (c : Compactification M.f₀.left) : Over (Spec (.of D.k₀)) :=
  Over.mk (c.g ≫ M.Y₀.hom)

/-- The open arrow over k0, with its structure equation named separately.
Source: latest blueprint refinement proof, compactification diagrams
(blueprint: def-zl-condensed-compactification-data). -/
def open₀ {D : WeilConjectures.FiniteFieldDatum.{u}} (M : Model D)
    (c : Compactification M.f₀.left) : M.X₀ ⟶ middle₀ M c :=
  Over.homMk c.i (by
    change c.i ≫ (c.g ≫ M.Y₀.hom) = M.X₀.hom
    rw [← Category.assoc, ← c.comm]
    exact Over.w M.f₀)

end AlgebraicGeometry.ProEtale.CondensedRing.CompactificationOpenComparison
