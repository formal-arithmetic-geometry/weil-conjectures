/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingMap
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.FourCornersSupplement
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Scalar.ProEtaleScalarMateIdentifications
public import WeilConjectures.AlgebraicGeometry.Direct.DirectImageScalarOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Scalar.ProEtaleScalarBalancingChain
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantExact
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.AlgebraicGeometry.PulledNormalization.PulledReductionNormalizationComparison

/-! # Unbounded coefficient comparison on flat-term K-flat pullback models

Source: Stacks Project, sites-cohomology.tex, Tags 0G7E, 06YT, 06YY, 0G7D;
sites-modules.tex, Tag 03EL; blueprint thm-exc-explicit-preservation, proof paragraph 2.
(blueprint: lem-exc-unbounded-coefficient-pullback-model).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/-- Compute coefficient extension after exact pullback using a supplied representative.
This is the pullback factorization followed by the existing universal scalar counit.
Source: Stacks 06YT, 06YY (blueprint: lem-exc-unbounded-coefficient-pullback-model). -/
def excPullbackThenCoefficientComputation
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {V X : Scheme.{u}} (f : V ⟶ X)
    (P : CochainComplex (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ)
    (K : proEtaleDerivedCategory X A) (i : DerivedCategory.Q.obj P ≅ K) :=
  (directImageScalarExtension φ V).map
    ((proEtaleConstantRingDerivedPullback A f).map i.inv ≫
      (proEtaleConstantRingPullback A f).mapDerivedCategoryFactors.hom.app P) ≫
    reductionScalarComplexCounit V (proEtaleConstantRingMap (T := V) φ)
      (((proEtaleConstantRingPullback A f).mapHomologicalComplex (.up ℤ)).obj P)

/-- Compute pullback after coefficient extension using the same representative.
This applies exact B-pullback to the existing scalar counit, then its factorization.
Source: Stacks 06YT, 06YY (blueprint: lem-exc-unbounded-coefficient-pullback-model). -/
def excCoefficientThenPullbackComputation
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {V X : Scheme.{u}} (f : V ⟶ X)
    (P : CochainComplex (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ)
    (K : proEtaleDerivedCategory X A) (i : DerivedCategory.Q.obj P ≅ K) :=
  (proEtaleConstantRingDerivedPullback B f).map
    ((directImageScalarExtension φ X).map i.inv ≫
      reductionScalarComplexCounit X (proEtaleConstantRingMap (T := X) φ) P) ≫
    (proEtaleConstantRingPullback B f).mapDerivedCategoryFactors.hom.app
      (((proEtaleRingExtension (proEtaleConstantRingMap (T := X) φ)).mapHomologicalComplex
        (.up ℤ)).obj P)

end AlgebraicGeometry.ProEtale
