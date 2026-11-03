/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleStratifiedPerfectCalculus
public import WeilConjectures.SmoothPurity.Supporting.ExcellentRing
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleExceptionalConstantTensor
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.Topology.KrullDimension
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import WeilConjectures.CategoryTheory.TruncationHypercohomology
import WeilConjectures.AlgebraicGeometry.SmoothPurity.NilpotentCoefficientDirectImageBound
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import WeilConjectures.AlgebraicGeometry.ProEtale.Classical.ProEtaleClassicalDirectImagePreservation
import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
import WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageMateCompatibility
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImageCanonicalMate
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImage
import WeilConjectures.AlgebraicGeometry.Classical.ClassicalContinuityMapSupplement
import WeilConjectures.SixFunctors.ProEtale.Comparison
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.AlgebraicGeometry.Projection.ProjectionComparisonEtaleProEtale
import WeilConjectures.AlgebraicGeometry.ProEtale.Classical.ProEtaleClassicalSheaves
import WeilConjectures.AlgebraicGeometry.Open.OpenTorBoundStalkFilteredExtension

/-! # Quasi-excellent finite-coefficient direct image and tensor

Source: Bhatt--Scholze, arXiv:1309.1198, Theorem 6.7.1 and Lemmas 6.5.11(1),(2),
6.7.2 and 6.7.17, specialized to `A = R/m^r`; the uniform cohomological dimension is
restricted to a finite-dimensional target as in ILO Exposé XIII Proposition 2.3.4 and
Theorem 4.2.1 (blueprint: lem-per-qe-finite-direct-image-tensor).
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale
open Scheme

/-- The canonical ordinary etale projection morphism with a termwise constant factor.
It is the existing derived projection morphism followed by the canonical pullback
identification of constant complexes.
Source: Bhatt--Scholze, Lemma 6.7.17
(blueprint: lem-per-qe-finite-direct-image-tensor). -/
noncomputable def qeFiniteCoefficientProjectionMap
    (A : Type (u + 1)) [CommRing A] {V T : Scheme.{u}} (h : V ⟶ T)
    (K : DerivedCategoryModule A V) (M : _root_.DerivedCategory (ModuleCat.{u + 1} A)) :
    ((derivedTensor (ModuleCat.{u + 1} A) T).obj
      ((lowerStar (ModuleCat.{u + 1} A) h).rightDerivedFunctor.obj K)).obj
      ((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).mapDerivedCategory.obj M) ⟶
    (lowerStar (ModuleCat.{u + 1} A) h).rightDerivedFunctor.obj
      (((derivedTensor (ModuleCat.{u + 1} A) V).obj K).obj
        ((constantSheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)).mapDerivedCategory.obj M)) :=
  ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) h).app K).app
      ((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).mapDerivedCategory.obj M) ≫
    (lowerStar (ModuleCat.{u + 1} A) h).rightDerivedFunctor.map
      (((derivedTensor (ModuleCat.{u + 1} A) V).obj K).map
        ((exceptionalConstantPullbackIso A h).hom.app M))

/- BLUEPRINT QUESTION (2026-11-01, P4): the node anchors this argument to the
opening ambient/CosuppCon clause of def-per-perverse-subcategories. In latest,
that definition only specifies perverse subcategories; def-per-support-condition
uses Verdier duality over a field. Neither contains the quasi-excellent
finite-coefficient exceptional-adjoint route named by this node. Reconcile the
anchor and the current unit route before filling this proof; see the P4 report.
The existing theorem and proof plan are preserved pending that review. -/

end AlgebraicGeometry.Etale
