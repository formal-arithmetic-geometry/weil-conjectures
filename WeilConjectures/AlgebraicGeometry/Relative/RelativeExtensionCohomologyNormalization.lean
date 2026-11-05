/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Sites.RelativeTorsorExtension
public import WeilConjectures.CategoryTheory.Sites.TorsorExtensionPresentation
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.CategoryTheory.Sites.Torsor
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import Mathlib.CategoryTheory.Abelian.Exact
public import WeilConjectures.CategoryTheory.Sites.EtaleTorsorExtensionPresentationExists
public import WeilConjectures.CategoryTheory.Sites.ExtensionPresentationShortExact
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import WeilConjectures.AlgebraicGeometry.Relative.RelativeTorsorCohomology
public import WeilConjectures.AlgebraicGeometry.Relative.RelativeCocycleCoordinates
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerBoundarySupplement
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import WeilConjectures.CategoryTheory.Sites.EtaleTorsorExtensionPresentationExists
import WeilConjectures.CategoryTheory.Sites.TorsorExtensionPresentation
import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.CategoryTheory.Sites.Torsor
import WeilConjectures.CategoryTheory.Sites.ExtensionPresentationShortExact
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.AlgebraicGeometry.Relative.RelativeTorsorClassNaturality
import WeilConjectures.ConstructibleSheaf.UpperStarConstantSheafComp
import WeilConjectures.CategoryTheory.Abelian.FirstResolutionExtensionClass
import WeilConjectures.AlgebraicGeometry.Relative.RelativeTorsorForgetNormalization
import WeilConjectures.CategoryTheory.Abelian.ExtRightDerivedCocycleComparison
import WeilConjectures.AlgebraicGeometry.RelativeCone.PurityRelativeCone
import WeilConjectures.AlgebraicGeometry.OpenClosedIntegralSections
import WeilConjectures.AlgebraicGeometry.EtaleOpenCohomologyComparison
import WeilConjectures.SixFunctors.OpenClosed.Exact
import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerCoefficients
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import WeilConjectures.SixFunctors.Finite.BaseChange

/-! # Relative torsor extensions and normalized supported cohomology

Source: Stacks Project, Tags 03AJ, 06XR, 06XV and 0A45, relative refinement;
blueprint lem-pur-divisor-class, first sentence and forget-support paragraph
(blueprint: lem-pur-relative-extension-cohomology-normalization).

The comparison is uniquely specified on every resolution cocycle by evaluation at one
and the inclusion into the signed cone with zero open coordinate. The relative torsor
class is the negative of the existing raw lifting-cocycle equivalence.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite HomologicalComplex

namespace AlgebraicGeometry.Etale

attribute [local irreducible] relativeFiberMap relativeTorsorEquiv

end AlgebraicGeometry.Etale
