/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Tensor.TensorPullbackFrames
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
public import WeilConjectures.AlgebraicGeometry.Relative.RelativeCocycleCoordinates
public import WeilConjectures.AlgebraicGeometry.CartierPoleBoundary
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerBoundarySupplement
public import WeilConjectures.AlgebraicGeometry.Relative.RelativeTorsorCohomology
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
public import WeilConjectures.CategoryTheory.YonedaExtension.YonedaExtensionData
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import WeilConjectures.AlgebraicGeometry.Modules.IdealSheafFiniteType
import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
import WeilConjectures.AlgebraicGeometry.EffectiveCartierSum
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Braided
import WeilConjectures.AlgebraicGeometry.Relative.RelativeExtensionCohomologyNormalization
import WeilConjectures.AlgebraicGeometry.Relative.RelativeTorsorAddition
import WeilConjectures.CategoryTheory.Sites.SmoothPurity.BinaryTorsorQuotient
import all WeilConjectures.AlgebraicGeometry.CartierComplementFrame
import all WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerBoundarySupplement
import all WeilConjectures.AlgebraicGeometry.Modules.SectionAvoidance
import all WeilConjectures.AlgebraicGeometry.InternalHomRestrictScheme
import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-! # Tensor addition of framed Cartier pairs

Source: Stacks Project, Tags 01WT, 01WU, 03AJ, 010L, 0117 and 0G78;
blueprint main-20261015, lem-pur-divisor-class, clause (b).
(blueprint: lem-pur-cartier-pair-tensor-addition)

The geometric, framed-torsor, relative-class, extension-class and naturality clauses
are recorded separately. Restriction uses the actual shifted cone, and the relative
class is minus the raw lifting class, as required by the Ext normalization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MonoidalCategory Opposite
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
section
attribute [local irreducible] supportedDivisorSection Scheme.Modules.dualEvaluation
  Scheme.IdealSheafData.toModules

end

section
attribute [local irreducible] cartierPairFrameTorsor cartierPairFrameVal

-- Explicit frame and pseudofunctor comparisons require additional elaboration.
end

section
attribute [local irreducible] cartierPairFrameTorsor cartierPairFrameVal

end

end AlgebraicGeometry.Etale
