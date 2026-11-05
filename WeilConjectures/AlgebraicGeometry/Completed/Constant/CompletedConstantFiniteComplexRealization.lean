/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Completed.Constant.CompletedConstantRealizationDataSupplement
import WeilConjectures.AlgebraicGeometry.Completed.Constant.CompletedConstantModuleModel
import WeilConjectures.AlgebraicGeometry.Completed.Constant.CompletedConstantResolutionTensorCalculation
import WeilConjectures.AlgebraicGeometry.Completed.Constant.CompletedConstantDerivedTensorTower
import WeilConjectures.AlgebraicGeometry.CompletedConstantReduction.CompletedConstantSheafReductionSupplement
import WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
import WeilConjectures.RingTheory.NoetherianPseudoCoherentCohomologyCriterion
import WeilConjectures.RingTheory.RingPseudoCoherent
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Noetherian.Basic
import WeilConjectures.RingTheory.FiniteFreeResolution
import WeilConjectures.RingTheory.PseudoCoherentOfCohomology
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.Single
import WeilConjectures.RingTheory.PseudoCoherentIffAllM
import WeilConjectures.RingTheory.MPseudoCoherentVanishingBase
import WeilConjectures.RingTheory.PseudoCoherentDistinguishedTriangle
import WeilConjectures.CategoryTheory.TruncationTriangle
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Abelian.Projective.Extend
import WeilConjectures.Algebra.Homology.DerivedCategory.ProjectiveHom
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Mathlib.Algebra.Category.FGModuleCat.Abelian
import Mathlib.Algebra.Homology.FullSubcategory
/-!
# Completed constant realization of finite complexes
Source: Stacks Project, proetale.tex, Tags 09BT and 09BV; sites-modules.tex,
Tags 093J--093M; algebra.tex, Tag 00MB
(blueprint: lem-weil-pbc-completed-constant-finite-complex-realization).
Positive quotient levels are indexed by `n : ℕ`, with exponent `n + 1`.
The comparison is stated on finite-free resolutions of bounded finite complexes.
Naturality on the category of resolutions includes independence of the resolution.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 1024
universe u v w vD vE
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
