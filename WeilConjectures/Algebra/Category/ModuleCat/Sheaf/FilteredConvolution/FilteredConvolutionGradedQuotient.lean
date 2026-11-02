/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients
public import WeilConjectures.CategoryTheory.FiniteFiltrationInductionExtension
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FilteredConvolutionCore.FilteredConvolutionCanonicalComparisonIso
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FilteredConvolutionCore.FilteredConvolutionCanonicalComparisonUnique
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FilteredConvolutionCore.FilteredConvolutionFiltration
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FilteredConvolutionCore.FilteredConvolutionGradedQuotientCore

/-! # Graded quotients of the convolution tensor filtration

Source: latest blueprint, part-duality-trace-formula/sec-lefschetz-verdier/
sec-trace-classes-and-the-lefschetz-verdier-formula/sec-additivity-of-trace-classes/
sk-i-additivity/sk-i-additivity.proof.md,
"Filtered operations", third graded identity and the sentence on Koszul signs
(blueprint: lem-trf-filtered-convolution-graded-quotient).

The helper predicates specify the convolution by its actual image sum and the comparison
by its composites with tensor quotient projections. They impose no chosen splitting on Q
and no differential-compatible splitting on P. All tensors are the existing total tensor
of cochain complexes, whose second differential has sign (-1)^i in cochain degree i.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace SheafOfModules
namespace FilteredConvolution

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {R : Sheaf J CommRingCat.{w}}

/-- The recorded general-site module category, with coefficient-sized modules.
Source: latest blueprint, sk-i-additivity.proof.md, Filtered operations
(blueprint: lem-trf-filtered-convolution-graded-quotient). -/
abbrev Modules (R : Sheaf J CommRingCat.{w}) :=
  ringedSiteModules.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)

/-- Integer cochain complexes in the recorded category of module sheaves.
Source: latest blueprint, sk-i-additivity.proof.md, Filtered operations
(blueprint: lem-trf-filtered-convolution-graded-quotient). -/
abbrev Complex (R : Sheaf J CommRingCat.{w}) := CochainComplex (Modules R) ℤ

/-- The convolution filtration level. -/
abbrev level {P Q : Complex R} (F : DecreasingFiltration P)
    (G : DecreasingFiltration Q) (r : ℤ) : Subobject (P ⊗ Q) :=
  FilteredConvolutionCore.level F G r

/-- The direct sum of tensor products of the existing graded quotient complexes.
Source: latest blueprint, sk-i-additivity.proof.md, Filtered operations, third graded identity
(blueprint: lem-trf-filtered-convolution-graded-quotient). -/
abbrev gradedSource {P Q : Complex R} (F : DecreasingFiltration P) (G : DecreasingFiltration Q)
    (r : ℤ) : Complex R :=
  ∐ (fun p : ℤ ↦ F.gradedPiece p ⊗ G.gradedPiece (r - p))

/-- The canonical comparison predicate. -/
abbrev IsCanonical {P Q : Complex R} (F : DecreasingFiltration P)
    (G : DecreasingFiltration Q) (H : DecreasingFiltration (P ⊗ Q)) (r : ℤ)
    (α : gradedSource F G r ⟶ H.gradedPiece r) : Prop :=
  FilteredConvolutionCore.IsCanonical F G H r α

set_option maxHeartbeats 800000 in
-- Elaborating the total-tensor quotient diagram exceeds the default heartbeat limit.
end FilteredConvolution
end SheafOfModules
