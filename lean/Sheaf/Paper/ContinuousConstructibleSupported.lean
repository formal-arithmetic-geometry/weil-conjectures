/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E5
-/
module
public import Sheaf.Paper.IntegralModelOpenClosedBasic
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Constructibility of supported continuous modules

Source: Bhatt--Scholze, Definition 6.8.10 and Lemma 6.8.13;
Stacks Project, Tags 09AH and 03DI
(blueprint: lem-weil-pbc-continuous-constructible-supported).
-/
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale

/-- Supported extension preserves finite-stratification constructibility whenever
continuous coefficients restrict correctly along immersions.
Source: Bhatt--Scholze, Definition 6.8.10 and Lemma 6.8.13;
Stacks Project, Tags 09AH and 03DI
(blueprint: lem-weil-pbc-continuous-constructible-supported).
Proof: for extension by zero, take a witnessing finite stratification of U and
compose its immersions with U -> X. Append Z as one additional stratum. The ranges
are locally closed, disjoint, and cover X; they are constructible since X is
noetherian. Restriction to each old stratum identifies with the original module
restriction. First identify the actual ordinary change of rings along a coefficient
isomorphism with the scalar-equivalence left adjoint, by uniqueness of left
adjoints to scalar restriction. Composition of ringed inverse images then applies;
its coefficient square follows by taking adjuncts of precomposition of continuous
functions along the two base-change projections. Thus the open unit identifies
the old restrictions. Restriction to Z is zero by continuous-coefficient open-closed
localization. Retain the old pro-etale covers and finitely presented local models;
on Z use the singleton identity cover and the finitely presented zero module.
For closed direct image, compose a witnessing stratification of Z with i and
append U. The closed counit gives the original restrictions on Z and the open
restriction is zero. The same cover and zero-model argument gives a witnessing
stratification. Empty strata and zero local models are allowed throughout. -/
theorem continuousConstructible_supported
    (T : Type u) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    (hT : ∀ (Y W : Scheme.{u}) [IsNoetherian Y] (f : W ⟶ Y) [IsImmersion f],
      IsIso (continuousCoefficientInverseImageMap f T))
    {X Z : Scheme.{u}} [IsNoetherian X] (i : Z ⟶ X) [IsClosedImmersion i]
    (U : X.ProEt) [IsOpenImmersion U.hom]
    (hU : Set.range U.hom = (Set.range i)ᶜ) :
    (∀ M : SheafOfModules.{u + 1} (latticeModuleRing U.left T),
      @IsContinuousConstructible U.left
        (U.hom.isEmbedding.isInducing.noetherianSpace (α := X)) T
        inferInstance inferInstance inferInstance M →
      IsContinuousConstructible X T ((continuousModuleExtensionByZero U T).obj M)) ∧
    (∀ M : SheafOfModules.{u + 1} (latticeModuleRing Z T),
      @IsContinuousConstructible Z
        (i.isEmbedding.isInducing.noetherianSpace (α := X)) T
        inferInstance inferInstance inferInstance M →
      IsContinuousConstructible X T ((continuousModuleDirectImage i T).obj M)) := by sorry

end AlgebraicGeometry.ProEtale
