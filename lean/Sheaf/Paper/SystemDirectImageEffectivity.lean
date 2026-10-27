/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y6
-/
module

public import Sheaf.Paper.IntegralComparisonSystemData
public import Sheaf.Paper.SfIntegralDirectImageConstructible

/-! # Effectivity of whole-system direct image of a coherent reduction

Source: Zheng, Construction 4.1 and Lemma 4.10; Stacks Project, Tag 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Direct image of one coherent quotient system is effective for reconstruction.
This concerns the actual whole-system counit, before any pullback or source comparison.
Source: Zheng, Construction 4.1 and Lemma 4.10; Stacks Project, Tag 0941;
blueprint integral direct-image comparison
(blueprint: lem-weil-system-direct-image-effectivity).
Proof: choose one simultaneous resolution of the reduction system of K for the
sectionwise direct images. The section-normalized finite evaluation comparisons
identify its finite levels with the corresponding derived finite direct images,
including the quotient transition maps. Finite-type constructibility and the
integral direct-image finite reduction comparisons make this one strict system
cartesian, with the bounded constructible integral realization given by its Roos
presentation. Apply normalized reconstruction to this cartesian system. Its
reconstruction map is the counit of D.system Y: the reduction and limit models
retain the simultaneous-resolution projection normalization, so their actual
counit is the projection-normalized reconstruction map. It is therefore an
isomorphism in the derived category of entire systems. This assertion uses neither
faithfulness of finite evaluation nor an arbitrary choice of finite-level
isomorphisms. Empty schemes and zero complexes give the zero counit isomorphism. -/
theorem systemDirectImage_effective
    (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
    [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of K₀))]
    [(integralComparisonSequenceDirectImage l E f).Additive]
    [Abelian.HasKInjectiveResolutions (coefficientSequenceModules l E X)]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : IntegralComparisonCoefficientData l E) (K : sfIntegralConstructibleCategory l E X) :
    IsIso ((D.system Y).adjunction.counit.app
      ((integralComparisonSequenceDirectImage l E f).rightDerivedFunctor.obj
        ((D.system X).reduction.obj K.obj))) := by sorry

end WeilConjectures
