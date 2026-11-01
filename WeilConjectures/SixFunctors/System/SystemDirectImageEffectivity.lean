/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.Comparison.IntegralComparisonSystemData
public import WeilConjectures.SmoothPurity.Sf.SfIntegralDirectImageConstructible
import WeilConjectures.SixFunctors.System.SystemDirectImageRoosPresentation

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

end WeilConjectures

namespace WeilConjectures

private theorem transpose_isIso_of_projection_iso
    {A B : Type*} [Category A] [Category B]
    {F : A ⥤ B} {G : B ⥤ A} (adj : F ⊣ G)
    {U V : A} {M N : B} (e : U ≅ V) (a : M ≅ N)
    (p : U ⟶ G.obj M) (q : V ⟶ G.obj N)
    (h : p ≫ G.map a.hom = e.hom ≫ q)
    (hq : IsIso ((adj.homEquiv V N).symm q)) :
    IsIso ((adj.homEquiv U M).symm p) := by
  have hh := congrArg ((adj.homEquiv U N).symm) h
  rw [adj.homEquiv_naturality_right_symm, adj.homEquiv_naturality_left_symm] at hh
  let := hq
  have : IsIso ((adj.homEquiv U M).symm p ≫ a.hom) := by
    rw [hh]
    infer_instance
  exact IsIso.of_isIso_comp_right _ a.hom

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
        ((D.system X).reduction.obj K.obj))) := by
  let N := (integralComparisonSequenceDirectImage l E f).rightDerivedFunctor.obj
    ((D.system X).reduction.obj K.obj)
  obtain ⟨hp, L, e, a, ha⟩ := systemDirectImage_roosPresentation l E f (D.system X) K.obj
  let := hp
  have hred := ((sfIntegralDirectImage_constructible K₀ l hl E f K.obj K.property).2.1 L).2.2.1
  apply ((D.system Y).isIso_iff_evaluations _).2
  intro n
  let adj := coefficientFiniteAdjunction l E Y n
  have hi := transpose_isIso_of_projection_iso adj e (a n)
    ((coefficientSequenceProjection l E Y n).app N)
    (L.projection ≫ Pi.π (sfDirectImageTerm l E f K.obj) n) (ha n) (hred n)
  have hq : ((D.system Y).reductionEvaluation n).inv.app
        ((coefficientSequenceLimit l E Y).obj N) ≫
      (coefficientSequenceDerivedEvaluation l E Y n).map
        ((D.system Y).adjunction.counit.app N) =
      (adj.homEquiv _ _).symm ((coefficientSequenceProjection l E Y n).app N) := by
    apply (adj.homEquiv _ _).injective
    exact ((D.system Y).counit_projection N n).trans
      ((adj.homEquiv _ _).apply_symm_apply _).symm
  have : IsIso (((D.system Y).reductionEvaluation n).inv.app
        ((coefficientSequenceLimit l E Y).obj N) ≫
      (coefficientSequenceDerivedEvaluation l E Y n).map
        ((D.system Y).adjunction.counit.app N)) := by
    rw [hq]
    exact hi
  exact IsIso.of_isIso_comp_left
    (((D.system Y).reductionEvaluation n).inv.app
      ((coefficientSequenceLimit l E Y).obj N)) _

end WeilConjectures
