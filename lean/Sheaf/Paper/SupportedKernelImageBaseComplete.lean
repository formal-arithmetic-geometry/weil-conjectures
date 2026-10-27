/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.SixFunctors.ProEtale.DerivedCompletion
public import Mathlib.CategoryTheory.Abelian.Images
import Sheaf.Paper.FiniteScalarLocalModelComplete
import Sheaf.Paper.StrictCompletionRestrictionComparison
import Sheaf.Paper.SectionIntegralPrincipalCompletionModel
import Sheaf.Paper.PrincipalCompleteHeartKernels
import all Sheaf.Paper.CompletionTriangleComparison
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images

/-! # Completeness of source kernels and images
Source: Bhatt--Scholze, Lemma 3.4.14 and Proposition 3.5.1.
-/
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
attribute [local instance 10000]
  AlgebraicGeometry.ProEtale.StrictCompletionRestriction.smallSiteLocalEquivalences
namespace AlgebraicGeometry.ProEtale
namespace SourceCompletion
open StrictCompletionRestriction
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

private theorem complete_iso
    {K L : DerivedCategory (AdicCompletion.Modules l E X)} (e : K ≅ L)
    (hK : IsDerivedComplete l E X K) : IsDerivedComplete l E X L := by
  obtain ⟨P, hP, ⟨i⟩, hc⟩ := hK
  exact ⟨P, hP, ⟨i ≪≫ e⟩, hc⟩

private theorem complete_iff
    (S : Presentation.{u + 2, u + 1, u + 1} (AdicCompletion.Modules l E X))
    (hS : StrictCompletionRestriction.IsIntegral l E X S)
    (K : DerivedCategory (AdicCompletion.Modules l E X)) :
    IsDerivedComplete l E X K ↔ IsIso (S.unit.app K) := by
  obtain ⟨data, hd, ht, hs, hr, hu, hc⟩ := hS
  exact CompletionTriangle.complete_iff_from_comparison l E X S.completion S.unit hc K
end SourceCompletion

/-- The ordinary source kernel and image of a map between finite scalar local models
are derived complete. No constancy of the morphism or closedness of its image is used.

Source: Bhatt--Scholze, Lemma 3.4.14 and Proposition 3.5.1.
(blueprint: lem-sfb-supported-kernel-image-base-complete)

Proof: Finite scalar local models are complete. The exact section-action equivalence
carries the specified completion unit to the section-integral unit, whose complete locus
is the principal quotient complete locus. Apply complete_heart_kernels to the actual
section-action image of f. Exact equivalences preserve ordinary kernels and images.
Their canonical isomorphisms, the exact degree-zero comparison, and the normalized
completion-unit comparison transport the two conclusions back to internal modules. -/
theorem supported_kernel_image_base_complete
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X : Scheme.{u}} (L M : AdicCompletion.Modules l E X) (f : L ⟶ M)
    (hL : HasFiniteConstantLocalModel (DerivedNakayama.integerRing l E) X L)
    (hM : HasFiniteConstantLocalModel (DerivedNakayama.integerRing l E) X M) :
    IsDerivedComplete l E X ((DerivedCategory.singleFunctor _ 0).obj (kernel f)) ∧
    IsDerivedComplete l E X ((DerivedCategory.singleFunctor _ 0).obj (image f)) := by
  classical
  obtain ⟨S, hS, hmodels, hsections, hrestrict⟩ :=
    StrictCompletionRestriction.strict_completion_restriction_comparison l E
  obtain ⟨T, hT, ⟨c⟩⟩ := hsections X
  obtain ⟨a, ha, F, hF⟩ :=
    StrictCompletionRestriction.section_integral_principal_completion_model l E X T hT
  let G := (ModuleObjectRingedComparison.equivalence (DerivedNakayama.integerRing l E) X).functor
  have he (N : AdicCompletion.Modules l E X) :
      IsDerivedComplete l E X ((DerivedCategory.singleFunctor _ 0).obj N) ↔
        PrincipalQuotientCompletion.Model.IsCompleteModule F (G.obj N) := by
    rw [SourceCompletion.complete_iff l E X (S X) (hS X)]
    change IsIso ((S X).unit.app ((DerivedCategory.singleFunctor _ 0).obj N)) ↔
      IsIso (F.unit.app ((DerivedCategory.singleFunctor _ 0).obj (G.obj N)))
    rw [← hF]
    refine Iff.trans ?_ (NatTrans.isIso_app_iff_of_iso T.unit
      ((G.mapDerivedCategorySingleFunctor 0).app N))
    refine Iff.trans ?_ (iff_of_eq (congrArg IsIso
      (c.unit ((DerivedCategory.singleFunctor (AdicCompletion.Modules l E X) 0).obj N))))
    constructor
    · intro h
      have := h
      infer_instance
    · intro h
      have := h
      have hmap : IsIso (G.mapDerivedCategory.map
          ((S X).unit.app ((DerivedCategory.singleFunctor _ 0).obj N))) :=
        IsIso.of_isIso_comp_right _ (c.derived.hom.app _)
      exact isIso_of_reflects_iso _ G.mapDerivedCategory
  have hlocal (N : AdicCompletion.Modules l E X)
      (hN : HasFiniteConstantLocalModel (DerivedNakayama.integerRing l E) X N) :
      IsDerivedComplete l E X ((DerivedCategory.singleFunctor _ 0).obj N) :=
    SourceCompletion.complete_iso l E X
      ((DerivedCategory.singleFunctorIsoCompQ _ 0).app N).symm
      ((FiniteScalarCompletion.finite_scalar_local_model_complete l E X).1 N hN)
  obtain ⟨hk, hq, hi⟩ :=
    (PrincipalQuotientCompletion.Model.complete_heart_kernels.{u + 1, u, 0} X
      (ModuleObjectRingedComparison.ring (DerivedNakayama.integerRing l E) X) a ha F).1
      (G.obj L) (G.obj M) (G.map f) ((he L).mp (hlocal L hL)) ((he M).mp (hlocal M hM))
  constructor
  · apply (he (kernel f)).mpr
    exact (NatTrans.isIso_app_iff_of_iso F.unit
      ((DerivedCategory.singleFunctor _ 0).mapIso (PreservesKernel.iso G f).symm)).mp hk
  · apply (he (image f)).mpr
    exact (NatTrans.isIso_app_iff_of_iso F.unit
      ((DerivedCategory.singleFunctor _ 0).mapIso (PreservesImage.iso G f))).mp hi
end AlgebraicGeometry.ProEtale
