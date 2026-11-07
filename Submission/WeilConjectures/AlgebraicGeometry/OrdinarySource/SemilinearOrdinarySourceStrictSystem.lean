/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.SemilinearSystemModels
public import Submission.WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
public import Submission.WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import Submission.WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Submission.WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Submission.WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Submission.WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import Submission.WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import Submission.WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.Hom
public import Submission.WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Generator.Basic
public import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import Submission.WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import Submission.WeilConjectures.Algebra.Homology.HomComplex
public import Submission.WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import Submission.WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
public import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Submission.WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import Submission.WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Submission.WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.Abelian
public import Submission.WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import Submission.WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import Submission.WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Submission.WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import Submission.WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Submission.WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Submission.WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import Submission.WeilConjectures.Algebra.Homology.HomComplexProjections
public import Submission.WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import Submission.WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import Submission.WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Submission.WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import Submission.WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import Submission.WeilConjectures.Algebra.Homology.HomComplexComponents
public import Submission.WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import Submission.WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
public import Submission.WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Submission.WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import Submission.WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import Submission.WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Limits.Final
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import Submission.WeilConjectures.Algebra.Homology.System.SystemLevelLeftExtensionBasic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # The prescribed ordinary system as a strict system

Source: Zheng Construction 4.1; Stacks 03D1.
(blueprint: def-coef-ordinary-source-strict-system).

The levels and transitions are literally the existing evaluation and transition operations.
Their strict laws follow from the section formula and the presheaf functor laws.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false
universe c v r
open CategoryTheory Opposite

section
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

namespace WeilConjectures.SemilinearSections.OrdinarySource

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r}) (τ : ∀ n, B (n + 1) ⟶ B n)

-- Keep the section map separate from the coefficient transports during elaboration.
/-- The horizontal map on section carriers, separated from its scalar transports.
Source: Zheng Construction 4.1; the section formula in SemilinearSystemModels.
(blueprint: def-coef-ordinary-source-strict-system). -/
def sourceSection (M : Systems.{c, v, max c v r} J B τ)
    {m n : ℕ} (h : n ≤ m) (U : Cᵒᵖ) :
    M.val.obj (op (m, U.unop)) → M.val.obj (op (n, U.unop)) :=
  fun x ↦ (((transition J B τ h).app M).val.app U) x

private theorem sourceTransition_apply (M : Systems.{c, v, max c v r} J B τ)
    {m n : ℕ} (h : n ≤ m) (U : Cᵒᵖ)
    (x : M.val.obj (op (m, U.unop))) :
    sourceSection.{c, v, r} J B τ M h U x =
      M.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x :=
  congrFun (eq_of_heq ((transition_exists J B τ h).exists.choose_spec M U)) x

attribute [local irreducible] sourceSection

/-- The identity horizontal map acts as the identity on sections.
Source: Zheng Construction 4.1; the section formula in SemilinearSystemModels.
(blueprint: def-coef-ordinary-source-strict-system). -/
theorem sourceStrict_identity (M : Systems.{c, v, max c v r} J B τ)
    (n : ℕ) (U : Cᵒᵖ) (x : M.val.obj (op (n, U.unop))) :
    @Eq (M.val.obj (op (n, U.unop)))
      (sourceSection.{c, v, r} J B τ M (Nat.le_refl n) U x) x := by
  have he : (Prod.mkHom (homOfLE (Nat.le_refl n)) (𝟙 U.unop)).op =
      𝟙 (op (n, U.unop)) := rfl
  have hi : M.val.map (Prod.mkHom (homOfLE (Nat.le_refl n)) (𝟙 U.unop)).op x = x := by
    rw [he, M.val.map_id]
    rfl
  exact (sourceTransition_apply.{c, v, r} J B τ M (Nat.le_refl n) U x).trans hi

/-- Horizontal maps compose as presheaf restrictions.
Source: Zheng Construction 4.1; the section formula in SemilinearSystemModels.
(blueprint: def-coef-ordinary-source-strict-system). -/
theorem sourceStrict_compose (M : Systems.{c, v, max c v r} J B τ)
    {l m n : ℕ} (h : l ≤ m) (k : m ≤ n)
    (U : Cᵒᵖ) (x : M.val.obj (op (n, U.unop))) :
    @Eq (M.val.obj (op (l, U.unop)))
      (sourceSection.{c, v, r} J B τ M (h.trans k) U x)
      (sourceSection.{c, v, r} J B τ M h U
        (sourceSection.{c, v, r} J B τ M k U x)) := by
  have he : (Prod.mkHom (homOfLE (h.trans k)) (𝟙 U.unop)).op =
      (Prod.mkHom (homOfLE k) (𝟙 U.unop)).op ≫
        (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op := by
    apply Quiver.Hom.unop_inj
    apply Prod.hom_ext
    · exact Subsingleton.elim _ _
    · simp
  exact (sourceTransition_apply.{c, v, r} J B τ M (h.trans k) U x).trans
    ((M.val.congr_map_apply he x).trans
      ((M.val.map_comp_apply (Prod.mkHom (homOfLE k) (𝟙 U.unop)).op
        (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x).trans
        ((congrArg (M.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op)
          (sourceTransition_apply.{c, v, r} J B τ M k U x).symm).trans
          (sourceTransition_apply.{c, v, r} J B τ M h U
            (show M.val.obj (op (m, U.unop)) from
              sourceSection.{c, v, r} J B τ M k U x)).symm)))

/-- The strict system with exactly the prescribed evaluations and transitions.
Source: Zheng Construction 4.1; the section formula in SemilinearSystemModels.
(blueprint: def-coef-ordinary-source-strict-system). -/
def sourceStrictObject (M : Systems.{c, v, max c v r} J B τ) :
    SheafOfModules.StrictRingSystem.{c, v, max c v r} (rings J B τ) where
  level n := (evaluation J B τ n).obj M
  transition h := (transition J B τ h).app M
  identity n U x := by
    have he := sourceStrict_identity.{c, v, r} J B τ M n U x
    unfold sourceSection at he
    exact he
  compose h k U x := by
    have he := sourceStrict_compose.{c, v, r} J B τ M h k U x
    unfold sourceSection at he
    exact he

/-- Extraction of strict systems using exactly the prescribed component functors.
Source: Zheng Construction 4.1; the section formula in SemilinearSystemModels.
(blueprint: def-coef-ordinary-source-strict-system). -/
def sourceStrictFunctor : Systems.{c, v, max c v r} J B τ ⥤
    SheafOfModules.StrictRingSystem.{c, v, max c v r} (rings J B τ) where
  obj := sourceStrictObject.{c, v, r} J B τ
  map f :=
    { app := fun n ↦ (evaluation J B τ n).map f
      comm := fun h ↦ (transition J B τ h).naturality f }
  map_id M := by
    apply SheafOfModules.strictRingSystem_hom_ext
    intro n
    exact (evaluation J B τ n).map_id M
  map_comp f g := by
    apply SheafOfModules.strictRingSystem_hom_ext
    intro n
    exact (evaluation J B τ n).map_comp f g

#print axioms sourceStrictFunctor

end WeilConjectures.SemilinearSections.OrdinarySource

end
