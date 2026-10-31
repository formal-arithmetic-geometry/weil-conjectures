/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerTraceModels
import all WeilConjectures.AlgebraicGeometry.ProEtaleMilnorEpimorphic
import all WeilConjectures.AlgebraicGeometry.ProEtaleMilnorSequence
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.AlgebraicGeometry.MilnorTower
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.AlgebraicGeometry.ProEtaleProductsExact
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all WeilConjectures.AlgebraicGeometry.ProEtaleSectionsLimitsColimits
import all WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.AlgebraicGeometry.AffineScheme
import all Mathlib.CategoryTheory.Sites.Sheaf
import all WeilConjectures.CategoryTheory.Sites.WeaklyContractible
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import all WeilConjectures.CategoryTheory.SiteCoveringAxioms
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import all WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import all Mathlib.CategoryTheory.Yoneda
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.CategoryTheory.Generator.Basic
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import all WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import all Mathlib.LinearAlgebra.Finsupp.LinearCombination
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator
import all WeilConjectures.AlgebraicGeometry.ProEtale.SectionsConservative
import all WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import all WeilConjectures.AlgebraicGeometry.WContractibleAffineCover
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all WeilConjectures.RingTheory.ProEtale.WContractible
import all Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import all Mathlib.RingTheory.RingHom.FaithfullyFlat
import all WeilConjectures.RingTheory.ProperBaseChange.IndPrincipalZariski
import all WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all Mathlib.Algebra.Category.ModuleCat.AB
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all WeilConjectures.AlgebraicGeometry.RoosCohomologySequence
import all WeilConjectures.AlgebraicGeometry.RoosCohomologyMaps
import all Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import all WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
import all WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import all WeilConjectures.AlgebraicGeometry.RoosCohomologyNaturality
import all Mathlib.Algebra.Homology.SingleHomology
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSurjectiveTowerDerivedLimitSupplement
import all Mathlib.Algebra.Category.ModuleCat.Products
import all WeilConjectures.Algebra.Homology.KernelShiftedMappingCone
import all WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import all WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import all WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import all Mathlib.Algebra.Homology.HomologicalComplexLimits
import all Mathlib.Algebra.Homology.DerivedCategory.KInjective
import all WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import all WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import all Mathlib.CategoryTheory.Adjunction.Evaluation
import all Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import all Mathlib.Algebra.BigOperators.Ring.Finset
import WeilConjectures.CategoryTheory.ExactProductsRoos.ExactProductsRoosComparisonSupplement

/-! # Epimorphic towers and the normalized derived-limit unit -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u a b c v w g va vb vc wa wb wc
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

open SpTowerClasses

private theorem towerDifference_epi (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (H : ℕᵒᵖ ⥤ DiagonalMod l T)
    (ht : ∀ n : ℕ, Epi (H.map (homOfLE (Nat.le_succ n)).op)) :
    Epi (towerTransitionEndomorphism (K := fun n : ℕ ↦ H.obj (op n))
      (fun n : ℕ ↦ H.map (homOfLE (Nat.le_succ n)).op)) := by
  obtain ⟨e, _, _, hi, _⟩ :=
    (constant_ring_module_sheaves (Scheme.ProEt.topology T) (ULift.{u + 1} ℤ_[l])).1
  let E := e.inverse
  have : E.Additive := hi
  have h (n : ℕ) : Epi ((H ⋙ E).map (homOfLE (Nat.le_succ n)).op) := by
    have := ht n
    exact E.map_epi _
  have : Epi (towerTransitionEndomorphism
      (K := fun n : ℕ ↦ E.obj (H.obj (op n)))
      (fun n : ℕ ↦ E.map (H.map (homOfLE (Nat.le_succ n)).op))) :=
    AlgebraicGeometry.ProEtale.sheaf_tower_epi.{0, u} T _ (H ⋙ E) h
  apply E.epi_of_epi_map
  apply (epi_comp_iff_of_isIso _ (piComparison E (fun n : ℕ ↦ H.obj (op n)))).mp
  rw [AlgebraicGeometry.ProEtale.map_transition]
  exact inferInstance

private theorem towerProducts_exact (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    HasExactLimitsOfShape (Discrete ℕ) (DiagonalMod l T) := by
  obtain ⟨e, _, _, _, _⟩ :=
    (constant_ring_module_sheaves (Scheme.ProEt.topology T) (ULift.{u + 1} ℤ_[l])).1
  have : HasExactLimitsOfShape (Discrete ℕ) (SheafOfModules.{u + 1}
      ((constantSheaf (Scheme.ProEt.topology T) RingCat.{u + 1}).obj
        (RingCat.of (ULift.{u + 1} ℤ_[l])))) :=
    Scheme.ProEt.products_exact.{u, 0, 0} T _ ℕ
  exact HasExactLimitsOfShape.of_codomain_equivalence (Discrete ℕ) e

private theorem derivedUnit_isIso
    {A : Type a} [Category.{v} A] [Abelian A] [HasCountableProducts A]
    [HasLimitsOfShape ℕᵒᵖ A] [HasExactLimitsOfShape (Discrete ℕ) A]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
    [IsGrothendieckAbelian.{g} (ℕᵒᵖ ⥤ A)]
    (L : DiagonalRlim A) (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (ht : ∀ p : ℤ, Epi (towerTransitionEndomorphism
      (K := fun n : ℕ ↦ (I.X p).obj (op n))
      (fun n : ℕ ↦ (I.X p).map (homOfLE (Nat.le_succ n)).op))) :
    IsIso (L.η.app I) := by
  let c : Cone I.asFunctor :=
    { pt := ExactProductsRoos.ordinary.obj I
      π := { app := fun n ↦ (NatTrans.mapHomologicalComplex
                (lim.π n) (.up ℤ)).app I
             naturality := by
               intro n m f
               ext p : 1
               change 𝟙 _ ≫ limit.π (I.X p) m =
                 limit.π (I.X p) n ≫ (I.X p).map f
               rw [Category.id_comp]
               exact (limit.w _ _).symm } }
  have hc : IsLimit c := by
    apply HomologicalComplex.isLimitOfEval
    intro p
    exact limit.isLimit (I.X p)
  let K := fun n : ℕ ↦ I.asFunctor.obj (op n)
  let P : Fan K := limit.cone (Discrete.functor K)
  let i := ExactProductsRoos.inclusion.app I
  let t := ExactProductsRoos.difference.app I
  obtain ⟨hz, ⟨hk⟩⟩ := AlgebraicGeometry.ProEtale.tower_kernel I.asFunctor c hc P
    (limit.isLimit _) i t (fun n ↦ Pi.lift_π _ n)
    (fun n ↦ (towerTransitionEndomorphism_eq_iff _ _).1 rfl n)
  have hte : Epi t := by
    apply HomologicalComplex.epi_of_epi_f
    intro p
    let ev := HomologicalComplex.eval A (.up ℤ) p
    have : Epi (towerTransitionEndomorphism
        (K := fun n : ℕ ↦ ev.obj (K n))
        (fun n : ℕ ↦ ev.map (I.asFunctor.map (homOfLE (Nat.le_succ n)).op))) := ht p
    change Epi (ev.map t)
    apply (epi_comp_iff_of_isIso _ (piComparison ev K)).mp
    change Epi (ev.map (towerTransitionEndomorphism
      (fun n : ℕ ↦ I.asFunctor.map (homOfLE (Nat.le_succ n)).op)) ≫ piComparison ev K)
    rw [AlgebraicGeometry.ProEtale.map_transition]
    exact inferInstance
  let S := ShortComplex.mk i t hz
  have : Mono S.f := mono_of_isLimit_fork hk
  have hS : S.ShortExact := { exact := S.exact_of_f_is_kernel hk }
  let S' := ShortComplex.mk i (-t) (by rw [Preadditive.comp_neg, hz, neg_zero])
  have hS' : S'.ShortExact := by
    apply ShortComplex.shortExact_of_iso (S₁ := S) _ hS
    exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
      { hom := -𝟙 _
        inv := -𝟙 _
        hom_inv_id := by simp
        inv_hom_id := by simp } (by simp [S, S']) (by simp [S, S'])
  have hq : QuasiIso (ExactProductsRoos.comparison.app I) :=
    AlgebraicGeometry.ProEtale.cocone_lift_quasiIso S' hS'
      (ExactProductsRoos.comparison_condition I)
  have : IsIso (DerivedCategory.Q.map (ExactProductsRoos.comparison.app I)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso A _).2 hq
  obtain ⟨e, he⟩ := ExactProductsRoos.comparisonIso L.R L.η L.computation
  have heI := NatTrans.congr_app he I
  change DerivedCategory.Q.map (ExactProductsRoos.comparison.app I) ≫ e.hom.app I =
    L.η.app I at heI
  rw [← heI]
  infer_instance

/-- Epimorphic strict towers have invertible ordinary-to-derived limit comparison.

Source: the Milnor passage to the limit in the diagonal trace proof, paragraph (1).
(blueprint: new-sfb-diagonal-trace-ordinary-rlim-epi).

Proof: transfer the Milnor difference-map epimorphism and exact countable products
from modules over the constant ring sheaf. For the single complex of the tower,
the ordinary limit is the kernel of its degreewise epic difference map. The
zero-second-coordinate map into the Roos fibre is therefore a quasi-isomorphism.
The normalized Roos comparison identifies its localization with the given derived
unit, so every factor of the ordinary-to-derived comparison is invertible.
-/
theorem diagonalOrdinaryRlim_isIso_of_epi (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    [DiagonalTraceLocalizations l T] (L : DiagonalRlim (DiagonalMod l T))
    (H : DiagonalSystems l T)
    (ht : ∀ n : ℕ, Epi (H.map (homOfLE (Nat.le_succ n)).op)) :
    IsIso (diagonalOrdinaryRlim L H) := by
  let I := (HomologicalComplex.single (DiagonalSystems l T) (.up ℤ) 0).obj H
  have hI (p : ℤ) (n : ℕ) : Epi ((I.X p).map (homOfLE (Nat.le_succ n)).op) := by
    by_cases hp : p = 0
    · subst p
      let e : I.X 0 ≅ H := HomologicalComplex.singleObjXSelf (.up ℤ) 0 H
      have := ht n
      have he := e.hom.naturality (homOfLE (Nat.le_succ n)).op
      have : Epi ((I.X 0).map (homOfLE (Nat.le_succ n)).op ≫ e.hom.app (op n)) := by
        rw [he]
        infer_instance
      exact (epi_comp_iff_of_isIso _ (e.hom.app (op n))).mp this
    · have hz : IsZero (I.X p) := HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 H p hp
      exact ((Functor.isZero_iff _).mp hz (op n)).epi _
  have := towerProducts_exact l T
  have : IsGrothendieckAbelian.{u + 1} (DiagonalSystems l T) :=
    CategoryTheory.tower_grothendieck (DiagonalMod l T)
  have := derivedUnit_isIso L I (fun p ↦ towerDifference_epi l T (I.X p) (hI p))
  unfold diagonalOrdinaryRlim
  infer_instance

attribute [local irreducible] diagonalOrdinaryRlim exactConeComparison

private theorem exactConeComparison_isIso
    {A : Type a} {B : Type b} {C : Type c}
    [Category.{va} A] [Category.{vb} B] [Category.{vc} C]
    [Abelian A] [Abelian B] [Abelian C] [HasLimitsOfShape ℕᵒᵖ B]
    [HasDerivedCategory.{wa} A] [HasDerivedCategory.{wb} B]
    [HasDerivedCategory.{wb} (ℕᵒᵖ ⥤ B)] [HasDerivedCategory.{wc} C]
    (U : A ⥤ B) (V : C ⥤ (ℕᵒᵖ ⥤ B))
    [U.Additive] [V.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (L : DiagonalRlim B) (M : A) (N : C)
    (π : (Functor.const ℕᵒᵖ).obj (U.obj M) ⟶ V.obj N)
    (hc : IsIso (limit.lift (V.obj N) ⟨U.obj M, π⟩))
    (hl : IsIso (diagonalOrdinaryRlim L (V.obj N))) :
    IsIso (exactConeComparison U V L M N π) := by
  unfold exactConeComparison
  infer_instance

end AlgebraicGeometry.ProEtale.DiagonalTrace
