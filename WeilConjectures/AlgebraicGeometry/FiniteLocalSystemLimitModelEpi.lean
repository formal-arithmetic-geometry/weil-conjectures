/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleMilnorSequence
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.AlgebraicGeometry.IntegralOperationsWellDefinedSupplement
public import WeilConjectures.AlgebraicGeometry.MilnorTower
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtaleProductsExact
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtaleSectionsLimitsColimits
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Sites.Sheaf
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimitSupplement
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator
public import WeilConjectures.AlgebraicGeometry.ProEtale.SectionsConservative
public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import WeilConjectures.AlgebraicGeometry.WContractibleAffineCover
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.RingTheory.ProEtale.WContractible
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import WeilConjectures.RingTheory.IndPrincipalZariski
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import WeilConjectures.AlgebraicGeometry.RoosCohomologySequence
public import WeilConjectures.AlgebraicGeometry.RoosCohomologyMaps
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
public import WeilConjectures.AlgebraicGeometry.RoosCohomologyNaturality
public import Mathlib.Algebra.Homology.SingleHomology
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.AlgebraicGeometry.CompletedConstantRealizationDataSupplement
public import WeilConjectures.AlgebraicGeometry.CompletedConstantSheafReductionSupplement
public import WeilConjectures.CategoryTheory.ConstantRingModuleSheaves
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.CategoryTheory.Sites.WeaklyContractibleMittagLeffler

/-! # A strict subargument of the finite local system limit model

The expanded scalar functors keep this proof module independent of the parent
module's convenience definitions. (blueprint: lem-zl-finite-local-system-limit-model-epi) -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.FiniteLocalSystemLimit
open Scheme

private noncomputable def restrictionIsoRoundTrip
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (e : R ≅ S) :
    SheafOfModules.restrictScalars.{u + 1} e.inv ⋙
      SheafOfModules.restrictScalars.{u + 1} e.hom ≅ 𝟭 _ :=
  NatIso.ofComponents (fun M ↦ {
    hom := { val := {
      app := fun U ↦ ModuleCat.ofHom
        (X := ((SheafOfModules.restrictScalars e.hom).obj
          ((SheafOfModules.restrictScalars e.inv).obj M)).val.obj U)
        (Y := M.val.obj U) {
        toFun := fun x ↦ x
        map_add' := fun _ _ ↦ rfl
        map_smul' := by
          intro a x
          change M.val.obj U at x
          change e.inv.hom.app U (e.hom.hom.app U a) • x = a • x
          have h := ConcreteCategory.congr_hom
            (congrArg (fun f ↦ f.hom.app U) e.hom_inv_id) a
          change e.inv.hom.app U (e.hom.hom.app U a) = a at h
          rw [h] }
      naturality := by intros; ext; rfl } }
    inv := { val := {
      app := fun U ↦ ModuleCat.ofHom
        (X := M.val.obj U)
        (Y := ((SheafOfModules.restrictScalars e.hom).obj
          ((SheafOfModules.restrictScalars e.inv).obj M)).val.obj U) {
        toFun := fun x ↦ x
        map_add' := fun _ _ ↦ rfl
        map_smul' := by
          intro a x
          change M.val.obj U at x
          change a • x = e.inv.hom.app U (e.hom.hom.app U a) • x
          have h := ConcreteCategory.congr_hom
            (congrArg (fun f ↦ f.hom.app U) e.hom_inv_id) a
          change e.inv.hom.app U (e.hom.hom.app U a) = a at h
          rw [h] }
      naturality := by intros; ext; rfl } }
    hom_inv_id := by ext; rfl
    inv_hom_id := by ext; rfl })

private theorem restrictionIsoIsEquivalence
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (e : R ≅ S) :
    (SheafOfModules.restrictScalars.{u + 1} e.hom).IsEquivalence := by
  let E : SheafOfModules.{u + 1} S ≌ SheafOfModules.{u + 1} R :=
    CategoryTheory.Equivalence.mk (SheafOfModules.restrictScalars e.hom)
      (SheafOfModules.restrictScalars e.inv)
      (restrictionIsoRoundTrip e.symm).symm (restrictionIsoRoundTrip e)
  exact E.isEquivalence_functor

private theorem restrictionFaithful
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (p : R ⟶ S) :
    (SheafOfModules.restrictScalars.{u + 1} p).Faithful where
  map_injective {M N} f g h := by
    ext U x
    exact congrArg (fun k ↦ k.val.app U x) h

/-- A Mittag-Leffler tower after scalar restriction has epic ringed Roos differential.
Source: blueprint latest, prop-zl-smooth-proper-relative-purity.proof.md, Step 1,
Passage to the limit (blueprint: lem-zl-finite-local-system-limit-model-epi).

Proof: use the weakly contractible affine basis of the pro-etale site. Evaluation
on such an object preserves epimorphisms, so sections of an image sheaf are the
image of sections. The image-subobject Mittag-Leffler hypothesis therefore makes
the section tower Mittag-Leffler. The module Mittag-Leffler criterion makes one
minus shift surjective on these sections and therefore epic as a fixed-scalar
sheaf map. Restriction of scalars is faithful and preserves products, and retains
the underlying additive maps. The product comparison identifies this sheaf map
with restriction of the ringed-module Roos differential. Faithfulness reflects
epimorphisms, giving the displayed conclusion. No finiteness, torsion bound,
connectedness or normalization hypothesis is needed for this transport step. -/
theorem finite_local_system_limit_model_epi
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (Y : Scheme.{u})
    (M : ℕᵒᵖ ⥤ Scheme.proEtaleRingModules Y (Scheme.adicLisseCompletedRing Y (Ideal.span
    {ULift.up (Padic.coefficientExtensionUniformizer l E)} : Ideal (ULift.{u + 1}
    (Padic.coefficientExtensionIntegers l E)))))
    (hML : ∀ n : ℕ, ∃ N : ℕ, ∃ hN : n ≤ N, ∀ (k : ℕ) (hk : n ≤ k),
      imageSubobject ((M ⋙ (SheafOfModules.restrictScalars ((Scheme.adicLisseForget Y).map
    (Scheme.CompletedConstantReduction.base Y (Ideal.span {ULift.up
    (Padic.coefficientExtensionUniformizer l E)} : Ideal (ULift.{u + 1}
    (Padic.coefficientExtensionIntegers l E))))) ⋙ SheafOfModules.restrictScalars
    ((constantCommuteCompose (Scheme.ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u +
    1})).app (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))).inv ⋙
    constantRingModuleRestriction (Scheme.ProEt.topology Y) (ULift.{u + 1}
    (Padic.coefficientExtensionIntegers l E)))).map (homOfLE hN).op) ≤
        imageSubobject ((M ⋙ (SheafOfModules.restrictScalars ((Scheme.adicLisseForget Y).map
    (Scheme.CompletedConstantReduction.base Y (Ideal.span {ULift.up
    (Padic.coefficientExtensionUniformizer l E)} : Ideal (ULift.{u + 1}
    (Padic.coefficientExtensionIntegers l E))))) ⋙ SheafOfModules.restrictScalars
    ((constantCommuteCompose (Scheme.ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u +
    1})).app (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))).inv ⋙
    constantRingModuleRestriction (Scheme.ProEt.topology Y) (ULift.{u + 1}
    (Padic.coefficientExtensionIntegers l E)))).map (homOfLE hk).op)) :
    Epi (towerTransitionEndomorphism (K := fun n : ℕ ↦ M.obj (op n))
      (fun n ↦ M.map (homOfLE (Nat.le_succ n)).op)) := by
  let G := (SheafOfModules.restrictScalars ((Scheme.adicLisseForget Y).map
    (Scheme.CompletedConstantReduction.base Y (Ideal.span {ULift.up
    (Padic.coefficientExtensionUniformizer l E)} : Ideal (ULift.{u + 1}
    (Padic.coefficientExtensionIntegers l E))))) ⋙ SheafOfModules.restrictScalars
    ((constantCommuteCompose (Scheme.ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))).inv ⋙
    constantRingModuleRestriction (Scheme.ProEt.topology Y)
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))
  let F := M ⋙ G
  let K : ℕ → Scheme.proEtaleRingModules Y
      (Scheme.adicLisseCompletedRing Y (Ideal.span {ULift.up
      (Padic.coefficientExtensionUniformizer l E)} : Ideal (ULift.{u + 1}
      (Padic.coefficientExtensionIntegers l E)))) := fun n ↦ M.obj (op n)
  let t₀ := towerTransitionEndomorphism (K := K)
    (fun n ↦ M.map (homOfLE (Nat.le_succ n)).op)
  let s₀ := towerProductShift (K := K)
    (fun n ↦ M.map (homOfLE (Nat.le_succ n)).op)
  let hP₀ := productIsProduct K
  letI : HasSheafify (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, u} Y
  letI : (Scheme.ProEt.topology Y).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, u} Y
  let A₁ := SheafOfModules.restrictScalars ((Scheme.adicLisseForget Y).map
    (Scheme.CompletedConstantReduction.base Y (Ideal.span {ULift.up
    (Padic.coefficientExtensionUniformizer l E)} : Ideal (ULift.{u + 1}
    (Padic.coefficientExtensionIntegers l E)))))
  let A₂ := SheafOfModules.restrictScalars
    ((constantCommuteCompose (Scheme.ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))).inv
  let C₃ := constantRingModuleRestriction (Scheme.ProEt.topology Y)
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))
  letI : PreservesLimitsOfShape (Discrete ℕ) A₁ := by
    let S₁ : Sheaf (Scheme.ProEt.topology Y) RingCat.{u + 1} := (Scheme.adicLisseForget Y).obj
      (Scheme.adicLisseCompletedRing Y (Ideal.span {ULift.up
        (Padic.coefficientExtensionUniformizer l E)} : Ideal (ULift.{u + 1}
        (Padic.coefficientExtensionIntegers l E))))
    let R₁ : Sheaf (Scheme.ProEt.topology Y) RingCat.{u + 1} := (Scheme.adicLisseForget Y).obj
      (Scheme.adicLisseConstantRing Y (ULift.{u + 1}
        (Padic.coefficientExtensionIntegers l E)))
    let H := SheafOfModules.toSheaf R₁
    letI : PreservesLimitsOfSize (SheafOfModules.toSheaf S₁) := by
      constructor
      intro K _
      exact ((moduleSheaves_colimits_forgetful S₁).2.2.2.2.2 K).1
    letI : PreservesLimitsOfSize H := by
      constructor
      intro K _
      exact ((moduleSheaves_colimits_forgetful R₁).2.2.2.2.2 K).1
    letI : ReflectsLimitsOfSize H := reflectsLimits_of_reflectsIsomorphisms
    letI : PreservesLimitsOfSize (A₁ ⋙ H) :=
      inferInstanceAs (PreservesLimitsOfSize (SheafOfModules.toSheaf S₁))
    letI : PreservesLimitsOfSize A₁ :=
      preservesLimits_of_reflects_of_preserves A₁ H
    letI : PreservesLimitsOfSize.{0, 0} A₁ :=
      preservesSmallestLimits_of_preservesLimits A₁
    exact (inferInstance : PreservesLimitsOfSize.{0, 0} A₁).preservesLimitsOfShape
  letI : A₂.IsEquivalence := by
    let e := (constantCommuteCompose (Scheme.ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app
      (CommRingCat.of (ULift.{u + 1}
        (Padic.coefficientExtensionIntegers l E)))
    dsimp [A₂]
    exact restrictionIsoIsEquivalence e.symm
  letI : PreservesLimitsOfShape (Discrete ℕ) A₂ := by
    letI : PreservesLimitsOfSize.{0, 0} A₂ :=
      preservesSmallestLimits_of_preservesLimits A₂
    exact (inferInstance : PreservesLimitsOfSize.{0, 0} A₂).preservesLimitsOfShape
  have hC₃ : C₃.IsEquivalence := by
    obtain ⟨e, he, _, _, _⟩ :=
      (constant_ring_module_sheaves (Scheme.ProEt.topology Y)
        (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))).1
    change (constantRingModuleRestriction (Scheme.ProEt.topology Y)
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))).IsEquivalence
    exact he ▸ e.isEquivalence_functor
  letI : C₃.IsEquivalence := hC₃
  letI : A₁.Faithful := restrictionFaithful _
  letI : G.Faithful := by
    change (A₁ ⋙ A₂ ⋙ C₃).Faithful
    infer_instance
  letI : C₃.Additive := by
    dsimp [C₃]
    exact { map_add := by intros; ext X x; rfl }
  letI : G.Additive := by
    change (A₁ ⋙ A₂ ⋙ C₃).Additive
    infer_instance
  letI : PreservesLimitsOfShape (Discrete ℕ) C₃ := by
    infer_instance
  letI : PreservesLimitsOfShape (Discrete ℕ) G := by
    change PreservesLimitsOfShape (Discrete ℕ) (A₁ ⋙ A₂ ⋙ C₃)
    infer_instance
  let hP := isLimitFanMkObjOfIsLimit G K (Pi.π K) hP₀
  let s := G.map s₀
  have ht (n : ℕ) : s ≫ G.map (Pi.π K n) =
      G.map (Pi.π K (n + 1)) ≫ F.map (homOfLE (Nat.le_succ n)).op := by
    dsimp [s]
    rw [← G.map_comp]
    simp [s₀, towerProductShift]
    rfl
  have hML' : ∀ n : ℕ, ∃ N : ℕ, ∃ hN : n ≤ N, ∀ (k : ℕ) (hk : n ≤ k),
      imageSubobject (F.map (homOfLE hN).op) ≤
        imageSubobject (F.map (homOfLE hk).op) := by
    intro n
    obtain ⟨N, hN, h⟩ := hML n
    exact ⟨N, hN, fun k hk ↦ h k hk⟩
  -- Elaborated without an expected type: unifying `𝟙 Pf.pt - t` before `hP` fixes `Pf` is slow.
  have hepi :=
    GrothendieckTopology.epi_one_sub_of_mittagLeffler_imageSubobject
      (fun W : Y.ProEt ↦ IsAffine W.left ∧
        (Scheme.ProEt.topology Y).IsWeaklyContractible W)
      (fun V ↦ Scheme.ProEt.exists_isWeaklyContractible_cover V)
      (fun _ hW ↦ hW.2) hP s ht hML'
  have hepi' : Epi (G.map t₀) := by
    change Epi (G.map (𝟙 _ - s₀))
    rw [Functor.map_sub]
    change Epi (𝟙 _ - s)
    exact hepi
  exact (Functor.reflectsEpimorphisms_of_faithful G).reflects _ hepi'

end AlgebraicGeometry.ProEtale.FiniteLocalSystemLimit
