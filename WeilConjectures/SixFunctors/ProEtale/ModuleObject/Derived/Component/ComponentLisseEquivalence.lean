/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedLisseEvaluationModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ZetaWeil.ContractibleLisseEvaluation
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.RingDerivedScalarExtension.RingIsoPerfectScalarEquivalence

/-! # The lisse equivalence induced by component pullback -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

open SheafOfModules in
private theorem affine_evaluation (T : Scheme.{u}) [IsAffine T]
    [IsWContractibleRing Γ(T, ⊤)]
    (O : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) [MonObj O] [IsCommMonObj O] :
    Evaluation.Statement (Scheme.ProEt.topology T) O (Scheme.ProEt.mk (𝟙 T))
      (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.WeaklyEtale T) := by
  let J := Scheme.ProEt.topology T
  let := (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u, 0}
    J (Evaluation.ringSheaf J O)).1
  let : HasDerivedCategory.{u + 1} (SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (Evaluation.ringSheaf J O))) := HasDerivedCategory.ofIsGrothendieckAbelian _
  exact contractible_lisse_evaluation J O _ _
    (AlgebraicGeometry.contractible_derived_sections_tensor.{0, u}.1 T _)

open SheafOfModules in
private theorem profinite_evaluation (S : Profinite.{u}) [ExtremallyDisconnected S]
    (O : Sheaf ((coherentTopology Profinite.{u}).over S) Ab.{u + 1})
    [MonObj O] [IsCommMonObj O] :
    Evaluation.Statement ((coherentTopology Profinite.{u}).over S) O
      (Over.mk (𝟙 S)) Over.mkIdTerminal := by
  let J := (coherentTopology Profinite.{u}).over S
  let := (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u, 0}
    J (Evaluation.ringSheaf J O)).1
  let : HasDerivedCategory.{u + 1} (SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (Evaluation.ringSheaf J O))) := HasDerivedCategory.ofIsGrothendieckAbelian _
  exact contractible_lisse_evaluation J O _ _
    (AlgebraicGeometry.contractible_derived_sections_tensor.{0, u}.2 S _)

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (T : Scheme.{u}) [IsAffine T] [IsWContractibleRing Γ(T, ⊤)]
  [(componentTests T).IsContinuous
    ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
    (Scheme.ProEt.topology T)]
  [(componentInverse T).Braided]
  [PreservesFiniteLimits (componentInverse T)]
  [PreservesFiniteColimits (componentInverse T)]
  (α : (componentInverse T).mapMon.obj
      (Mon.mk (profiniteCoefficient Λ (affineComponentSpace T))) ≅
      Mon.mk (condensedRingObj Λ T))

/-- The component derived functor identifies the two lisse full subcategories.
Source: Hemo--Richarz--Scholbach, Proposition 4.3(3)
(blueprint: lem-zl-component-lisse-equivalence).

Proof: contractible evaluation identifies lisse objects with perfect complexes over the
respective section rings. The section-ring comparison and its derived realization square
transport perfect complexes across the coefficient isomorphism. Scalar transport is an
equivalence on modules because the coefficient map is an isomorphism, and it preserves
bounded finite-projective representatives termwise. Restrict the resulting derived
equivalence to the full perfect subcategories and conjugate it by the two evaluation
equivalences. The displayed inclusion comparison is the composite of these canonical
comparison isomorphisms. -/
theorem component_lisse_equivalence
    (a : Evaluation.A ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
      (profiniteCoefficient Λ (affineComponentSpace T)) (Over.mk (𝟙 (affineComponentSpace T))) ≅
      Evaluation.A (Scheme.ProEt.topology T) (condensedRingObj Λ T)
        (Scheme.ProEt.mk (𝟙 T)))
    (square : Nonempty (Evaluation.F
        ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
        (profiniteCoefficient Λ (affineComponentSpace T)) (Over.mk (𝟙 (affineComponentSpace T)))
        Over.mkIdTerminal ⋙ componentDerived Λ T α ≅
      RingDerivedScalarExtension.moduleDerivedExtension a.hom.hom ⋙
        Evaluation.F (Scheme.ProEt.topology T) (condensedRingObj Λ T)
          (Scheme.ProEt.mk (𝟙 T))
          (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.WeaklyEtale T))) :
    ∃ e : (Evaluation.lisse ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
        (profiniteCoefficient Λ (affineComponentSpace T))).FullSubcategory ≌
      (Evaluation.lisse (Scheme.ProEt.topology T) (condensedRingObj Λ T)).FullSubcategory,
      Nonempty (e.functor ⋙ (Evaluation.lisse (Scheme.ProEt.topology T)
          (condensedRingObj Λ T)).ι ≅
        (Evaluation.lisse ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
          (profiniteCoefficient Λ (affineComponentSpace T))).ι ⋙ componentDerived Λ T α) := by
  let eh : T ≃ₜ PrimeSpectrum Γ(T, ⊤) :=
    TopCat.homeoOfIso (Scheme.forgetToTop.mapIso T.isoSpec)
  let ec : ConnectedComponents T ≃ₜ ConnectedComponents (PrimeSpectrum Γ(T, ⊤)) :=
    eh.isQuotientMap.isCoinducing.connectedComponentsHomeomorph (fun y ↦ by
      rw [show eh ⁻¹' {y} = {eh.symm y} by
        ext x
        exact (Equiv.eq_symm_apply eh.toEquiv).symm]
      exact isConnected_singleton)
  let : ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum Γ(T, ⊤))) :=
    IsWContractibleRing.extremallyDisconnected_connectedComponents
  let : ExtremallyDisconnected (affineComponentSpace T) :=
    extremallyDisconnected_of_homeo ec.symm
  obtain ⟨_, _, _, eS, ⟨iS⟩, _⟩ :=
    profinite_evaluation (affineComponentSpace T) (profiniteCoefficient Λ (affineComponentSpace T))
  obtain ⟨_, _, _, eT, ⟨iT⟩, _⟩ := affine_evaluation T (condensedRingObj Λ T)
  obtain ⟨er, ⟨ir⟩⟩ := RingDerivedScalarExtension.ring_iso_perfect_scalar_equivalence _ _ a
  obtain ⟨square⟩ := square
  refine ⟨eS.symm.trans (er.trans eT), ⟨?_⟩⟩
  exact Functor.isoWhiskerLeft eS.inverse (Functor.isoWhiskerLeft er.functor iT) ≪≫
    Functor.isoWhiskerLeft eS.inverse
      ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight ir _ ≪≫
        Functor.associator _ _ _) ≪≫
    Functor.isoWhiskerLeft eS.inverse (Functor.isoWhiskerLeft _ square.symm) ≪≫
    Functor.isoWhiskerLeft eS.inverse
      ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight iS.symm _ ≪≫
        Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight eS.counitIso _ ≪≫ Functor.leftUnitor _

end AlgebraicGeometry.ProEtale.CondensedRing
