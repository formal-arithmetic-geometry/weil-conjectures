/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedFourierTransform
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.Compactification.BaseChange

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.DetPropSfCbc
import WeilConjectures.AlgebraicGeometry.CondensedCoefficientIsoBoundedConstructible
import WeilConjectures.AlgebraicGeometry.FourierKernelLisse
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleTensorObj
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleUpperStar
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarShift
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided

/-! # Stalks of the condensed Fourier--Deligne transform

Source: literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/
sec-fourier-transform/sec-fourier-inversion/sk-thm-inversion/lem-fd-stalk-formula.md,
node lem-fd-stalk-formula; geometric application
(blueprint: lem-fd-origin-noetherian-stalk).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
open AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale.CondensedRing

set_option maxHeartbeats 0 in
-- The derived tensor and coefficient comparisons elaborate large instance terms.
/-- The condensed stalk formula with explicit Noetherian hypotheses, including a base
which is an algebraic closure of the character field. All operations and the rank shift
are the same as in the existing stalk formula.

Source: latest blueprint lem-fd-stalk-at-origin.proof.md, first paragraph, specializing
lem-fd-stalk-formula after geometric base extension
(blueprint: lem-fd-origin-noetherian-stalk).
Proof: pullback of K is bounded constructible. The kernel is locally free and its
single complex can be tensored with this pullback inside the triangulated bounded
constructible subcategory. Apply condensed compact-support base change to that tensor
product. Derived pullback is monoidal and respects composition, which gives the displayed
two tensor factors. Finally commute the rank shift past pullback. The explicit Noetherian
hypotheses replace the inference of those properties from finite type over k₀. -/
theorem nonempty_iso_condensedFourierTransform_noetherianStalk
    (k₀ : Type u) [Field k₀] [Fintype k₀]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj.{u} E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj.{u} ℓ)))
    {S V Vdual : Scheme.{u}}
    {π : V ⟶ S} {πdual : Vdual ⟶ S}
    [LocallyOfFiniteType π] [QuasiCompact π] [IsSeparated π]
    [LocallyOfFiniteType πdual] [QuasiCompact πdual] [IsSeparated πdual]
    [IsNoetherian Vdual] [IsNoetherian (pullback π πdual)] (r : ℕ)
    (b : Γ(pullback π πdual, ⊤))
    [(pullback π πdual).Over (Spec (.of k₀))]
    (ψ : AddChar k₀ (MonObj.Γ Λ))
    (c : Compactification (pullback.snd π πdual)) [IsNoetherian c.Z]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1})
      (condensedRingObj Λ V)))
    (hK : boundedConstructible (condensedRingObj Λ V) K)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (ξ : Spec (.of Ω) ⟶ Vdual) :
    Nonempty (
      (moduleObjectDerivedPullback Λ ξ).obj
        ((condensedFourierTransform Λ k₀ π πdual ψ b c (r : ℤ)).obj K) ≅
      (shiftFunctor _ (r : ℤ)).obj
        ((rightDerivedLowerShriekOfCompactification Λ (c.baseChange ξ)).obj
          (((moduleObjectDerivedPullback Λ
              (pullback.fst (pullback.snd π πdual) ξ ≫
                pullback.fst π πdual)).obj K) ⊗
            (moduleObjectDerivedPullback Λ
              (pullback.fst (pullback.snd π πdual) ξ)).obj
              ((DerivedCategory.singleFunctor _ 0).obj
                (condensedFourierKernel Λ k₀ π πdual ψ b))))) := by
  let g' := pullback.fst (pullback.snd π πdual) ξ
  let A := (upperStar Λ (pullback.fst π πdual)).leftDerivedFunctor.obj K
  let B := (DerivedCategory.singleFunctor _ 0).obj
    (condensedFourierKernel Λ k₀ π πdual ψ b)
  let M := A ⊗ B
  have htri_of_iso
      {R T : Sheaf (Scheme.ProEt.topology (pullback π πdual)) Ab.{u + 1}}
      [MonObj R] [IsCommMonObj R] [MonObj T] [IsCommMonObj T]
      (φ : T ⟶ R) [IsMonHom φ] [IsIso φ]
      [(boundedConstructible T).IsTriangulated] :
      (boundedConstructible R).IsTriangulated := by
    have heq : boundedConstructible R =
        (boundedConstructible T).inverseImage (Mod.comap φ).mapDerivedCategory := by
      ext L
      exact (boundedConstructible_comap_iso_iff φ L).symm
    rw [heq]
    infer_instance
  have : (boundedConstructible (condensedRingObj Λ (pullback π πdual))).IsTriangulated := by
    rcases hΛ with hE | hQ
    · obtain ⟨i⟩ := hE
      have : IsIso i.inv.hom := inferInstanceAs (IsIso ((Mon.forget _).map i.inv))
      have : IsIso (coefficientMap i.inv.hom (pullback π πdual)) :=
        inferInstanceAs (IsIso ((upperStarFromPoint (pullback π πdual)).map i.inv.hom))
      let : (boundedConstructible (condensedRingObj
          (Profinite.continuousMapRingObj E) (pullback π πdual))).IsTriangulated :=
        isTriangulated_boundedConstructible_continuousMapRingObj (pullback π πdual) ℓ E
      exact htri_of_iso (coefficientMap i.inv.hom (pullback π πdual))
    · obtain ⟨i⟩ := hQ
      have : IsIso i.inv.hom := inferInstanceAs (IsIso ((Mon.forget _).map i.inv))
      have : IsIso (coefficientMap i.inv.hom (pullback π πdual)) :=
        inferInstanceAs (IsIso ((upperStarFromPoint (pullback π πdual)).map i.inv.hom))
      let : (boundedConstructible (condensedRingObj
          (Profinite.padicAlgClRingObj ℓ) (pullback π πdual))).IsTriangulated :=
        isTriangulated_boundedConstructible_padicAlgClRingObj (pullback π πdual) ℓ
      exact htri_of_iso (coefficientMap i.inv.hom (pullback π πdual))
  have hunit (n : ℕ) (hn : n ≠ 0) : IsUnit (n : MonObj.Γ Λ) := by
    rcases hΛ with hE | hQ
    · obtain ⟨i⟩ := hE
      let : CharZero E := (algebraMap E (PadicAlgCl ℓ)).charZero
      let a := (MonObj.Γ.map i.inv.hom).comp (Profinite.continuousMapConstRingHom E)
      simpa only [map_natCast] using
        (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hn) : IsUnit (n : E)).map a
    · obtain ⟨i⟩ := hQ
      let a := (MonObj.Γ.map i.inv.hom).comp (Profinite.PadicAlgCl.constRingHom ℓ)
      simpa only [map_natCast] using
        (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hn) :
          IsUnit (n : PadicAlgCl ℓ)).map a
  have hadm : IsAdmissibleCoefficient Λ := by
    refine ⟨ℓ, inferInstance, Or.inr (Or.inr (Or.inr (Or.inr ?_)))⟩
    exact hΛ.imp (fun i ↦ ⟨E, i⟩) id
  have hLF : IsLocallyFree (condensedRingObj Λ (pullback π πdual))
      (condensedFourierKernel Λ k₀ π πdual ψ b) :=
    (isLocallyFree_iff _).2
      ((Etale.prop_kernel_lisse.2.2.2 Λ k₀ (hunit _ Fintype.card_ne_zero) hadm
        (pullback π πdual) ψ ψ b).1)
  have hA : boundedConstructible (condensedRingObj Λ (pullback π πdual)) A :=
    boundedConstructible_leftDerivedUpperStar_obj_of_scheme Λ _ K hK
  let : BraidedCategory (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology (pullback π πdual)) Ab.{u + 1})
        (condensedRingObj Λ (pullback π πdual)))) := DerivedCategory.braidedCategory' _
  have hM : boundedConstructible (condensedRingObj Λ (pullback π πdual)) M :=
    (boundedConstructible (condensedRingObj Λ (pullback π πdual))).prop_of_iso (β_ B A)
      (boundedConstructible_singleFunctor_tensorObj_of_isLocallyFree hLF hA)
  have hcoeff :
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E))) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)) :=
    hΛ.elim (fun h ↦ Or.inr (Or.inl ⟨E, h⟩)) (fun h ↦ Or.inr (Or.inr h))
  have hbc := (condensed_compactSupportBaseChange ℓ Λ hcoeff
    (pullback.snd π πdual) ξ c M hM).2.2
  let eBC := asIso ((detSfCompactSupportBaseChangeComposite Λ (pullback.snd π πdual) ξ c
    (compactSupportOpenBaseChangeIso Λ (pullback.snd π πdual) ξ c)).app M)
  let eFirst : (upperStar Λ g').leftDerivedFunctor.obj A ≅
      (upperStar Λ (g' ≫ pullback.fst π πdual)).leftDerivedFunctor.obj K :=
    (leftDerivedUpperStarComp Λ g' (pullback.fst π πdual)).symm.app K
  let eIntegrand := ((leftDerivedUpperStarTensorIso Λ g').app A).app B ≪≫
    tensorIso eFirst (Iso.refl ((upperStar Λ g').leftDerivedFunctor.obj B))
  refine ⟨((upperStar Λ ξ).leftDerivedFunctor.commShiftIso (r : ℤ)).app
      ((rightDerivedLowerShriekOfCompactification Λ c).obj M) ≪≫
    (shiftFunctor _ (r : ℤ)).mapIso (eBC ≪≫
      (rightDerivedLowerShriekOfCompactification Λ (c.baseChange ξ)).mapIso eIntegrand)⟩

end AlgebraicGeometry.ProEtale.CondensedRing
