/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.RegularRoosKoszulData
import Sheaf.SixFunctors.PrincipalStrictSmallModelComparison
import Sheaf.SixFunctors.PrincipalStrictSmallModelLocalTests
import Sheaf.CategoryTheory.RingedKoszulCompletionReflector
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono

/-! # Reflection by the principal strict Koszul limit

Source: Stacks Project, Tags 099B, 0A0E and 0941.
(blueprint: lem-sf-principal-strict-limit-reflector).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
universe c v r w
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.RegularRoosKoszul

attribute [local irreducible] KoszulSmallModel.derivedEquiv

universe u₁ u₂ v₁ v₂

private theorem precomposition_bijective_of_equivalence
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
    (E : A ≌ B) {X Y L : A} {Z : B} (u : X ⟶ Y)
    (v : E.functor.obj X ⟶ Z) (e : E.functor.obj Y ≅ Z)
    (he : E.functor.map u ≫ e.hom = v)
    (h : Function.Bijective (fun f : Z ⟶ E.functor.obj L ↦ v ≫ f)) :
    Function.Bijective (fun f : Y ⟶ L ↦ u ≫ f) := by
  let b : (Y ⟶ L) ≃ (Z ⟶ E.functor.obj L) :=
    E.fullyFaithfulFunctor.homEquiv.trans (Iso.homCongr e (Iso.refl _))
  have hb := h.comp b.bijective
  have hmap := (E.fullyFaithfulFunctor.homEquiv (X := X) (Y := L)).bijective
  have heq : (fun f : Y ⟶ L ↦ v ≫ b f) =
      (fun f ↦ E.functor.map (u ≫ f)) := by
    funext f
    change v ≫ (e.inv ≫ E.functor.map f ≫ 𝟙 _) = E.functor.map (u ≫ f)
    rw [Category.comp_id, ← he, Category.assoc, Iso.hom_inv_id_assoc, Functor.map_comp]
  change Function.Bijective (fun f : Y ⟶ L ↦ v ≫ b f) at hb
  rw [heq] at hb
  exact (Function.Bijective.of_comp_iff' hmap _).mp hb

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max c v r})
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [HasDerivedCategory.{w} (Modules.{c, v, r} R)]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ Modules.{c, v, r} R)]

variable [∀ W : C, HasSheafify (J.over W) AddCommGrpCat.{max c v r}]
  [∀ W : C, HasSheafify (J.over W) CommRingCat.{max c v r}]
  [∀ W : C, (J.over W).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [∀ W : C, HasDerivedCategory.{w}
  (SheafOfModules.{max c v r} ((sheafCompose (J.over W)
    (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj (R.over W)))]

/-- The principal strict Koszul limit is the reflection onto locally derived complete
objects, with the actual normalized strict augmentation unit.

Source: Stacks Project, algebraization.tex, Tags 099B and 0A0E; sites-cohomology.tex,
Tag 0941 (blueprint: lem-sf-principal-strict-limit-reflector).

Proof: pass to the canonical small model of the site in the coefficient universe.
The induced exact equivalence of module sheaves preserves tensor products, single
complexes, principal cones and the transitions (t,1). Dualizing the positive singleton
Koszul complex and evaluating at one identifies it with the principal negative cone;
tensor symmetry gives the strict tensor-tower identification. Compare the total
right-derived limits by their universal properties. Naturality of their comparisons
at the ordinary constant/limit unit identifies the transported unit with constantUnit
followed by the actual augmentation, rather than merely its level projections.
Apply the singleton ringed Koszul reflector to the ideal represented by the monomorphism
multiplication by t from the unit module.
It supplies completeness of the output and the displayed Hom bijection. The local test
is invariant under the equivalence on every slice: restriction and derived internal
Hom commute with this exact site equivalence and localization is sheafified sectionwise.
Sections in the principal ideal are locally multiples of t; vanishing descends, so
it suffices to test the displayed multiples on every slice. Transport the reflector
and its Hom bijection back. No K-flatness or exact products are needed. A unit gives the
zero reflection; on the zero ring both sides and every localization test are zero. -/
theorem principal_strict_limit_reflector
    (t : (SheafOfModules.unit (ring.{c, v, r} R)).sections)
    (hreg : Mono (globalSectionMultiplication.{c, v, max c v r} R t))
    (Q : CochainComplex (Modules.{c, v, r} R) ℤ) :
    locallyComplete.{c, v, r, w} R t (koszulCompletion R Q t) ∧
      ∀ L, locallyComplete.{c, v, r, w} R t L →
        Function.Bijective (fun f : koszulCompletion R Q t ⟶ L ↦
        koszulUnit.{c, v, r, w} R (DerivedCategory.Q.obj Q) Q (Iso.refl _) t ≫ f) := by
  let K : DerivedCategory.{w} (Modules.{c, v, r} R) :=
    koszulCompletion R Q t
  let nativeSheafify : HasSheafify J AddCommGrpCat.{max c v r} := inferInstance
  let nativeWEquals : J.WEqualsLocallyBijective AddCommGrpCat.{max c v r} := inferInstance
  let nativeDerived : HasDerivedCategory.{w} (Modules.{c, v, r} R) := inferInstance
  let nativeTowerDerived : HasDerivedCategory.{w} (ℕᵒᵖ ⥤ Modules.{c, v, r} R) := inferInstance
  let nativeSliceSheafify : ∀ W : C,
      HasSheafify (J.over W) AddCommGrpCat.{max c v r} := inferInstance
  let nativeSliceCommSheafify : ∀ W : C,
      HasSheafify (J.over W) CommRingCat.{max c v r} := inferInstance
  let nativeSliceWEquals : ∀ W : C,
      (J.over W).WEqualsLocallyBijective AddCommGrpCat.{max c v r} := inferInstance
  let nativeSliceDerived : ∀ W : C, HasDerivedCategory.{w}
      (SheafOfModules.{max c v r} ((sheafCompose (J.over W)
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj (R.over W))) :=
    inferInstance
  let Js := (equivSmallModel.{max c v r} C).inverse.inducedTopology J
  let smallSheafify : HasSheafify Js AddCommGrpCat.{max c v r} :=
    SheafOfModules.hasSheafify_coefficientUniverse.{max c v r, max c v r, max c v r}
  let smallSliceSheafify : ∀ U : SmallModel.{max c v r} C,
      HasSheafify (Js.over U) AddCommGrpCat.{max c v r} :=
    fun _ ↦ SheafOfModules.hasSheafify_coefficientUniverse.{max c v r, max c v r, max c v r}
  let S := KoszulSmallModel.ring.{c, v, max c v r} R
  let A := SheafOfModules.{max c v r}
    ((sheafCompose _ (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj S)
  let smallDerived : HasDerivedCategory A := HasDerivedCategory.standard A
  let smallTowerDerived : HasDerivedCategory (ℕᵒᵖ ⥤ A) := HasDerivedCategory.standard _
  let smallSliceDerived : ∀ U : SmallModel.{max c v r} C,
      HasDerivedCategory (SheafOfModules.{max c v r}
        ((sheafCompose (_ : GrothendieckTopology (Over U))
          (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj (S.over U))) :=
    fun _ ↦ HasDerivedCategory.standard _
  let a := KoszulSmallModel.globalSection.{c, v, max c v r} R ⟨t.val, t.property⟩
  let Rg := (sheafCompose _
    (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj S
  let I := SheafOfModules.unit Rg
  let μ := ringedKoszulScalar S a
  let : Mono (globalSectionMultiplication.{c, v, max c v r} R t) := hreg
  have : Mono (globalSectionMultiplication.{c, v, max c v r} R t).val :=
    inferInstanceAs (Mono ((SheafOfModules.forget _).map
      (globalSectionMultiplication.{c, v, max c v r} R t)))
  have hμval : Mono μ.val := PresheafOfModules.mono_of_injective (fun {U} ↦ by
    exact PresheafOfModules.injective_of_mono
      (globalSectionMultiplication.{c, v, max c v r} R t).val
        ((equivSmallModel.{max c v r} C).inverse.op.obj U))
  let : Mono μ := (SheafOfModules.forget Rg).mono_of_mono_map hμval
  have hgen (U : SmallModel.{max c v r} C) :
      IsRingedIdealGeneratingList S I μ U 1 (fun _ ↦ a.val (op U)) := by
    let M := I.over U
    let s : ULift.{max c v r} (Fin 1) → M.sections :=
      fun _ ↦ M.unitHomEquiv (𝟙 M)
    let f := M.freeHomEquiv.symm s
    have hf : SheafOfModules.ιFree (R := _) (ULift.up (0 : Fin 1)) ≫ f = 𝟙 M := by
      apply M.unitHomEquiv.injective
      rw [← SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply]
      simp only [f, Equiv.apply_symm_apply]
      rfl
    let : IsSplitEpi f := IsSplitEpi.mk' ⟨SheafOfModules.ιFree (ULift.up (0 : Fin 1)), hf⟩
    let σ : M.GeneratingSections :=
      { I := ULift.{max c v r} (Fin 1), s := s, epi := inferInstance }
    refine ⟨σ, Equiv.ulift, ?_⟩
    intro i
    change μ.val.app (op U) (1 : S.obj.obj (op U)) = a.val (op U)
    exact congrArg (fun s : (SheafOfModules.unit Rg).sections ↦ s.val (op U))
      ((SheafOfModules.unit Rg).unitHomEquiv.apply_symm_apply ⟨a.val, a.property⟩)
  obtain ⟨D, hc, hb, _, _⟩ := ringedKoszulCompletionReflector S 1 (fun _ ↦ a) I μ hgen
  let E := KoszulSmallModel.derivedEquiv.{c, v, max c v r, w, max c v r + 1} R
  let N := E.functor.obj (DerivedCategory.Q.obj Q)
  obtain ⟨e, he⟩ :=
    principal_strict_small_model_comparison.{c, v, r, w, max c v r + 1} R t Q D
  have hcomp := hc N
  have localTests :=
    @principal_strict_small_model_local_tests.{c, v, r, w, max c v r + 1}
      C _ J R nativeSheafify nativeWEquals nativeDerived nativeTowerDerived
      nativeSliceSheafify nativeSliceCommSheafify nativeSliceWEquals nativeSliceDerived
      smallSheafify smallSliceSheafify smallDerived smallSliceDerived
  have htest := localTests t K
  refine ⟨htest.mpr ?_, ?_⟩
  · intro U f hf
    exact (hcomp U f hf).of_iso
      ((derivedInternalHom _ (S.over U)).mapIso
        ((Iso.refl _).prod ((ringedDerivedRestriction S U).mapIso e)))
  · intro L hL
    have hLs := (localTests t L).mp hL
    have hbij := hb N (E.functor.obj L) hLs
    exact precomposition_bijective_of_equivalence E
      (koszulUnit.{c, v, r, w} R (DerivedCategory.Q.obj Q) Q (Iso.refl _) t)
      (D.unit N) e he hbij

end CategoryTheory.RegularRoosKoszul
