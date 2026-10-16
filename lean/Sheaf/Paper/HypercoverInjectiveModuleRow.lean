/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.Paper.HypercoverResolutionModel
import Sheaf.CategoryTheory.RingedHypercoverInjectiveAugmentationRing
import Sheaf.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale

/-! # Injective hypercover rows over arbitrary rings

Source: Stacks Project, Hypercoverings, Tag 01GW.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FiniteSplitEtaleHypercover

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]

private theorem matching_local_lifting (U : FiniteSplitEtaleHypercover X)
    (n : ℕ) (T : X.Etale)
    (p : ∀ (Δ : SimplexCategory), Δ.len < n →
      (Δ ⟶ SimplexCategory.mk n) → (T ⟶ U.simplicial.obj (op Δ)))
    (hc : ∀ (Δ Δ' : SimplexCategory) (h : Δ.len < n) (h' : Δ'.len < n)
      (α : Δ' ⟶ Δ) (θ : Δ ⟶ SimplexCategory.mk n),
      p Δ h θ ≫ U.simplicial.map α.op = p Δ' h' (α ≫ θ)) :
    ∃ S : Sieve T, S ∈ X.smallEtaleTopology T ∧
      ∀ (V : X.Etale) (f : V ⟶ T), S f →
        ∃ t : V ⟶ U.simplicial.obj (op (SimplexCategory.mk n)),
          ∀ (Δ : SimplexCategory) (h : Δ.len < n) (θ : Δ ⟶ SimplexCategory.mk n),
            t ≫ U.simplicial.map θ.op = f ≫ p Δ h θ := by
  obtain ⟨m, hm, _⟩ := U.matching_universal n ((Scheme.Etale.forget X).obj T)
    (fun Δ h θ ↦ (Scheme.Etale.forget X).map (p Δ h θ)) (by
      intro Δ Δ' h h' α θ
      simpa only [← Functor.map_comp] using congrArg (Scheme.Etale.forget X).map
        (hc Δ Δ' h h' α θ))
  let m' : T ⟶ U.matching n := (Scheme.Etale.forget X).preimage m
  have hm' (Δ : SimplexCategory) (h : Δ.len < n) (θ : Δ ⟶ SimplexCategory.mk n) :
      m' ≫ U.projection n Δ h θ = p Δ h θ := by
    apply (Scheme.Etale.forget X).map_injective
    simpa only [m', Functor.map_comp, Functor.map_preimage] using hm Δ h θ
  let S := Sieve.ofArrows (fun _ : Unit ↦ U.simplicial.obj (op (SimplexCategory.mk n)))
    (fun _ ↦ U.matchingMap n)
  have hS : S ∈ X.smallEtaleTopology (U.matching n) := by
    apply (Scheme.ofArrows_mem_smallEtaleTopology_iff _).mpr
    ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    obtain ⟨y, hy⟩ := (U.matching_cover n).surj x
    exact ⟨(), y, hy⟩
  refine ⟨S.pullback m', X.smallEtaleTopology.pullback_stable m' hS, ?_⟩
  intro V f hf
  obtain ⟨i, t, ht⟩ := Sieve.ofArrows.exists hf
  refine ⟨t, ?_⟩
  intro Δ h θ
  rw [← U.matchingMap_projection n Δ h θ, ← Category.assoc]
  change t ≫ U.matchingMap n ≫ U.projection n Δ h θ = _
  rw [← Category.assoc, ← ht, Category.assoc, hm']

/-- An injective module sheaf has an exact augmented hypercover section complex.
Source: Stacks Project, Hypercoverings, Tag 01GW, for free left modules.
(blueprint: lem-sc-hypercover-injective-module-row).

Proof: realize the sheaf as modules over the sheafified constant ring, without changing
its underlying abelian presheaf. This equivalence preserves injectivity. Enlarge the
hom universe of the etale site and transport its topology and module sheaves along
ULiftHom.equiv. The matching universal property and the surjective matching maps give
local lifts of every lower-simplex matching family. Apply the ringed-hypercover exactness
theorem over this ring sheaf. Transport back the injective augmentation and the exactness
in every positive degree. A single-complex augmentation with these properties is a
quasi-isomorphism, by the degree-zero and positive-degree criteria for homology.
No commutativity of the coefficient ring is used; free modules are left modules. -/
theorem injective_module_row_quasiIso (U : FiniteSplitEtaleHypercover X)
    (R : Type (u + 1)) [Ring R]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) [Injective F] :
    QuasiIso (sectionAugmentation R U F) := by
  let C' := ULiftHom.{u + 1} X.Etale
  let up : X.Etale ⥤ C' := ULiftHom.up
  let down : C' ⥤ X.Etale := ULiftHom.down
  let top' := down.inducedTopology X.smallEtaleTopology
  have : down.IsEquivalence :=
    inferInstanceAs ((ULiftHom.equiv : X.Etale ≌ C').inverse.IsEquivalence)
  have : up.IsEquivalence :=
    inferInstanceAs ((ULiftHom.equiv : X.Etale ≌ C').functor.IsEquivalence)
  have : down.IsContinuous top' X.smallEtaleTopology := by
    dsimp [top', down]
    infer_instance
  have : up.IsContinuous X.smallEtaleTopology top' := by
    exact inferInstanceAs ((ULiftHom.equiv : X.Etale ≌ C').functor.IsContinuous
      X.smallEtaleTopology ((ULiftHom.equiv : X.Etale ≌ C').inverse.inducedTopology
        X.smallEtaleTopology))
  have : (ULiftHom.equiv.symm : C' ≌ X.Etale).functor.IsContinuous top'
      X.smallEtaleTopology := by change down.IsContinuous top' X.smallEtaleTopology; infer_instance
  have : (ULiftHom.equiv.symm : C' ≌ X.Etale).inverse.IsContinuous
      X.smallEtaleTopology top' := by
    change up.IsContinuous X.smallEtaleTopology top'
    infer_instance
  have : HasPullbacks C' := Adjunction.hasLimitsOfShape_of_equivalence down
  let pc := top'.toPrecoverage
  have hpc : pc.toGrothendieck = top' := by
    refine le_antisymm top'.toGrothendieck_toPrecoverage_le ?_
    intro T S hS
    have h := pc.generate_mem_toGrothendieck ((top'.arrows_mem_toPrecoverage_iff S).mpr hS)
    simpa only [Sieve.generate_sieve] using h
  have : top'.Subcanonical :=
    GrothendieckTopology.subcanonical_of_full_of_faithful down top' X.smallEtaleTopology
  let A := Scheme.etaleConstantModuleRing X R
  let G := Scheme.etaleConstantModuleFunctor X R
  have : G.IsEquivalence := Scheme.etaleConstantModuleFunctor_isEquivalence X R
  let M := G.obj F
  have : Injective M := (G.asEquivalence.map_injective_iff F).mpr inferInstance
  let A' := (down.sheafPushforwardContinuous RingCat.{u + 1}
    top' X.smallEtaleTopology).obj A
  let E : SheafOfModules.{u + 1} A ≌ SheafOfModules.{u + 1} A' :=
    SheafOfModules.pushforwardPushforwardEquivalence
      (ULiftHom.equiv.symm : C' ≌ X.Etale) (𝟙 A') (𝟙 A)
      (by ext V x; change (A.obj.map (𝟙 _)).hom x = x; simp)
      (by ext V x; change (A.obj.map (𝟙 _)).hom x = x; simp)
  let M' : SheafOfModules.{u + 1} A' := E.functor.obj M
  have : Injective M' := (E.map_injective_iff M).mpr inferInstance
  have : pc.toGrothendieck.Subcanonical := by rw [hpc]; infer_instance
  have hseq' := ringedHypercover_injective_augmentation_exact_ring.{u + 1, u + 1, u + 1} pc
  rw [hpc] at hseq'
  have hseq := hseq' A' M' (up.obj (⊤_ X.Etale)) (U.simplicial ⋙ up)
    (Functor.whiskerRight (U.simplicial.augmentOfIsTerminal terminalIsTerminal).hom up) (by
      intro n T w p hp hc
      obtain ⟨S, hS, hlift⟩ := matching_local_lifting U n (down.obj T)
        (fun Δ h θ ↦ down.map (p Δ h θ))
        (fun Δ Δ' h h' α θ ↦ congrArg down.map (hc Δ Δ' h h' α θ))
      refine ⟨S.functorPullback down, ?_, ?_⟩
      · change _ ∈ down.inducedTopology X.smallEtaleTopology T
        rw [← Functor.restrictedTopology_eq_inducedTopology]
        exact Functor.IsCocontinuous.cover_lift hS
      · intro V f hf
        obtain ⟨t, ht⟩ := hlift (down.obj V) (down.map f) hf
        refine ⟨ULift.up t, ?_, fun Δ h θ ↦ congrArg ULift.up (ht Δ h θ)⟩
        apply ULift.ext
        exact terminal.hom_ext _ _)
  let K := (sectionComplexFunctor R U).obj F
  let a := sectionAugmentation R U F
  have hd (n : ℕ) (s : K.X n) :
      K.d n (n + 1) s =
        ∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val • F.obj.map (U.simplicial.δ j).op s := by
    change (((AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat R)).obj
      (U.simplicial.rightOp ⋙ F.obj)).d n (n + 1)) s = _
    simp only [AlgebraicTopology.alternatingCofaceMapComplex,
      AlgebraicTopology.AlternatingCofaceMapComplex.obj, CochainComplex.of_d,
      AlgebraicTopology.AlternatingCofaceMapComplex.objD]
    change (∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val • F.obj.map (U.simplicial.δ j).op) s = _
    simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul,
      LinearMap.sum_apply, LinearMap.smul_apply]
  have hi : Function.Injective (a.f 0) := by
    have h := hseq.1
    change Function.Injective (F.obj.map (terminal.from _).op) at h
    exact h
  have hz : Function.Exact (a.f 0) (K.d 0 1) := by
    have h := hseq.2.1
    change Function.Exact (F.obj.map (terminal.from _).op)
      (fun s ↦ ∑ j : Fin 2, (-1 : ℤ) ^ j.val • F.obj.map (U.simplicial.δ j).op s) at h
    change Function.Exact (F.obj.map (terminal.from _).op) (fun s ↦ K.d 0 1 s)
    simpa only [hd] using h
  have hpos (n : ℕ) : K.ExactAt (n + 1) := by
    rw [HomologicalComplex.exactAt_iff' K n (n + 1) (n + 2) (by simp) (by simp)]
    apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
    have h := hseq.2.2 n
    change Function.Exact
      (fun s ↦ ∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val • F.obj.map (U.simplicial.δ j).op s)
      (fun s ↦ ∑ j : Fin (n + 3), (-1 : ℤ) ^ j.val • F.obj.map (U.simplicial.δ j).op s) at h
    change Function.Exact (fun s ↦ K.d n (n + 1) s) (fun s ↦ K.d (n + 1) (n + 2) s)
    simp only [hd]
    convert h using 1 <;> rfl
  rw [quasiIso_iff]
  intro n
  cases n with
  | zero =>
      rw [CochainComplex.quasiIsoAt₀_iff]
      apply (ShortComplex.quasiIso_iff_of_zeros _ ?_ ?_ ?_).mpr
        ⟨(ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr hz,
          (ModuleCat.mono_iff_injective _).mpr hi⟩
      · exact HomologicalComplex.single_obj_d (.up ℕ) 0 _ 0 1
      · exact HomologicalComplex.single_obj_d (.up ℕ) 0 _ 0 0
      · exact K.shape 0 0 (by simp)
  | succ n =>
      exact (quasiIsoAt_iff_exactAt a (n + 1)
        (HomologicalComplex.ExactAt.of_isZero
          (HomologicalComplex.isZero_single_obj_X _ _ _ (n + 1) (by omega)))).mpr (hpos n)

end AlgebraicGeometry.FiniteSplitEtaleHypercover
