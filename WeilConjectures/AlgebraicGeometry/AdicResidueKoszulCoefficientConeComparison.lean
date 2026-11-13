/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import WeilConjectures.AlgebraicGeometry.AdicResidueQuotientTensorTower
public import WeilConjectures.AlgebraicGeometry.KoszulComplex
import WeilConjectures.AlgebraicGeometry.AdicResidueExactCoefficientRealization
import WeilConjectures.CategoryTheory.AdditiveConeFamilyComparison
import WeilConjectures.CategoryTheory.ExteriorKoszulScalarRealization
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Single

/-! # Finite coefficient comparison for normalized Koszul augmentations

Source: Stacks Project, proetale.tex, lemma-naive-completion (099M), and
more-algebra.tex, lemma-sequence-Koszul-complexes.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u v
open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.ConstantCompletion
namespace AlgebraicGeometry.Scheme

/-- Keep the coefficient category abstract during the degree-zero calculation. -/
private theorem augmentationComparisonOfZero
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (E : C ⥤ D) [E.Additive]
    {K L : CochainComplex C ℤ} {T Q : CochainComplex D ℤ}
    (f : K ⟶ L) (ε : T ⟶ Q)
    (eK : (E.mapHomologicalComplex (.up ℤ)).obj K ≅ T)
    (eQ : (E.mapHomologicalComplex (.up ℤ)).obj L ≅ Q)
    {V Z : C} {M : D} (vK : V ≅ K.X 0) (vL : L.X 0 ≅ Z) (π : V ⟶ Z)
    (c : M ≅ E.obj V) (w : E.obj Z ⟶ Q.X 0) (ρ : M ⟶ T.X 0) (p : M ⟶ Q.X 0)
    (hf : vK.hom ≫ f.f 0 ≫ vL.hom = π)
    (heQ : eQ.hom.f 0 = E.map vL.hom ≫ w)
    (hu : c.hom ≫ E.map vK.hom ≫ eK.hom.f 0 = ρ)
    (hp : c.hom ≫ E.map π ≫ w = p) (hε : ρ ≫ ε.f 0 = p)
    (hex : ∀ g h : (E.mapHomologicalComplex (.up ℤ)).obj K ⟶ Q,
      g.f 0 = h.f 0 → g = h) :
    (E.mapHomologicalComplex (.up ℤ)).map f ≫ eQ.hom = eK.hom ≫ ε := by
  apply hex
  apply (cancel_epi (c.hom ≫ E.map vK.hom)).1
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    heQ, Category.assoc]
  rw [← E.map_comp_assoc, ← E.map_comp_assoc, Category.assoc, hf]
  have hun := congrArg (fun z ↦ z ≫ ε.f 0) hu
  simp only [Category.assoc] at hun
  rw [hun, hε, hp]

attribute [local irreducible] homComplexFunctor ringedKoszulDualTower
  completed ringedKoszulDualUnit adicResidueQuotientCoefficientUnit
  adicResidueQuotientModule

set_option maxHeartbeats 400000 in
-- Nested sheaf and complex functors require a larger elaboration heartbeat budget.
/-- Exact realization identifies the finite algebraic augmentation cones and their
strict transitions with those of any normalized coefficient augmentation.
This is a finite comparison: it asserts no eventual vanishing, uses no complex P,
and makes no assertion about derived inverse limits.

Source: Stacks Project, proetale.tex, proof of lemma-naive-completion (099M);
more-algebra.tex, lemma-sequence-Koszul-complexes; algebraization.tex,
lemma-derived-completion-koszul (0A0E). -/
theorem adicResidue_koszul_coefficient_cone_comparison
    (X : Scheme.{u}) {A : Type (max v (u + 1))} [CommRing A] [IsNoetherianRing A]
    (J : Ideal A) (U : coefficientProEtaleSiteModel.{u, v} X)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = J)
    (εA : ∀ n : ℕ, ExteriorAlgebra.koszulComplex A r (fun i ↦ a i ^ (n + 1)) ⟶
      (ChainComplex.single₀ (ModuleCat.{max v (u + 1)} A)).obj
        (ModuleCat.of A (A ⧸ (Ideal.span (Set.range a)) ^ (n + 1))))
    (tA : ∀ n m : ℕ, n ≤ m →
      (ExteriorAlgebra.koszulComplex A r (fun i ↦ a i ^ (m + 1)) ⟶
        ExteriorAlgebra.koszulComplex A r (fun i ↦ a i ^ (n + 1))))
    (qA : ∀ n m : ℕ, n ≤ m →
      ((ChainComplex.single₀ (ModuleCat.{max v (u + 1)} A)).obj
          (ModuleCat.of A (A ⧸ (Ideal.span (Set.range a)) ^ (m + 1))) ⟶
        (ChainComplex.single₀ (ModuleCat.{max v (u + 1)} A)).obj
          (ModuleCat.of A (A ⧸ (Ideal.span (Set.range a)) ^ (n + 1)))))
    (hεA : ∀ n, (εA n).f 0 = ModuleCat.ofHom
      (((Ideal.span (Set.range a)) ^ (n + 1)).mkQ.comp
        (exteriorPower.zeroEquiv A (Fin r →₀ A)).toLinearMap))
    (htA : ∀ n m h k, (tA n m h).f k = ModuleCat.ofHom
      (exteriorPower.map k
        (Finsupp.linearCombination A (fun i ↦ Finsupp.single i (a i ^ (m - n))))))
    (hqA : ∀ n m h,
      ModuleCat.ofHom ((Ideal.span (Set.range a)) ^ (m + 1)).mkQ ≫ (qA n m h).f 0 =
        ModuleCat.ofHom ((Ideal.span (Set.range a)) ^ (n + 1)).mkQ)
    (hc : ∀ n m h,
      HomologicalComplex.extendMap (tA n m h) ComplexShape.embeddingDownNat ≫
        HomologicalComplex.extendMap (εA n) ComplexShape.embeddingDownNat =
      HomologicalComplex.extendMap (εA m) ComplexShape.embeddingDownNat ≫
        HomologicalComplex.extendMap (qA n m h) ComplexShape.embeddingDownNat) :
    let R := (completed (coefficientProEtaleModelTopology.{u, v} X) A J).over U
    let b := fun i ↦ ringedKoszulSliceSection
      (completed (coefficientProEtaleModelTopology.{u, v} X) A J)
      (algebraSection (coefficientMap (coefficientProEtaleModelTopology.{u, v} X) A J)
        (a i)) U
    ∀ (ε : ringedKoszulDualTower R r b ⟶ adicResidueQuotientCoefficientTower X J U)
      (_hε : ∀ n : ℕ, ringedKoszulDualUnit R r b n ≫ ε.app (op n) =
        adicResidueQuotientCoefficientUnit X J U n),
    ∃ (E : ModuleCat.{max v (u + 1)} A ⥤ Mod R) (_hadd : E.Additive)
      (_hlim : PreservesFiniteLimits E) (_hcolim : PreservesFiniteColimits E)
      (e : ∀ n : ℕ,
        (E.mapHomologicalComplex (.up ℤ)).obj
          (HomologicalComplex.homotopyCofiber
            (HomologicalComplex.extendMap (εA n) ComplexShape.embeddingDownNat)) ≅
          (CochainComplex.mappingCone
            ((HomologicalComplex.functorEquivalence
              (Mod R) (.up ℤ) ℕᵒᵖ).inverse.map ε)).asFunctor.obj
              (op n)),
      ∀ (n m : ℕ) (h : n ≤ m),
        (E.mapHomologicalComplex (.up ℤ)).map
          (HomologicalComplex.homotopyCofiber.mapArrowHom
            (HomologicalComplex.extendMap (εA m) ComplexShape.embeddingDownNat)
            (HomologicalComplex.extendMap (εA n) ComplexShape.embeddingDownNat)
            (fun j : ℤ ↦ ⟨j - 1, sub_add_cancel j 1⟩)
            (Arrow.homMk
              (HomologicalComplex.extendMap (tA n m h) ComplexShape.embeddingDownNat)
              (HomologicalComplex.extendMap (qA n m h) ComplexShape.embeddingDownNat)
              (hc n m h))) ≫ (e n).hom =
        (e m).hom ≫
          (CochainComplex.mappingCone
            ((HomologicalComplex.functorEquivalence
              (Mod R) (.up ℤ) ℕᵒᵖ).inverse.map ε)).asFunctor.map
              (homOfLE h).op  := by
  have _ := hqA
  subst J
  intro O b ε hε
  obtain ⟨E, hadd, hlim, hcolim, c, q, hs, hq⟩ :=
    adicResidue_exact_coefficient_realization X (Ideal.span (Set.range a)) U
  let s := fun x : A ↦ ringedKoszulSliceSection
    (completed (coefficientProEtaleModelTopology.{u, v} X) A (Ideal.span (Set.range a)))
    (algebraSection (coefficientMap (coefficientProEtaleModelTopology.{u, v} X) A
      (Ideal.span (Set.range a))) x) U
  let H := E.mapHomologicalComplex (.up ℤ)
  let B (n : ℕ) := ModuleCat.of A (A ⧸ (Ideal.span (Set.range a)) ^ (n + 1))
  let K (n : ℕ) := (ExteriorAlgebra.koszulComplex A r (fun i ↦ a i ^ (n + 1))).extend
    ComplexShape.embeddingDownNat
  let L (n : ℕ) := ((ChainComplex.single₀ (ModuleCat A)).obj (B n)).extend
    ComplexShape.embeddingDownNat
  let f (n : ℕ) : K n ⟶ L n :=
    HomologicalComplex.extendMap (εA n) ComplexShape.embeddingDownNat
  let Q := adicResidueQuotientCoefficientTower X (Ideal.span (Set.range a)) U
  obtain ⟨eK, ht, hu⟩ := exteriorKoszul_scalar_realization O E c s hs r a tA htA
  let eQ (n : ℕ) : H.obj (L n) ≅ Q.obj (op n) :=
    H.mapIso (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat
      (B n) 0 0 rfl) ≪≫
    (HomologicalComplex.singleMapHomologicalComplex E (.up ℤ) 0).app (B n) ≪≫
    (HomologicalComplex.single (Mod O) (.up ℤ) 0).mapIso (q n)
  let vK (n : ℕ) : ModuleCat.of A A ⟶ (K n).X 0 :=
    ModuleCat.ofHom (exteriorPower.zeroEquiv A (Fin r →₀ A)).symm.toLinearMap ≫
      ((ExteriorAlgebra.koszulComplex A r (fun i ↦ a i ^ (n + 1))).extendXIso
        ComplexShape.embeddingDownNat (i := 0) rfl).inv
  have hvK (n : ℕ) : IsIso (vK n) := by
    change IsIso ((exteriorPower.zeroEquiv A (Fin r →₀ A)).toModuleIso.inv ≫ _)
    infer_instance
  have heQ (n : ℕ) : (eQ n).hom.f 0 =
      E.map ((((ChainComplex.single₀ (ModuleCat A)).obj (B n)).extendXIso
        ComplexShape.embeddingDownNat (i := 0) rfl).hom) ≫
      (q n).hom ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).inv := by
    simp only [eQ, H, Iso.trans_hom, Iso.app_hom, HomologicalComplex.comp_f,
      Functor.mapIso_hom, Functor.mapHomologicalComplex_map_f,
      HomologicalComplex.extendSingleIso_hom_f,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      HomologicalComplex.single_map_f_self, Category.assoc,
      Iso.inv_hom_id_assoc, ← E.map_comp_assoc]
    rfl
  have haug (n : ℕ) : H.map (f n) ≫ (eQ n).hom = (eK n).hom ≫ ε.app (op n) := by
    have hf0 : vK n ≫ (f n).f 0 ≫
        (((ChainComplex.single₀ (ModuleCat A)).obj (B n)).extendXIso
          ComplexShape.embeddingDownNat (i := 0) rfl).hom =
        ModuleCat.ofHom ((Ideal.span (Set.range a)) ^ (n + 1)).mkQ := by
      dsimp only [vK, f]
      rw [HomologicalComplex.extendMap_f _ _ (i := 0) (i' := 0) rfl, hεA n]
      dsimp only [B]
      simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
      change ModuleCat.ofHom
        (((((Ideal.span (Set.range a)) ^ (n + 1)).mkQ).comp
          (exteriorPower.zeroEquiv A (Fin r →₀ A)).toLinearMap).comp
            (exteriorPower.zeroEquiv A (Fin r →₀ A)).symm.toLinearMap) = _
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      simp
    have hp := congrArg (fun z ↦ z ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0
        (adicResidueQuotientModule X (Ideal.span (Set.range a)) U n)).inv) (hq n)
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at hp
    have hn := congrArg (fun z ↦
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0
        (SheafOfModules.unit (siteModuleRings O))).inv ≫ z.f 0) (hε n)
    simp only [HomologicalComplex.comp_f] at hn
    refine augmentationComparisonOfZero E (f n) (ε.app (op n)) (eK n) (eQ n)
      (asIso (vK n))
      (((ChainComplex.single₀ (ModuleCat A)).obj (B n)).extendXIso
        ComplexShape.embeddingDownNat (i := 0) rfl)
      (ModuleCat.ofHom ((Ideal.span (Set.range a)) ^ (n + 1)).mkQ)
      c ((q n).hom ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).inv)
      _ _ hf0 (heQ n) (hu n) hp hn ?_
    intro g h hzero
    apply HomologicalComplex.to_single_hom_ext
    exact hzero
  have hfepi (n : ℕ) : Epi (H.map (f n)) := by
    have hepi (k : ℕ) : Epi ((εA n).f k) := by
      cases k with
      | zero =>
        rw [hεA n]
        apply (ModuleCat.epi_iff_surjective _).2
        exact (Submodule.mkQ_surjective _).comp
          (exteriorPower.zeroEquiv A (Fin r →₀ A)).surjective
      | succ k =>
        exact (HomologicalComplex.isZero_single_obj_X (.down ℕ) 0 (B n) (k + 1)
          (by omega)).epi _
    have : Epi (f n) := by
      apply HomologicalComplex.epi_of_epi_f
      intro i
      by_cases hi : ∃ k, ComplexShape.embeddingDownNat.f k = i
      · obtain ⟨k, hk⟩ := hi
        dsimp only [f]
        rw [HomologicalComplex.extendMap_f _ _ hk]
        infer_instance
      · exact (HomologicalComplex.isZero_extend_X _ _ i (by simpa using hi)).epi _
    infer_instance
  obtain ⟨e, he⟩ := additiveConeFamilyComparison E K L f
    (fun n m h ↦ HomologicalComplex.extendMap (tA n m h) ComplexShape.embeddingDownNat)
    (fun n m h ↦ HomologicalComplex.extendMap (qA n m h) ComplexShape.embeddingDownNat)
    hc ε eK eQ haug ht hfepi
  exact ⟨E, hadd, hlim, hcolim, e, he⟩

end AlgebraicGeometry.Scheme
