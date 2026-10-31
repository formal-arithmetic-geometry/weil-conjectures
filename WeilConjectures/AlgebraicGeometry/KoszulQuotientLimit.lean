/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntrinsicKoszulCompletion
public import WeilConjectures.AlgebraicGeometry.CompletionMap
import WeilConjectures.AlgebraicGeometry.KoszulQuotientTensorAugmentation
import WeilConjectures.AlgebraicGeometry.KoszulQuotientConeIsIso
/-!
# The augmentation comparison of Koszul and quotient completions

Source: Weil conjectures blueprint, proper base change, order 1259
(blueprint: lemma-weil-pbc-koszul-quotient-limit).
-/

@[expose] public section

universe t

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme

noncomputable section

set_option backward.isDefEq.respectTransparency true

open CochainComplex CochainComplex.HomComplex

section Cone

universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
variable {P Q : CochainComplex C ℤ} (s : P ⟶ P) (t : Q ⟶ Q)
set_option backward.isDefEq.respectTransparency false in
private lemma cocone_delta_snd :
    δ (-1) 0 (mappingCocone.snd s) = -Cochain.ofHom (mappingCocone.fst s ≫ s) := by
  simp [mappingCocone.snd, mappingCocone.fst,
    Cochain.δ_leftShift (mappingCone.snd s) (-1) (-1) 0 (by omega) 1 (by omega),
    mappingCone.δ_snd, Cochain.leftShift_comp_zero_cochain,
    Cochain.ofHom_comp, Cocycle.cochain_ofHom_homOf_eq_coe]

private noncomputable def coconeMap (v : P ⟶ Q) (h : s ≫ v = v ≫ t) :
    mappingCocone s ⟶ mappingCocone t :=
  mappingCocone.lift t (mappingCocone.fst s ≫ v)
    ((mappingCocone.snd s).comp (Cochain.ofHom v) (add_zero _)) (by
      rw [δ_comp_ofHom, cocone_delta_snd, Cochain.neg_comp, ← Cochain.ofHom_comp]
      simp only [Category.assoc, h, neg_add_cancel])

private lemma cocone_ext {A : CochainComplex C ℤ} (s : P ⟶ P)
    (a b : A ⟶ mappingCocone s)
    (h₁ : a ≫ mappingCocone.fst s = b ≫ mappingCocone.fst s)
    (h₂ : ∀ p, a.f p ≫ (mappingCocone.snd s).v p (p + -1) rfl =
      b.f p ≫ (mappingCocone.snd s).v p (p + -1) rfl) : a = b := by
  ext p
  have h₁' := congrArg (fun f ↦ f.f p) h₁
  dsimp only [HomologicalComplex.comp_f] at h₁'
  calc
    a.f p = a.f p ≫ 𝟙 _ := (Category.comp_id _).symm
    _ = a.f p ≫ ((mappingCocone.fst s).f p ≫ (mappingCocone.inl s).v p p
          (add_zero p) + (mappingCocone.snd s).v p (p + -1) rfl ≫
            (mappingCocone.inr s).1.v (p + -1) p (by omega)) := by
      rw [mappingCocone.id_X]
    _ = b.f p ≫ ((mappingCocone.fst s).f p ≫ (mappingCocone.inl s).v p p
          (add_zero p) + (mappingCocone.snd s).v p (p + -1) rfl ≫
            (mappingCocone.inr s).1.v (p + -1) p (by omega)) := by
      simp only [Preadditive.comp_add, ← Category.assoc, h₁', h₂]
    _ = b.f p := by rw [mappingCocone.id_X, Category.comp_id]

private lemma coconeMap_fst (v : P ⟶ Q) (h : s ≫ v = v ≫ t) :
    coconeMap s t v h ≫ mappingCocone.fst t = mappingCocone.fst s ≫ v := by
  simp [coconeMap]

private lemma coconeMap_snd (v : P ⟶ Q) (h : s ≫ v = v ≫ t) (p : ℤ) :
    (coconeMap s t v h).f p ≫ (mappingCocone.snd t).v p (p + -1) rfl =
      (mappingCocone.snd s).v p (p + -1) rfl ≫ v.f (p + -1) := by
  simp [coconeMap]


end Cone

set_option backward.isDefEq.respectTransparency false in
private lemma koszulUnit_fst (X : Scheme.{t}) (Λ : Type t) [CommRing Λ] (r : ℕ) (f : Fin r → Λ)
    (C : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X Λ)) ℤ) :
    koszulCompletionUnitComplex X Λ r f C ≫
      mappingCocone.fst (koszulOneSubShift X Λ r f C) =
      koszulProductUnit X Λ r f C := by
  apply HomologicalComplex.Hom.ext
  funext p
  dsimp only [HomologicalComplex.comp_f, koszulCompletionUnitComplex]
  have h := mappingCocone.inl_v_fst_f (koszulOneSubShift X Λ r f C) p
  simp only [mappingCocone.inl, Cochain.rightShift_v (n := -1) _ _ _ _ p p
    (add_zero p) (p + -1) (by omega), mappingCone.inl, Cochain.mk_v,
    CochainComplex.shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv, Category.comp_id] at h
  simpa only [Category.assoc, Category.comp_id] using congrArg
    (fun z ↦ (koszulProductUnit X Λ r f C).f p ≫ z) h

set_option backward.isDefEq.respectTransparency false in
private lemma koszulUnit_snd (X : Scheme.{t}) (Λ : Type t) [CommRing Λ] (r : ℕ) (f : Fin r → Λ)
    (C : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X Λ)) ℤ) (p : ℤ) :
    (koszulCompletionUnitComplex X Λ r f C).f p ≫
      (mappingCocone.snd (koszulOneSubShift X Λ r f C)).v p (p + -1) rfl = 0 := by
  dsimp only [koszulCompletionUnitComplex]
  have h := mappingCocone.inl_v_snd_v (koszulOneSubShift X Λ r f C) p (p + -1) rfl
  simp only [mappingCocone.inl, Cochain.rightShift_v (n := -1) _ _ _ _ p p
    (add_zero p) (p + -1) (by omega), mappingCone.inl, Cochain.mk_v,
    CochainComplex.shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv, Category.comp_id] at h
  simpa only [Category.assoc, CategoryTheory.Limits.comp_zero] using congrArg
    (fun z ↦ (koszulProductUnit X Λ r f C).f p ≫ z) h

set_option backward.isDefEq.respectTransparency false

private lemma koszulConstantOne_isIso (X : Scheme.{t}) (Λ : Type t) [CommRing Λ] :
    IsIso (koszulConstantOne X Λ) := by
  let := (koszulConstantUnit_local X Λ).1
  let := (koszulConstantUnit_local X Λ).2
  let R := adicModuleRing X Λ
  let α := koszulConstantUnit X Λ
  let P := (siteConstantModulePresheafGeneral (C := X.ProEt) (ULift.{t + 1} Λ)).obj
    (ModuleCat.of (ULift.{t + 1} Λ) (ULift.{t + 1} Λ))
  let U : SheafOfModules.{t + 1} R := SheafOfModules.unit R
  let V := (PresheafOfModules.restrictScalars α).obj U.val
  let s : V.sections := V.sectionsMk (fun A ↦ (1 : R.obj.obj A)) (by
    intro A B h
    change R.obj.map h 1 = 1
    exact map_one _)
  let a : P ⟶ V := V.unitHomEquiv.symm s
  let b : (koszulConstantFunctor X Λ).obj
      (ModuleCat.of (ULift.{t + 1} Λ) (ULift.{t + 1} Λ)) ⟶ U :=
    (PresheafOfModules.sheafificationHomEquiv.{t + 1} α).symm a
  have hb (A : X.ProEtᵒᵖ) :
      b.val.app A ((toSheafify (ProEt.topology X) P.presheaf).app A
        (1 : ULift.{t + 1} Λ)) = (1 : R.obj.obj A) := by
    have h :=
      (PresheafOfModules.sheafificationHomEquiv.{t + 1} α (P := P) (F := U)).apply_symm_apply a
    have h' := congrArg (fun z ↦ (z.app A) (1 : ULift.{t + 1} Λ)) h
    change b.val.app A ((toSheafify (ProEt.topology X) P.presheaf).app A
      (1 : ULift.{t + 1} Λ)) = a.app A (1 : ULift.{t + 1} Λ) at h'
    have ha := congrArg (fun z ↦ z.val A) (V.unitHomEquiv.apply_symm_apply s)
    change a.app A (1 : ULift.{t + 1} Λ) = (1 : R.obj.obj A) at ha
    exact h'.trans ha
  have hu (A : X.ProEtᵒᵖ) :
      (koszulConstantOne X Λ).val.app A (1 : R.obj.obj A) =
        (toSheafify (ProEt.topology X) P.presheaf).app A
          (1 : ULift.{t + 1} Λ) :=
    (koszulConstantOne_exists X Λ).exists.choose_spec A
  have hub : koszulConstantOne X Λ ≫ b = 𝟙 U := by
    apply U.unitHomEquiv.injective
    apply Subtype.ext
    funext A
    change b.val.app A ((koszulConstantOne X Λ).val.app A
      (1 : R.obj.obj A)) = (1 : R.obj.obj A)
    rw [hu, hb]
  have hbu : b ≫ koszulConstantOne X Λ = 𝟙 _ := by
    apply (PresheafOfModules.sheafificationHomEquiv.{t + 1} α).injective
    apply PresheafOfModules.hom_ext
    intro A
    apply ModuleCat.hom_ext
    apply (LinearMap.ringLmapEquivSelf (ULift.{t + 1} Λ) ℤ _).injective
    change (koszulConstantOne X Λ).val.app A
      (b.val.app A ((toSheafify (ProEt.topology X) P.presheaf).app A (1 : ULift.{t + 1} Λ))) =
      (toSheafify (ProEt.topology X) P.presheaf).app A (1 : ULift.{t + 1} Λ)
    rw [hb, hu]
  exact ⟨b, hub, hbu⟩


private lemma koszulSheafUnitZero_isIso (X : Scheme.{t}) (Λ : Type t) [CommRing Λ]
    (r : ℕ) (f : Fin r → Λ) (n : ℕ) :
    IsIso (koszulSheafUnitZero X Λ r f n) := by
  let : IsIso (koszulConstantOne X Λ) := koszulConstantOne_isIso X Λ
  let : IsIso (ModuleCat.ofHom (exteriorPower.zeroEquiv (ULift.{t + 1} Λ)
      (Fin r →₀ ULift.{t + 1} Λ)).symm.toLinearMap) := by
    change IsIso (exteriorPower.zeroEquiv (ULift.{t + 1} Λ)
      (Fin r →₀ ULift.{t + 1} Λ)).symm.toModuleIso.hom
    infer_instance
  dsimp only [koszulSheafUnitZero]
  infer_instance


private lemma koszulTensorUnit_naturality
    (X : Scheme.{t}) (Λ : Type t) [CommRing Λ] (r : ℕ) (f : Fin r → Λ)
    (C D : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X Λ)) ℤ)
    (g : C ⟶ D) (n : ℕ) :
    koszulTensorUnit X Λ r f C n ≫
      HomologicalComplex.mapBifunctorMap g (𝟙 (koszulPowerSheaf X Λ r f n))
        (@curriedTensor _ _ (SheafOfModules.monoidalCategory (adicConstantRing X Λ)))
        (ComplexShape.up ℤ) = g ≫ koszulTensorUnit X Λ r f D n := by
  let := SheafOfModules.monoidalCategory (adicConstantRing X Λ)
  apply HomologicalComplex.Hom.ext
  funext p
  dsimp only [HomologicalComplex.comp_f, koszulTensorUnit]
  simp only [koszulTensorUnitComponent, Category.assoc,
    HomologicalComplex.ι_mapBifunctorMap, HomologicalComplex.id_f]
  change (ρ_ (C.X p)).inv ≫ C.X p ◁ koszulSheafUnitZero X Λ r f n ≫
    g.f p ▷ _ ≫ D.X p ◁ 𝟙 _ ≫ _ = _
  rw [whiskerLeft_id, Category.id_comp]
  simp only [← Category.assoc]
  congr 1
  simp only [Category.assoc, ← whisker_exchange, rightUnitor_inv_naturality]

private lemma koszulQuotientAugmentation_naturality
    (X : Scheme.{t}) (Λ : Type t) [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) (r : ℕ) (f : Fin r → Λ)
    (K L : proEtaleDerivedCategory X Λ)
    (M : AdicKFlatModel X Λ K) (N : AdicKFlatModel X Λ L) (n : ℕ)
    [IsIso (koszulSheafUnitZero X Λ r f n)]
    (v : koszulTensor X Λ r f M.complex n ⟶ adicReductionComplex X d M n)
    (w : koszulTensor X Λ r f N.complex n ⟶ adicReductionComplex X d N n)
    (hv : koszulTensorUnit X Λ r f M.complex n ≫ v =
      adicReductionAugmentation X d M n)
    (hw : koszulTensorUnit X Λ r f N.complex n ≫ w =
      adicReductionAugmentation X d N n)
    (hvzero : ∀ p q : ℤ, q ≠ 0 →
      HomologicalComplex.ιMapBifunctor M.complex (koszulPowerSheaf X Λ r f n)
        (@curriedTensor _ _ (SheafOfModules.monoidalCategory (adicConstantRing X Λ)))
        (ComplexShape.up ℤ) p q (p + q) rfl ≫ v.f (p + q) = 0)
    (hwzero : ∀ p q : ℤ, q ≠ 0 →
      HomologicalComplex.ιMapBifunctor N.complex (koszulPowerSheaf X Λ r f n)
        (@curriedTensor _ _ (SheafOfModules.monoidalCategory (adicConstantRing X Λ)))
        (ComplexShape.up ℤ) p q (p + q) rfl ≫ w.f (p + q) = 0)
    (g : M.complex ⟶ N.complex)
    (σ : adicReductionComplex X d M n ⟶ adicReductionComplex X d N n)
    (hσ : adicReductionAugmentation X d M n ≫ σ =
      g ≫ adicReductionAugmentation X d N n) :
    v ≫ σ = HomologicalComplex.mapBifunctorMap g (𝟙 (koszulPowerSheaf X Λ r f n))
      (@curriedTensor _ _ (SheafOfModules.monoidalCategory (adicConstantRing X Λ)))
      (ComplexShape.up ℤ) ≫ w := by
  let := SheafOfModules.monoidalCategory (adicConstantRing X Λ)
  apply HomologicalComplex.Hom.ext
  funext k
  dsimp only [HomologicalComplex.comp_f]
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  change p + q = k at hpq
  by_cases hq : q = 0
  · subst q
    have hp : p = k := by omega
    cases hp
    rw [← cancel_epi ((ρ_ (M.complex.X k)).inv ≫
      (M.complex.X k ◁ koszulSheafUnitZero X Λ r f n))]
    have h := congrArg (fun z ↦ z.f k) (show
      koszulTensorUnit X Λ r f M.complex n ≫ v ≫ σ =
        koszulTensorUnit X Λ r f M.complex n ≫
          HomologicalComplex.mapBifunctorMap g (𝟙 (koszulPowerSheaf X Λ r f n))
            (curriedTensor _) (ComplexShape.up ℤ) ≫ w from by
        rw [← Category.assoc, hv, hσ, ← hw, ← Category.assoc,
          ← Category.assoc, koszulTensorUnit_naturality])
    simpa only [HomologicalComplex.comp_f, koszulTensorUnit,
      koszulTensorUnitComponent, Category.assoc] using h
  · subst k
    rw [← Category.assoc, hvzero p q hq, CategoryTheory.Limits.zero_comp,
      HomologicalComplex.ι_mapBifunctorMap_assoc, hwzero p q hq]
    simp only [CategoryTheory.Limits.comp_zero]


set_option backward.isDefEq.respectTransparency true

set_option backward.isDefEq.respectTransparency false in
private lemma koszulQuotientProduct_comm (X : Scheme.{t}) (Λ : Type t) [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) (r : ℕ) (f : Fin r → Λ)
    (K : proEtaleDerivedCategory X Λ) (M : AdicKFlatModel X Λ K)
    (v : ∀ n, koszulTensor X Λ r f M.complex n ⟶ adicReductionComplex X d M n)
    (hstep : ∀ n, v (n + 1) ≫ adicReductionComplexStep X d M n =
      koszulTensorTransition X Λ r f M.complex n ≫ v n) :
    koszulOneSubShift X Λ r f M.complex ≫ Limits.Pi.map v =
      Limits.Pi.map v ≫ (𝟙 _ - adicReductionProductShift X d M) := by
  dsimp only [koszulOneSubShift, koszulProduct, adicReductionProduct,
    adicReductionProductShift, towerProductShift]
  rw [Preadditive.sub_comp, Preadditive.comp_sub, Category.id_comp, Category.comp_id]
  congr 1
  apply Pi.hom_ext
  intro n
  simp only [Category.assoc, Pi.map_π, Pi.lift_π, Pi.lift_π_assoc, Pi.map_π_assoc]
  rw [← Category.assoc, hstep, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
-- The statement elaborates several explicit product and cone constructions.
set_option linter.unusedVariables false in
-- The existing signature names an unused proof binder in its zero-summand clause.
/-- The canonical comparison is induced by the quotient augmentation, including both
coordinates of the shifted cone. The tensor augmentation is fixed by its restriction to
the degree-zero unit and by vanishing on all other Koszul-degree summands.

Source: blueprint order 1259 (blueprint: lemma-weil-pbc-koszul-quotient-limit).
Proof: apply lem-weil-pbc-noetherian-koszul-augmentation-pro-zero to the generators.
The augmentation to I powers exists because f_j^(n+1) belongs to I^(n+1).
Its degree-zero component is the quotient, so it commutes strictly with transitions.
Constant module sheafification is exact (lem-weil-pbc-sheafification-exact and
lem-pc-sites-module-sheafification-interface), hence preserves the pro-zero cone maps.
Tensor using the same flat-term K-flat model at every level (lem-pc-kflat-resolution,
def-weil-derived-tensor). The tensor-cone identification has sign (-1)^p on the shifted
summand in tensor degree p. K-flatness preserves quasi-isomorphisms and zero derived maps.
Apply lem-weil-pbc-ringed-strict-tower-homotopy-limit: the induced limit map is invertible.
The explicit cone action uses the product augmentation in both coordinates; exact
countable pro-etale products identify this with the total right derived strict limit.
The levelwise unit composites are the quotient units, so the cone lifts give the stated
unit equation. Maps of K-flat representatives commute with tensor augmentations and
transitions before localization. These squares descend through quasi-isomorphisms and
therefore give naturality for all derived morphisms, independently of representatives. -/
theorem koszulQuotientLimit (X : Scheme.{t}) (Λ : Type t) [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) (r : ℕ) (f : Fin r → Λ)
    (hf : Ideal.span (Set.range f) = d.ideal) :
    ∃ (v : ∀ (K : proEtaleDerivedCategory X Λ) (M : AdicKFlatModel X Λ K) (n : ℕ),
        @Quiver.Hom (CochainComplex
          (SheafOfModules.{t + 1} (adicModuleRing X Λ)) ℤ) inferInstance
          (koszulTensor X Λ r f M.complex n) (adicReductionComplex X d M n))
      (w : ∀ (K : proEtaleDerivedCategory X Λ) (M : AdicKFlatModel X Λ K),
        @Quiver.Hom (CochainComplex
          (SheafOfModules.{t + 1} (adicModuleRing X Λ)) ℤ) inferInstance
          (koszulCompletionComplex X Λ r f M.complex) (adicCompletionComplex X d M))
      (c : ∀ (K : proEtaleDerivedCategory X Λ) (M : AdicKFlatModel X Λ K),
        intrinsicKoszulCompletion X Λ d r f hf K M.complex M.isKFlat M.realization ≅
          adicCompletionObject X d M),
      (∀ (K : proEtaleDerivedCategory X Λ)
        (M : AdicKFlatModel X Λ K) (n : ℕ), koszulTensorUnit X Λ r f M.complex n ≫ v K M n =
        adicReductionAugmentation X d M n) ∧
      (∀ (K : proEtaleDerivedCategory X Λ)
        (M : AdicKFlatModel X Λ K) (n : ℕ) (p q : ℤ) (hq : q ≠ 0),
        HomologicalComplex.ιMapBifunctor M.complex (koszulPowerSheaf X Λ r f n)
          (@curriedTensor _ _ (SheafOfModules.monoidalCategory (adicConstantRing X Λ)))
          (ComplexShape.up ℤ) p q (p + q) rfl ≫ (v K M n).f (p + q) = 0) ∧
      (∀ (K : proEtaleDerivedCategory X Λ)
        (M : AdicKFlatModel X Λ K) (n : ℕ), v K M (n + 1) ≫ adicReductionComplexStep X d M n =
        koszulTensorTransition X Λ r f M.complex n ≫ v K M n) ∧
      (∀ (K : proEtaleDerivedCategory X Λ)
        (M : AdicKFlatModel X Λ K), w K M ≫ adicCompletionProjection X d M =
        CochainComplex.mappingCocone.fst (koszulOneSubShift X Λ r f M.complex) ≫
          Limits.Pi.map (v K M)) ∧
      (∀ (K : proEtaleDerivedCategory X Λ)
        (M : AdicKFlatModel X Λ K) (p : ℤ), (w K M).f p ≫
          (CochainComplex.mappingCocone.snd
            (𝟙 _ - adicReductionProductShift X d M)).v p (p + -1) rfl =
        (CochainComplex.mappingCocone.snd
          (koszulOneSubShift X Λ r f M.complex)).v p (p + -1) rfl ≫
            (Limits.Pi.map (v K M)).f (p + -1)) ∧
      (∀ (K : proEtaleDerivedCategory X Λ)
        (M : AdicKFlatModel X Λ K), (c K M).hom = (adicLocalization X Λ).map (w K M)) ∧
      (∀ (K : proEtaleDerivedCategory X Λ)
        (M : AdicKFlatModel X Λ K), intrinsicKoszulCompletionUnit X Λ d r f hf K M.complex
        M.isKFlat M.realization ≫ (c K M).hom = adicCompletionMap X d M) ∧
      (∀ (K L : proEtaleDerivedCategory X Λ)
        (M : AdicKFlatModel X Λ K) (N : AdicKFlatModel X Λ L)
        (g : M.complex ⟶ N.complex)
        (τ : ∀ n : ℕ, koszulTensor X Λ r f M.complex n ⟶
          koszulTensor X Λ r f N.complex n)
        (σ : ∀ n : ℕ, adicReductionComplex X d M n ⟶ adicReductionComplex X d N n)
        (a : koszulCompletionComplex X Λ r f M.complex ⟶
          koszulCompletionComplex X Λ r f N.complex)
        (b : adicCompletionComplex X d M ⟶ adicCompletionComplex X d N),
        (∀ n, τ n = HomologicalComplex.mapBifunctorMap g
          (𝟙 (koszulPowerSheaf X Λ r f n))
          (@curriedTensor _ _ (SheafOfModules.monoidalCategory (adicConstantRing X Λ)))
          (ComplexShape.up ℤ)) →
        (∀ n, adicReductionAugmentation X d M n ≫ σ n =
          g ≫ adicReductionAugmentation X d N n) →
        a ≫ CochainComplex.mappingCocone.fst (koszulOneSubShift X Λ r f N.complex) =
          CochainComplex.mappingCocone.fst (koszulOneSubShift X Λ r f M.complex) ≫
            Limits.Pi.map τ →
        (∀ p : ℤ, a.f p ≫
          (CochainComplex.mappingCocone.snd (koszulOneSubShift X Λ r f N.complex)).v
            p (p + -1) rfl =
          (CochainComplex.mappingCocone.snd (koszulOneSubShift X Λ r f M.complex)).v
            p (p + -1) rfl ≫ (Limits.Pi.map τ).f (p + -1)) →
        b ≫ adicCompletionProjection X d N =
          adicCompletionProjection X d M ≫ Limits.Pi.map σ →
        (∀ p : ℤ, b.f p ≫ (CochainComplex.mappingCocone.snd
            (𝟙 _ - adicReductionProductShift X d N)).v p (p + -1) rfl =
          (CochainComplex.mappingCocone.snd
            (𝟙 _ - adicReductionProductShift X d M)).v p (p + -1) rfl ≫
              (Limits.Pi.map σ).f (p + -1)) →
        (c K M).hom ≫ (adicLocalization X Λ).map b =
          (adicLocalization X Λ).map a ≫ (c L N).hom) := by
  classical
  obtain ⟨v, hvunit, hvzero, hvstep⟩ :=
    koszulQuotientTensorAugmentation X Λ d r f hf
  let w := fun (K : proEtaleDerivedCategory X Λ) (M : AdicKFlatModel X Λ K) ↦
    coconeMap (koszulOneSubShift X Λ r f M.complex)
      (𝟙 _ - adicReductionProductShift X d M) (Limits.Pi.map (v K M))
      (koszulQuotientProduct_comm X Λ d r f K M (v K M) (hvstep K M))
  have hwfst (K : proEtaleDerivedCategory X Λ) (M : AdicKFlatModel X Λ K) :
      w K M ≫ adicCompletionProjection X d M =
        mappingCocone.fst (koszulOneSubShift X Λ r f M.complex) ≫
          Limits.Pi.map (v K M) := coconeMap_fst _ _ _ _
  have hwsnd (K : proEtaleDerivedCategory X Λ) (M : AdicKFlatModel X Λ K) (p : ℤ) :
      (w K M).f p ≫
        (mappingCocone.snd (𝟙 _ - adicReductionProductShift X d M)).v p (p + -1) rfl =
      (mappingCocone.snd (koszulOneSubShift X Λ r f M.complex)).v p (p + -1) rfl ≫
        (Limits.Pi.map (v K M)).f (p + -1) := coconeMap_snd _ _ _ _ _
  have hwiso (K : proEtaleDerivedCategory X Λ) (M : AdicKFlatModel X Λ K) :
      IsIso ((adicLocalization X Λ).map (w K M)) :=
    koszulQuotientCone_isIso X Λ d r f hf K M (v K M) (hvunit K M)
      (hvzero K M) (hvstep K M) (w K M) (hwfst K M) (hwsnd K M)
  let c := fun (K : proEtaleDerivedCategory X Λ) (M : AdicKFlatModel X Λ K) ↦
    @asIso _ _ _ _ ((adicLocalization X Λ).map (w K M)) (hwiso K M)
  refine ⟨v, w, c, hvunit, ?_, hvstep, hwfst, hwsnd, ?_, ?_, ?_⟩
  · intro K M n p q hq
    exact hvzero K M n p q hq
  · intros
    rfl
  · intro K M
    have hu : koszulCompletionUnitComplex X Λ r f M.complex ≫ w K M =
        adicCompletionChainMap X d M := by
      apply cocone_ext (𝟙 _ - adicReductionProductShift X d M)
      · change (_ ≫ w K M) ≫ adicCompletionProjection X d M = _
        rw [Category.assoc, hwfst, ← Category.assoc, koszulUnit_fst]
        dsimp only [adicCompletionChainMap]
        rw [mappingCocone.lift_fst]
        apply Pi.hom_ext
        intro n
        simp only [Category.assoc, Pi.map_π, koszulProductUnit, Pi.lift_π_assoc,
          adicReductionProductAugmentation, Pi.lift_π]
        exact hvunit K M n
      · intro p
        dsimp only [HomologicalComplex.comp_f, adicCompletionChainMap]
        rw [Category.assoc, hwsnd, ← Category.assoc, koszulUnit_snd,
          zero_comp, mappingCocone.lift_f_snd_v]
        rfl
    change (M.realization.inv ≫ (adicLocalization X Λ).map
      (koszulCompletionUnitComplex X Λ r f M.complex)) ≫
        (adicLocalization X Λ).map (w K M) = _
    rw [Category.assoc, ← Functor.map_comp, hu]
    rfl
  · intro K L M N g τ σ a b hτ hσ hafst hasnd hbfst hbsnd
    have hv : Limits.Pi.map (v K M) ≫ Limits.Pi.map σ =
        Limits.Pi.map τ ≫ Limits.Pi.map (v L N) := by
      apply Pi.hom_ext
      intro n
      simp only [Category.assoc, Pi.map_π, Pi.map_π_assoc]
      let := koszulSheafUnitZero_isIso X Λ r f n
      have hn := koszulQuotientAugmentation_naturality X Λ d r f K L M N n
        (v K M n) (v L N n) (hvunit K M n) (hvunit L N n)
        (hvzero K M n) (hvzero L N n) g (σ n) (hσ n)
      rw [hn, hτ n]
    have hab : w K M ≫ b = a ≫ w L N := by
      apply cocone_ext (𝟙 _ - adicReductionProductShift X d N)
      · change (w K M ≫ b) ≫ adicCompletionProjection X d N =
          (a ≫ w L N) ≫ adicCompletionProjection X d N
        rw [Category.assoc, hbfst, ← Category.assoc, hwfst, Category.assoc, hv,
          ← Category.assoc, ← hafst, Category.assoc, ← hwfst]
        simp only [Category.assoc]
      · intro p
        have hv' := congrArg (fun z ↦ z.f (p + -1)) hv
        dsimp only [HomologicalComplex.comp_f] at hv' ⊢
        rw [Category.assoc, hbsnd, ← Category.assoc, hwsnd, Category.assoc, hv',
          ← Category.assoc, ← hasnd, Category.assoc, ← hwsnd]
        simp only [Category.assoc]
    change (adicLocalization X Λ).map _ ≫ (adicLocalization X Λ).map _ =
      (adicLocalization X Λ).map _ ≫ (adicLocalization X Λ).map _
    rw [← Functor.map_comp, ← Functor.map_comp, hab]

end

end AlgebraicGeometry.Scheme
