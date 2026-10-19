/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.StrictTowerArithmeticRestrictionDefs
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.CategoryTheory.TowerSplitEnvelope
import WeilConjectures.Algebra.Homology.KernelShiftedMappingCone

/-! # The explicit arithmetic map between cochain Roos models

Source: Stacks Project, Tags 0941, 070M and 0H9K.
-/

@[expose] public section

set_option autoImplicit false
universe a b
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.StrictTowerArithmetic

private lemma split_transition
    {A : Type a} [Category.{b} A] [Abelian A]
    (T : ℕᵒᵖ ⥤ A) [Injective T] (n : ℕ) :
    IsSplitEpi (T.map (homOfLE (Nat.le_succ n)).op) := by
  obtain ⟨E, j, _, _, _, _, hs, hm, _, _⟩ := tower_split_envelope (C := A)
  have (d : ℕᵒᵖ) : Mono ((j.app T).app d) := hm T d.unop
  have : Mono (j.app T) := NatTrans.mono_of_mono_app _
  let r := Injective.factorThru (𝟙 T) (j.app T)
  have hr : j.app T ≫ r = 𝟙 T := Injective.comp_factorThru _ _
  have : IsSplitEpi ((E.obj T).map (homOfLE (Nat.le_succ n)).op) := hs T n
  refine IsSplitEpi.mk' ⟨(j.app T).app (op n) ≫
    section_ ((E.obj T).map (homOfLE (Nat.le_succ n)).op) ≫ r.app (op (n + 1)), ?_⟩
  rw [Category.assoc, Category.assoc, ← r.naturality]
  simp only [← Category.assoc, IsSplitEpi.id, Category.comp_id]
  exact congrArg (fun q ↦ q.app (op n)) hr

private lemma split_map
    {A : Type a} [Category.{b} A] (T : ℕᵒᵖ ⥤ A)
    (hs : ∀ n, IsSplitEpi (T.map (homOfLE (Nat.le_succ n)).op))
    (n m : ℕ) (h : n ≤ m) : IsSplitEpi (T.map (homOfLE h).op) := by
  induction m, h using Nat.le_induction with
  | base => simpa using (inferInstance : IsSplitEpi (𝟙 (T.obj (op n))))
  | succ m h ih =>
    have := hs m
    have : IsSplitEpi (T.map (homOfLE (Nat.le_succ m)).op ≫
        T.map (homOfLE h).op) := inferInstance
    convert this using 1
    rw [← T.map_comp]
    congr 1

private lemma telescoping
    {D : Type*} [Category D] [Preadditive D]
    (X : ℕᵒᵖ ⥤ D) [HasProduct (fun i : ℕ ↦ X.obj (op i))] (s m : ℕ) :
    (∑ k ∈ Finset.range m,
      (Pi.π (fun i : ℕ ↦ X.obj (op i)) (s + k) -
        Pi.π (fun i : ℕ ↦ X.obj (op i)) (s + k + 1) ≫
          X.map (homOfLE (Nat.le_succ (s + k))).op) ≫
        X.map (homOfLE (Nat.le_add_right s k)).op) =
      Pi.π (fun i : ℕ ↦ X.obj (op i)) s -
        Pi.π (fun i : ℕ ↦ X.obj (op i)) (s + m) ≫
          X.map (homOfLE (Nat.le_add_right s m)).op := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    have hcomp : X.map (homOfLE (Nat.le_succ (s + m))).op ≫
        X.map (homOfLE (Nat.le_add_right s m)).op =
        X.map (homOfLE (Nat.le_add_right s (m + 1))).op := by
      rw [← X.map_comp]
      rfl
    simp only [Preadditive.sub_comp, Category.assoc, hcomp]
    abel

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma block_square
    {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
    (e : ℕ) (he : 1 ≤ e) (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    boundary I ≫ block e I.asFunctor =
      selection e I.asFunctor ≫ boundary ((complexRestriction _ e).obj I) := by
  apply Pi.hom_ext
  intro n
  let s := e * (n + 1) - 1
  have hnext : s + e = e * (n + 1 + 1) - 1 := by
    dsimp [s]
    rw [Nat.mul_succ e (n + 1)]
    have : 1 ≤ e * (n + 1) := by nlinarith
    omega
  let X := I.asFunctor
  change (towerTransitionEndomorphism (fun n : ℕ ↦
      X.map (homOfLE (Nat.le_succ n)).op) ≫ block e X) ≫
      Pi.π (fun n : ℕ ↦ X.obj ((index e).obj (op n))) n =
    (selection e X ≫ towerTransitionEndomorphism (fun n : ℕ ↦
      X.map ((index e).map (homOfLE (Nat.le_succ n)).op))) ≫
      Pi.π (fun n : ℕ ↦ X.obj ((index e).obj (op n))) n
  simp only [block, selection, towerTransitionEndomorphism,
    towerProductShift, Category.assoc, Pi.lift_π, Preadditive.comp_sub,
    Category.comp_id, Preadditive.comp_sum, Preadditive.sub_comp,
    Category.id_comp, Pi.lift_π_assoc]
  have ht := telescoping X s e
  simp only [Preadditive.sub_comp, Category.assoc, Finset.sum_sub_distrib] at ht
  dsimp only [s] at ht hnext
  convert ht using 1
  · rfl
  · congr 1
    have hcongr (k l : ℕ) (hk : s ≤ k) (hl : s ≤ l) (hkl : k = l) :
        Pi.π (fun i : ℕ ↦ X.obj (op i)) k ≫ X.map (homOfLE hk).op =
          Pi.π (fun i : ℕ ↦ X.obj (op i)) l ≫ X.map (homOfLE hl).op := by
      subst l
      rfl
    have h : s ≤ e * (n + 1 + 1) - 1 := by omega
    change Pi.π (fun i : ℕ ↦ X.obj (op i)) (e * (n + 1 + 1) - 1) ≫
        X.map (homOfLE h).op = _
    exact hcongr _ _ _ _ hnext.symm

private noncomputable def ordinaryCone
    {A : Type a} [Category.{b} A] [Abelian A] [HasLimitsOfShape ℕᵒᵖ A]
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) : Cone I.asFunctor where
  pt := (limitComplex A).obj I
  π :=
    { app := fun n ↦
        { f := fun i ↦ limit.π (I.X i) n
          comm' := fun i j _ ↦ by
            exact (limMap_π (I.d i j) n).symm }
      naturality := fun m n f ↦ by
        ext i
        change 𝟙 _ ≫ limit.π (I.X i) n =
          limit.π (I.X i) m ≫ (I.X i).map f
        simp }

private noncomputable def ordinaryConeIsLimit
    {A : Type a} [Category.{b} A] [Abelian A] [HasLimitsOfShape ℕᵒᵖ A]
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) : IsLimit (ordinaryCone I) := by
  apply HomologicalComplex.isLimitOfEval
  intro i
  exact limit.isLimit (I.X i)

private noncomputable def familyMap
    {A : Type a} [Category.{b} A] [Abelian A]
    [HasCountableProducts A] [HasLimitsOfShape ℕᵒᵖ A]
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (limitComplex A).obj I ⟶ ∏ᶜ (fun n : ℕ ↦ I.asFunctor.obj (op n)) :=
  Pi.lift (fun n ↦ (ordinaryCone I).π.app (op n))

private lemma familyMap_boundary
    {A : Type a} [Category.{b} A] [Abelian A]
    [HasCountableProducts A] [HasLimitsOfShape ℕᵒᵖ A]
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) : familyMap I ≫ boundary I = 0 := by
  apply Pi.hom_ext
  intro n
  simp only [familyMap, boundary, towerTransitionEndomorphism, towerProductShift,
    Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id, Category.assoc,
    Pi.lift_π, Pi.lift_π_assoc, zero_comp, sub_eq_zero]
  exact ((ordinaryCone I).w (homOfLE (Nat.le_succ n)).op).symm

private noncomputable def familyMapIsKernel
    {A : Type a} [Category.{b} A] [Abelian A]
    [HasCountableProducts A] [HasLimitsOfShape ℕᵒᵖ A]
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    IsLimit (KernelFork.ofι (familyMap I) (familyMap_boundary I)) := by
  apply Fork.IsLimit.mk'
  intro s
  let k := s.ι
  have hk : k ≫ boundary I = 0 := by simpa only [comp_zero] using s.condition
  let c : Cone I.asFunctor :=
    { pt := s.pt
      π := NatTrans.ofOpSequence (fun n ↦ k ≫ Pi.π _ n) (by
        intro n
        have h := congrArg (fun q ↦ q ≫ Pi.π _ n) hk
        change 𝟙 _ ≫ k ≫ Pi.π _ n = _
        rw [Category.id_comp]
        simpa only [boundary, towerTransitionEndomorphism, towerProductShift,
          Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id,
          Category.assoc,
          Pi.lift_π, zero_comp, sub_eq_zero] using h) }
  have hfac : (ordinaryConeIsLimit I).lift c ≫ familyMap I = k := by
    apply Pi.hom_ext
    intro n
    simpa only [familyMap, c, NatTrans.ofOpSequence_app, Category.assoc, Pi.lift_π] using
      (ordinaryConeIsLimit I).fac c (op n)
  refine ⟨(ordinaryConeIsLimit I).lift c, hfac, ?_⟩
  intro m hm
  apply (ordinaryConeIsLimit I).hom_ext
  intro n
  have hm' : m ≫ familyMap I = k := hm
  have h := congrArg (fun q ↦ q ≫ Pi.π _ n.unop) (hm'.trans hfac.symm)
  simpa only [familyMap, Category.assoc, Pi.lift_π] using h

private lemma product_boundary_split
    {D : Type*} [Category D] [Preadditive D]
    {K : ℕ → D} [HasProduct K] (f : ∀ n, K (n + 1) ⟶ K n)
    (hf : ∀ n, IsSplitEpi (f n)) : IsSplitEpi (towerTransitionEndomorphism f) := by
  classical
  let a : ∀ n, ∏ᶜ K ⟶ K n := fun n ↦ Nat.rec (0 : ∏ᶜ K ⟶ K 0)
    (fun n an ↦ (an - Pi.π K n) ≫ @section_ _ _ _ _ (f n) (hf n)) n
  have ha (n : ℕ) : a (n + 1) ≫ f n = a n - Pi.π K n := by
    dsimp [a]
    simp only [Category.assoc, IsSplitEpi.id, Category.comp_id]
  refine IsSplitEpi.mk' ⟨Pi.lift a, ?_⟩
  apply Pi.hom_ext
  intro n
  simp only [towerTransitionEndomorphism, towerProductShift, Preadditive.comp_sub,
    Category.comp_id, Preadditive.sub_comp, Category.assoc, Pi.lift_π, Category.id_comp]
  rw [Pi.lift_π_assoc, ha]
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma boundary_epi
    {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (hs : ∀ (p : ℤ) (n : ℕ),
      IsSplitEpi ((I.X p).map (homOfLE (Nat.le_succ n)).op)) (p : ℤ) :
    Epi ((boundary I).f p) := by
  let ev := HomologicalComplex.eval A (ComplexShape.up ℤ) p
  let q := piComparison ev (fun n : ℕ ↦ I.asFunctor.obj (op n))
  let d := towerTransitionEndomorphism (K := fun n : ℕ ↦ (I.X p).obj (op n))
    (fun n ↦ (I.X p).map (homOfLE (Nat.le_succ n)).op)
  have hd : IsSplitEpi d := product_boundary_split _ (hs p)
  have h : (boundary I).f p ≫ q = q ≫ d := by
    apply Pi.hom_ext
    intro n
    change (ev.map (boundary I) ≫ q) ≫
        Pi.π (fun n : ℕ ↦ (I.X p).obj (op n)) n =
      (q ≫ d) ≫ Pi.π (fun n : ℕ ↦ (I.X p).obj (op n)) n
    simp only [Category.assoc]
    have hb := (towerTransitionEndomorphism_eq_iff
      (fun n : ℕ ↦ I.asFunctor.map (homOfLE (Nat.le_succ n)).op)
      (boundary I)).mp rfl n
    have hb' := congrArg ev.map hb
    simp only [Functor.map_comp, Functor.map_sub] at hb'
    rw [show q ≫ Pi.π (fun n : ℕ ↦ (I.X p).obj (op n)) n =
      ev.map (Pi.π (fun n : ℕ ↦ I.asFunctor.obj (op n)) n) from
      piComparison_comp_π ev _ n]
    rw [hb']
    dsimp only [d]
    have hn := (towerTransitionEndomorphism_eq_iff
      (fun n : ℕ ↦ (I.X p).map (homOfLE (Nat.le_succ n)).op) d).mp rfl n
    rw [hn, Preadditive.comp_sub]
    have hproj (m : ℕ) : q ≫ Pi.π (fun n : ℕ ↦ (I.X p).obj (op n)) m =
        ev.map (Pi.π (fun n : ℕ ↦ I.asFunctor.obj (op n)) m) :=
      piComparison_comp_π ev _ m
    rw [hproj n, ← Category.assoc, hproj (n + 1)]
    rfl
  have hq : IsIso q := inferInstance
  have hh := congrArg (fun t ↦ t ≫ inv q) h
  simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id] at hh
  rw [hh]
  infer_instance

open CochainComplex CochainComplex.HomComplex HomologicalComplex in
private lemma cocone_fst_f
    {A : Type a} [Category.{b} A] [Abelian A]
    {P Q : CochainComplex A ℤ} (f : P ⟶ Q) (p : ℤ) :
    (mappingCocone.fst f).f p =
      ((mappingCone f).shiftFunctorObjXIso (-1) p (p - 1) (by omega)).hom ≫
        homotopyCofiber.fstX f (p - 1) p (by change p - 1 + 1 = p; omega) := by
  simp [mappingCocone.fst,
    Cochain.leftShift_v (n := 1) _ _ _ _ p p (add_zero p) (p - 1) (by omega),
    mappingCone.fst]

open CochainComplex CochainComplex.HomComplex HomologicalComplex in
private lemma cocone_snd_v
    {A : Type a} [Category.{b} A] [Abelian A]
    {P Q : CochainComplex A ℤ} (f : P ⟶ Q) (p q : ℤ) (h : p + -1 = q) :
    (mappingCocone.snd f).v p q h =
      ((mappingCone f).shiftFunctorObjXIso (-1) p q (by omega)).hom ≫
        homotopyCofiber.sndX f q := by
  simp [mappingCocone.snd,
    Cochain.leftShift_v (n := 0) _ _ _ _ p q h q (add_zero q), mappingCone.snd,
    Int.negOnePow_even 2 ⟨1, rfl⟩]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma normalized_kernel_comparison
    {A : Type a} [Category.{b} A] [Abelian A]
    [HasCountableProducts A] [HasLimitsOfShape ℕᵒᵖ A]
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (hs : ∀ p : ℤ, Epi ((boundary I).f p)) :
    ∃ κ : (limitComplex A).obj I ⟶ model I,
      QuasiIso κ ∧ κ ≫ CochainComplex.mappingCocone.fst (boundary I) = familyMap I ∧
      ∀ (p q : ℤ) (h : p + -1 = q),
        κ.f p ≫ (CochainComplex.mappingCocone.snd (boundary I)).v p q h = 0 := by
  let _ := HasDerivedCategory.standard A
  obtain ⟨k, hk, hq, _⟩ :=
    CochainComplex.exists_kernel_to_shifted_mappingCone_of_degreewise_epi (boundary I) hs
  let t := (familyMapIsKernel I).conePointUniqueUpToIso (kernelIsKernel (boundary I))
  have ht : t.hom ≫ kernel.ι (boundary I) = familyMap I :=
    (familyMapIsKernel I).conePointUniqueUpToIso_hom_comp
      (kernelIsKernel (boundary I)) WalkingParallelPair.zero
  have : QuasiIso k := hq
  refine ⟨t.hom ≫ k, inferInstance, ?_, ?_⟩
  · apply HomologicalComplex.Hom.ext
    funext p
    simp only [HomologicalComplex.comp_f, Category.assoc, cocone_fst_f, (hk p).2]
    exact congrArg (fun q ↦ q.f p) ht
  · intro p q h
    obtain rfl : q = p - 1 := by omega
    simp only [HomologicalComplex.comp_f, Category.assoc, cocone_snd_v, (hk p).1,
      comp_zero]

open CochainComplex in
private noncomputable def coconeMap
    {A : Type a} [Category.{b} A] [Abelian A]
    {P Q P' Q' : CochainComplex A ℤ}
    (f : P ⟶ Q) (g : P' ⟶ Q') (a : P ⟶ P') (b : Q ⟶ Q')
    (h : f ≫ b = a ≫ g) : mappingCocone f ⟶ mappingCocone g :=
  (mappingCone.map f g a b h)⟦(-1 : ℤ)⟧'

open CochainComplex CochainComplex.HomComplex in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma coconeMap_fst
    {A : Type a} [Category.{b} A] [Abelian A]
    {P Q P' Q' : CochainComplex A ℤ}
    (f : P ⟶ Q) (g : P' ⟶ Q') (a : P ⟶ P') (b : Q ⟶ Q')
    (h : f ≫ b = a ≫ g) :
    coconeMap f g a b h ≫ mappingCocone.fst g = mappingCocone.fst f ≫ a := by
  apply HomologicalComplex.Hom.ext
  funext p
  change (coconeMap f g a b h).f p ≫ (mappingCocone.fst g).f p =
    (mappingCocone.fst f).f p ≫ a.f p
  rw [cocone_fst_f, cocone_fst_f]
  change (mappingCone.map f g a b h).f (p - 1) ≫
      (𝟙 _ ≫ HomologicalComplex.homotopyCofiber.fstX g (p - 1) p (by
        change p - 1 + 1 = p; omega)) =
    (𝟙 _ ≫ HomologicalComplex.homotopyCofiber.fstX f (p - 1) p (by
      change p - 1 + 1 = p; omega)) ≫ a.f p
  simp only [Category.id_comp]
  apply mappingCone.ext_from f p (p - 1) (by omega)
  · change (mappingCone.inl f).v p (p - 1) (by omega) ≫ _ = _
    rw [mappingCone.map, mappingCone.inl_v_desc_f_assoc]
    rw [Cochain.comp_v (n₂ := -1) _ _ _ p p (p - 1) (add_zero p) (by omega)]
    simp [mappingCone.inl]
  · rw [mappingCone.map, mappingCone.inr_f_desc_f_assoc]
    simp [mappingCone.inr]

open CochainComplex CochainComplex.HomComplex in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma coconeMap_snd
    {A : Type a} [Category.{b} A] [Abelian A]
    {P Q P' Q' : CochainComplex A ℤ}
    (f : P ⟶ Q) (g : P' ⟶ Q') (a : P ⟶ P') (b : Q ⟶ Q')
    (h : f ≫ b = a ≫ g) (p q : ℤ) (hpq : p + -1 = q) :
    (coconeMap f g a b h).f p ≫ (mappingCocone.snd g).v p q hpq =
      (mappingCocone.snd f).v p q hpq ≫ b.f q := by
  obtain rfl : q = p + -1 := by omega
  rw [cocone_snd_v, cocone_snd_v]
  change (mappingCone.map f g a b h).f (p + -1) ≫
      (𝟙 _ ≫ HomologicalComplex.homotopyCofiber.sndX g (p + -1)) =
    (𝟙 _ ≫ HomologicalComplex.homotopyCofiber.sndX f (p + -1)) ≫ b.f (p + -1)
  simp only [Category.id_comp]
  apply mappingCone.ext_from f p (p + -1) (by omega)
  · change (mappingCone.inl f).v p (p + -1) (by omega) ≫ _ = _
    rw [mappingCone.map, mappingCone.inl_v_desc_f_assoc]
    rw [Cochain.comp_v (n₂ := -1) _ _ _ p p (p + -1) (add_zero p) (by omega)]
    simp [mappingCone.inl]
  · rw [mappingCone.map, mappingCone.inr_f_desc_f_assoc]
    simp [mappingCone.inr]

private def ceilIndex (e : ℕ) : ℕᵒᵖ ⥤ ℕᵒᵖ :=
  (show ℕ →o ℕ from
    { toFun := fun n ↦ n / e
      monotone' := fun _ _ h ↦ Nat.div_le_div_right h }).monotone.functor.op
private lemma arithmetic_gc (e : ℕ) (he : 1 ≤ e) (i n : ℕ) :
    i / e ≤ n ↔ i ≤ e * (n + 1) - 1 := by
  have hp : 0 < e := he
  rw [Nat.div_le_iff_le_mul_add_pred hp]
  rw [Nat.mul_add, Nat.mul_one]
  omega
private def indexAdjunction (e : ℕ) (he : 1 ≤ e) : index e ⊣ ceilIndex e :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun n i ↦
        { toFun := fun f ↦ (homOfLE ((arithmetic_gc e he i.unop n.unop).2 f.unop.le)).op
          invFun := fun f ↦ (homOfLE ((arithmetic_gc e he i.unop n.unop).1 f.unop.le)).op
          left_inv := fun _ ↦ Subsingleton.elim _ _
          right_inv := fun _ ↦ Subsingleton.elim _ _ } }
private lemma limitMap_isIso
    (A : Type a) [Category.{b} A] [Abelian A] [HasLimitsOfShape ℕᵒᵖ A]
    (e : ℕ) (he : 1 ≤ e) (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    IsIso (limitMap e I) := by
  have : (index e).Initial := Functor.initial_of_adjunction (indexAdjunction e he)
  have (i : ℤ) : IsIso ((limitMap e I).f i) := by
    dsimp [limitMap]
    infer_instance
  exact HomologicalComplex.Hom.isIso_of_components _


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma cocone_ext
    {A : Type a} [Category.{b} A] [Abelian A]
    {P Q K : CochainComplex A ℤ} (f : P ⟶ Q) (a b : K ⟶ CochainComplex.mappingCocone f)
    (hfst : a ≫ CochainComplex.mappingCocone.fst f =
      b ≫ CochainComplex.mappingCocone.fst f)
    (hsnd : ∀ (p q : ℤ) (h : p + -1 = q),
      a.f p ≫ (CochainComplex.mappingCocone.snd f).v p q h =
        b.f p ≫ (CochainComplex.mappingCocone.snd f).v p q h) : a = b := by
  apply HomologicalComplex.Hom.ext
  funext p
  have hf := congrArg (fun t ↦ t.f p) hfst
  change a.f p ≫ (CochainComplex.mappingCocone.fst f).f p =
    b.f p ≫ (CochainComplex.mappingCocone.fst f).f p at hf
  have hs := hsnd p (p - 1) (by omega)
  rw [cocone_fst_f] at hf
  rw [cocone_snd_v] at hs
  apply (cancel_mono ((CochainComplex.mappingCone f).shiftFunctorObjXIso
    (-1) p (p - 1) (by omega)).hom).mp
  apply HomologicalComplex.homotopyCofiber.ext_to_X f (p - 1) p (by
    change p - 1 + 1 = p; omega)
  · simpa only [Category.assoc] using hf
  · simpa only [Category.assoc] using hs

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma familyMap_selection
    {A : Type a} [Category.{b} A] [Abelian A]
    [HasCountableProducts A] [HasLimitsOfShape ℕᵒᵖ A]
    (e : ℕ) (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    familyMap I ≫ selection e I.asFunctor =
      limitMap e I ≫ familyMap ((complexRestriction A e).obj I) := by
  apply Pi.hom_ext
  intro n
  simp only [familyMap, selection, Category.assoc, Pi.lift_π]
  apply HomologicalComplex.Hom.ext
  funext p
  change limit.π (I.X p) ((index e).obj (op n)) =
    (limitMap e I).f p ≫ (familyMap ((complexRestriction A e).obj I) ≫ Pi.π _ n).f p
  rw [show familyMap ((complexRestriction A e).obj I) ≫ Pi.π _ n =
    (ordinaryCone ((complexRestriction A e).obj I)).π.app (op n) from Pi.lift_π _ _]
  exact (limit.pre_π (I.X p) (index e) (op n)).symm

/-- The finite-block square and its canonical cochain mapping-cocone comparison.
Source: Stacks Project, Cohomology on Sites, Tag 0941; More on Algebra, Tag 0H9K;
Derived Categories, Tag 070M
(blueprint: lem-sp-strict-tower-arithmetic-restriction-cochain-model).

Proof:
1. Embed an injective tower J into the functorial finite-product split envelope.
The embedding is monic pointwise, hence monic as a tower map. Injectivity gives
a tower retraction. Compose the embedding at n, an envelope transition section,
and the retraction at n+1 to split J_(n+1) → J_n. Compose sections for each block.
2. In each cochain degree, solve x_0=0 and x_(n+1)=σ_n(x_n-y_n). The resulting map
from the product to itself is a right inverse of 1-shift. The same recursion works
for the restricted tower, so both transition differentials are degreewise epi.
3. The compatible-family map from the termwise limit into the product is a kernel
of 1-shift, degreewise and hence in complexes. Compose this kernel identification
with the kernel-to-shifted-cone quasi-isomorphism of Tag 070M. Normalize its sign
so that mappingCocone.fst is the compatible-family map and mappingCocone.snd is zero.
These define κ and κe with the stated coordinates.
4. Project the product square to coordinate n. Expand the block sum and telescope
successive transition composites. All internal terms cancel, leaving the difference
of the selected coordinate and the next selected coordinate transported back. Thus
boundary ≫ block = selection ≫ restricted boundary. The actual map of shifted cones
of this square defines c, with precisely the two asserted coordinates.
5. Project κ ≫ c and limitMap ≫ κe to both cone summands: their first coordinates
are the same selected compatible family and their second coordinates vanish.
Thus the maps agree. Since limitMap is an isomorphism for e≥1 and κ,κe are
quasi-isomorphisms, two-out-of-three makes c a quasi-isomorphism.
The zero tower, e=1, and zero transitions satisfy these same formulas; no exactness
of arbitrary countable products is used. -/
theorem strictTowerArithmeticRestrictionCochainModel
    (A : Type a) [Category.{b} A] [Abelian A]
    [HasCountableProducts A] [HasLimitsOfShape ℕᵒᵖ A]
    (e : ℕ) (he : 1 ≤ e) (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (hI : ∀ i : ℤ, Injective (I.X i)) :
        boundary I ≫ block e I.asFunctor =
          selection e I.asFunctor ≫ boundary ((complexRestriction _ e).obj I) ∧
        ∃ (κ : (limitComplex _).obj I ⟶ model I)
          (κe : (limitComplex _).obj ((complexRestriction _ e).obj I) ⟶
            model ((complexRestriction _ e).obj I))
          (c : model I ⟶ model ((complexRestriction _ e).obj I)),
          QuasiIso κ ∧ QuasiIso κe ∧ QuasiIso c ∧
          (∀ (i : ℤ) (n : ℕ),
            κ.f i ≫ (CochainComplex.mappingCocone.fst (boundary I)).f i ≫
                (Pi.π (fun n : ℕ ↦ I.asFunctor.obj (op n)) n).f i =
              limit.π (I.X i) (op n)) ∧
          (∀ (i j : ℤ) (h : i + -1 = j),
            κ.f i ≫ (CochainComplex.mappingCocone.snd (boundary I)).v i j h = 0) ∧
          (∀ (i : ℤ) (n : ℕ),
            κe.f i ≫ (CochainComplex.mappingCocone.fst
                (boundary ((complexRestriction _ e).obj I))).f i ≫
                (Pi.π (fun n : ℕ ↦ I.asFunctor.obj ((index e).obj (op n))) n).f i =
              limit.π (((complexRestriction _ e).obj I).X i) (op n)) ∧
          (∀ (i j : ℤ) (h : i + -1 = j),
            κe.f i ≫ (CochainComplex.mappingCocone.snd
              (boundary ((complexRestriction _ e).obj I))).v i j h = 0) ∧
          c ≫ CochainComplex.mappingCocone.fst (boundary ((complexRestriction _ e).obj I)) =
            CochainComplex.mappingCocone.fst (boundary I) ≫ selection e I.asFunctor ∧
          (∀ (i j : ℤ) (h : i + -1 = j),
            c.f i ≫ (CochainComplex.mappingCocone.snd
                (boundary ((complexRestriction _ e).obj I))).v i j h =
              (CochainComplex.mappingCocone.snd (boundary I)).v i j h ≫
                (block e I.asFunctor).f j) ∧
          κ ≫ c = limitMap e I ≫ κe := by
  have hsq := block_square e he I
  have hs (p : ℤ) (n : ℕ) :
      IsSplitEpi ((I.X p).map (homOfLE (Nat.le_succ n)).op) := by
    have := hI p
    exact split_transition (I.X p) n
  have hse (p : ℤ) (n : ℕ) :
      IsSplitEpi ((((complexRestriction A e).obj I).X p).map
        (homOfLE (Nat.le_succ n)).op) := by
    exact split_map (I.X p) (hs p) _ _
      (Nat.sub_le_sub_right (Nat.mul_le_mul_left e (by omega : n + 1 ≤ n + 1 + 1)) 1)
  obtain ⟨κ, hκ, hκfst, hκsnd⟩ := normalized_kernel_comparison I (boundary_epi I hs)
  obtain ⟨κe, hκe, hκefst, hκesnd⟩ := normalized_kernel_comparison
    ((complexRestriction A e).obj I) (boundary_epi _ hse)
  let c := coconeMap (boundary I) (boundary ((complexRestriction A e).obj I))
    (selection e I.asFunctor) (block e I.asFunctor) hsq
  have hcfst : c ≫ CochainComplex.mappingCocone.fst
      (boundary ((complexRestriction A e).obj I)) =
      CochainComplex.mappingCocone.fst (boundary I) ≫ selection e I.asFunctor :=
    coconeMap_fst _ _ _ _ _
  have hcsnd := coconeMap_snd (boundary I)
    (boundary ((complexRestriction A e).obj I))
    (selection e I.asFunctor) (block e I.asFunctor) hsq
  have hcomm : κ ≫ c = limitMap e I ≫ κe := by
    apply cocone_ext
    · rw [Category.assoc, hcfst, ← Category.assoc, hκfst, Category.assoc, hκefst]
      exact familyMap_selection e I
    · intro p q h
      simp only [HomologicalComplex.comp_f, Category.assoc]
      rw [hcsnd p q h, ← Category.assoc, hκsnd p q h, zero_comp, hκesnd p q h,
        comp_zero]
  have : QuasiIso κ := hκ
  have : QuasiIso κe := hκe
  have : IsIso (limitMap e I) := limitMap_isIso A e he I
  have : QuasiIso c := by
    have h : QuasiIso (κ ≫ c) := by rw [hcomm]; infer_instance
    exact (quasiIso_iff_comp_left κ c).mp h
  refine ⟨hsq, κ, κe, c, hκ, hκe, inferInstance, ?_, hκsnd, ?_, hκesnd,
    hcfst, hcsnd, hcomm⟩
  · intro p n
    have h := congrArg (fun q ↦ q ≫ Pi.π _ n) hκfst
    simp only [familyMap, Category.assoc, Pi.lift_π] at h
    exact congrArg (fun q ↦ q.f p) h
  · intro p n
    have h := congrArg (fun q ↦ q ≫ Pi.π _ n) hκefst
    simp only [familyMap, Category.assoc, Pi.lift_π] at h
    exact congrArg (fun q ↦ q.f p) h

end CategoryTheory.StrictTowerArithmetic
