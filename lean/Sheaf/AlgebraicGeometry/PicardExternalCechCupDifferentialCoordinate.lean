/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R4
-/
module

public import Sheaf.AlgebraicGeometry.PicardExternalCechCupBidegree
import all Sheaf.Paper.CechCupProduct

/-! # The external Alexander--Whitney differential calculation
Source: Stacks Project, Tags 0BED and 07MB.
(blueprint: lem-sc-picard-external-cech-cup-differential).
-/

@[expose] public section
universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
variable {k : Type w} [Field k] {X Y : Scheme.{w}}

section

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def pulledSection {Z T : Scheme.{w}} (a : T ⟶ Z) (M : Z.Modules)
    (Q : Z.Opens) (W : T.Opens) (h : W ≤ a ⁻¹ᵁ Q) (s : Γ(M, Q)) :
    Γ((tensorPullback a).obj M, W) :=
  ((tensorPullback a).obj M).presheaf.map (homOfLE h).op
    (((Classical.choose (exists_tensorPullbackAdjunction a)).unit.app M).val.app (op Q) s)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma pulledSection_restrict {Z T : Scheme.{w}} (a : T ⟶ Z) (M : Z.Modules)
    (Q Q' : Z.Opens) (W : T.Opens) (h : W ≤ a ⁻¹ᵁ Q) (h' : Q ≤ Q')
    (s : Γ(M, Q')) :
    pulledSection a M Q W h (M.presheaf.map (homOfLE h').op s) =
      pulledSection a M Q' W (h.trans ((TopologicalSpace.Opens.map a.base).monotone h')) s := by
  unfold pulledSection
  have hn := PresheafOfModules.naturality_apply
    (((Classical.choose (exists_tensorPullbackAdjunction a)).unit.app M).val)
    (homOfLE h').op s
  change _ = ((tensorPullback a).obj M).presheaf.map
    (homOfLE ((TopologicalSpace.Opens.map a.base).monotone h')).op
      (((Classical.choose (exists_tensorPullbackAdjunction a)).unit.app M).val.app (op Q') s)
    at hn
  refine (congrArg
    (fun z ↦ ((tensorPullback a).obj M).presheaf.map (homOfLE h).op z) hn).trans ?_
  exact TopCat.Presheaf.map_homOfLE_map_homOfLE_apply _ _ _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma pulledSection_map {Z T : Scheme.{w}} (a : T ⟶ Z) (M : Z.Modules)
    (Q : Z.Opens) (W W' : T.Opens) (h : W ≤ a ⁻¹ᵁ Q) (h' : W' ≤ W)
    (s : Γ(M, Q)) :
    ((tensorPullback a).obj M).presheaf.map (homOfLE h').op
        (pulledSection a M Q W h s) = pulledSection a M Q W' (h'.trans h) s := by
  unfold pulledSection
  exact TopCat.Presheaf.map_homOfLE_map_homOfLE_apply _ _ _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma scalarEquiv_d {Z : Scheme.{w}} (t : Z ⟶ Spec (CommRingCat.of k))
    {μ : Type w} (A : μ → Z.Opens) (M : Z.Modules) (n : ℕ)
    (a : ((picardCechFunctor t A).obj M).X n) (y : Fin (n + 2) → μ) :
    TopCat.Presheaf.cechComplexFunctorXAddEquiv A (scalarPresheaf t M) (n + 1)
        (((picardCechFunctor t A).obj M).d n (n + 1) a) y =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        M.presheaf.map (cupFaceRestriction A y i.succAbove).op
          (TopCat.Presheaf.cechComplexFunctorXAddEquiv A (scalarPresheaf t M) n a
            (y ∘ i.succAbove)) := by
  have h := (congrArg (fun f ↦ f a y)
    ((TopCat.Presheaf.cechComplexFunctorIso A (scalarPresheaf t M)).hom.comm
      n (n + 1))).symm
  change TopCat.Presheaf.cechComplexFunctorXAddEquiv A (scalarPresheaf t M) (n + 1)
    (((picardCechFunctor t A).obj M).d n (n + 1) a) y =
      ((TopCat.Presheaf.cechComplex A).obj
        (scalarPresheaf t M ⋙ forget₂ (ModuleCat _) AddCommGrpCat)).d n (n + 1)
          (TopCat.Presheaf.cechComplexFunctorXAddEquiv A (scalarPresheaf t M) n a) y at h
  rw [TopCat.Presheaf.cechComplex_d_apply] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def pulledFace {Z T : Scheme.{w}} (a : T ⟶ Z) {μ ν : Type w}
    (A : μ → Z.Opens) (W : ν → T.Opens) (v : ν → μ)
    (hw : ∀ i, W i ≤ a ⁻¹ᵁ A (v i)) (M : Z.Modules) {m n : ℕ}
    (c : ∀ z : Fin m → μ, Γ(M, ⨅ i, A (z i))) (y : Fin n → ν)
    (face : Fin m → Fin n) : Γ((tensorPullback a).obj M, ⨅ i, W (y i)) :=
  pulledSection a M (⨅ i, A (v (y (face i)))) (⨅ i, W (y i))
    (by
      intro x hx
      change a.base x ∈ ⨅ i, A (v (y (face i)))
      rw [← SetLike.mem_coe, TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
      intro i
      exact hw (y (face i)) (iInf_le (fun j ↦ W (y j)) (face i) hx))
    (c (fun i ↦ v (y (face i))))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma pulledFace_d {Z T : Scheme.{w}} (a : T ⟶ Z)
    (t : Z ⟶ Spec (CommRingCat.of k)) {μ ν : Type w}
    (A : μ → Z.Opens) (W : ν → T.Opens) (v : ν → μ)
    (hw : ∀ i, W i ≤ a ⁻¹ᵁ A (v i)) (M : Z.Modules) (m n : ℕ)
    (c : ((picardCechFunctor t A).obj M).X m) (y : Fin n → ν)
    (face : Fin (m + 2) → Fin n) :
    pulledFace a A W v hw M
        (TopCat.Presheaf.cechComplexFunctorXAddEquiv A (scalarPresheaf t M) (m + 1)
          (((picardCechFunctor t A).obj M).d m (m + 1) c)) y face =
      ∑ i : Fin (m + 2), (-1 : ℤ) ^ i.val • pulledFace a A W v hw M
        (TopCat.Presheaf.cechComplexFunctorXAddEquiv A (scalarPresheaf t M) m c)
        y (face ∘ i.succAbove) := by
  unfold pulledFace
  rw [scalarEquiv_d]
  unfold pulledSection
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_zsmul, map_zsmul]
  apply congrArg (((-1 : ℤ) ^ i.val) • ·)
  exact pulledSection_restrict _ _ _ _ _ _ _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma aw_faces_sum {A B C : Type*} [AddCommGroup C] (p q : ℕ)
    (L : (Fin (p + 1) → Fin (p + q + 2)) → A)
    (R : (Fin (q + 1) → Fin (p + q + 2)) → B) (pair : A → B → C) :
    (∑ i : Fin (p + q + 2), (-1 : ℤ) ^ i.val •
      pair (L (i.succAbove ∘ cupFront p q)) (R (i.succAbove ∘ cupBack p q))) =
    (∑ i : Fin (p + 2), (-1 : ℤ) ^ i.val •
      pair (L (Fin.cast (by omega) ∘ cupFront (p + 1) q ∘ i.succAbove))
        (R (Fin.cast (by omega) ∘ cupBack (p + 1) q))) +
    (-1 : ℤ) ^ p • (∑ j : Fin (q + 2), (-1 : ℤ) ^ j.val •
      pair (L (Fin.cast (by omega) ∘ cupFront p (q + 1)))
        (R (Fin.cast (by omega) ∘ cupBack p (q + 1) ∘ j.succAbove))) := by
  apply aw_sum p q
  · intro i
    apply congrArg₂ pair
    · apply congrArg L
      funext k
      apply Fin.ext
      simp only [Function.comp_apply, cupFront, Fin.succAbove, Fin.lt_def,
        Fin.val_castSucc, Fin.val_cast]
      split_ifs <;> simp_all
    · apply congrArg R
      funext k
      apply Fin.ext
      simp only [Function.comp_apply, cupBack, Fin.succAbove, Fin.lt_def,
        Fin.val_castSucc, Fin.val_cast]
      split_ifs <;> simp_all <;> omega
  · intro j
    apply congrArg₂ pair
    · apply congrArg L
      funext k
      apply Fin.ext
      simp only [Function.comp_apply, cupFront, Fin.succAbove, Fin.lt_def,
        Fin.val_castSucc, Fin.val_cast]
      split_ifs <;> simp_all
      omega
    · apply congrArg R
      funext k
      apply Fin.ext
      simp only [Function.comp_apply, cupBack, Fin.succAbove, Fin.lt_def,
        Fin.val_castSucc, Fin.val_cast]
      split_ifs <;> simp_all <;> omega
  · apply congrArg₂ pair
    · apply congrArg L
      funext k
      apply Fin.ext
      simp only [Function.comp_apply, cupFront, Fin.succAbove, Fin.lt_def,
        Fin.val_castSucc, Fin.val_cast]
      split_ifs <;> simp_all
      omega
    · apply congrArg R
      funext k
      apply Fin.ext
      simp only [Function.comp_apply, cupBack, Fin.succAbove, Fin.lt_def,
        Fin.val_castSucc, Fin.val_cast]
      split_ifs <;> simp_all
      omega

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma scalarEquiv_cast {Z : Scheme.{w}} (t : Z ⟶ Spec (CommRingCat.of k))
    {μ : Type w} (A : μ → Z.Opens) (M : Z.Modules) {m n : ℕ} (h : m = n)
    (c : ((picardCechFunctor t A).obj M).X m) (y : Fin (n + 1) → μ) :
    TopCat.Presheaf.cechComplexFunctorXAddEquiv A (scalarPresheaf t M) n
      (eqToHom (congrArg (fun i ↦ ((picardCechFunctor t A).obj M).X i) h) c) y =
    M.presheaf.map (cupFaceRestriction A y
      (Fin.cast (congrArg (fun i ↦ i + 1) h))).op
      (TopCat.Presheaf.cechComplexFunctorXAddEquiv A (scalarPresheaf t M) m c
        (y ∘ Fin.cast (congrArg (fun i ↦ i + 1) h))) := by
  subst n
  dsimp only [eqToHom_refl]
  exact (TopCat.Presheaf.map_homOfLE_self_apply M.presheaf _ _).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma externalFace_cup
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    {ι κ : Type w} (U : ι → X.Opens) (V : κ → Y.Opens) (F : X.Modules) (G : Y.Modules)
    (l : ∀ p q : ℕ, ((curriedTensor (ModuleCat.{w} k)).obj
        (((picardCechFunctor f U).obj F).X p)).obj
          (((picardCechFunctor g V).obj G).X q) ⟶
      ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G)).X (p + q))
    (hl : ∀ p q, IsPicardExternalCechCupBidegree f g U V F G p q (l p q))
    (p q n : ℕ) (a : ((picardCechFunctor f U).obj F).X p) (b : ((picardCechFunctor g V).obj G).X q)
    (y : Fin n → ι × κ) (face : Fin (p + q + 1) → Fin n) :
    (externalCupCoefficients f g F G).presheaf.map
      (cupFaceRestriction (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2) y face).op
      (TopCat.Presheaf.cechComplexFunctorXAddEquiv
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2) (scalarPresheaf (pullback.fst f g ≫ f)
          (externalCupCoefficients f g F G)) (p + q) (l p q (a ⊗ₜ[k] b)) (y ∘ face)) =
      let W := (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)
      tmulSection
        (pulledFace (pullback.fst f g) U W Prod.fst (fun _ij ↦ inf_le_left) F
          (TopCat.Presheaf.cechComplexFunctorXAddEquiv U (scalarPresheaf f F) p a)
          y (face ∘ cupFront p q))
        (pulledFace (pullback.snd f g) V W Prod.snd (fun _ij ↦ inf_le_right) G
          (TopCat.Presheaf.cechComplexFunctorXAddEquiv V (scalarPresheaf g G) q b)
          y (face ∘ cupBack p q)) := by
  rw [hl p q a b (y ∘ face)]
  erw [tmulSection_map]
  apply congrArg₂ tmulSection
  · exact pulledSection_map _ _ _ _ _ _ _ _
  · exact pulledSection_map _ _ _ _ _ _ _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma externalCup_leibniz
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    {ι κ : Type w} (U : ι → X.Opens) (V : κ → Y.Opens) (F : X.Modules) (G : Y.Modules)
    (l : ∀ p q : ℕ, ((curriedTensor (ModuleCat.{w} k)).obj
        (((picardCechFunctor f U).obj F).X p)).obj
          (((picardCechFunctor g V).obj G).X q) ⟶
      ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G)).X (p + q))
    (hl : ∀ p q, IsPicardExternalCechCupBidegree f g U V F G p q (l p q))
    (p q : ℕ) (a : ((picardCechFunctor f U).obj F).X p) (b : ((picardCechFunctor g V).obj G).X q) :
    ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G)).d
        (p + q) (p + q + 1) (l p q (a ⊗ₜ[k] b)) =
      (eqToHom (congrArg (fun n ↦ ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G)).X n)
        (Nat.add_right_comm p 1 q)))
        (l (p + 1) q (((picardCechFunctor f U).obj F).d p (p + 1) a ⊗ₜ[k] b)) +
      (-1 : ℤ) ^ p • (eqToHom (congrArg (fun n ↦ ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G)).X n)
        (Nat.add_assoc p q 1).symm))
        (l p (q + 1) (a ⊗ₜ[k] ((picardCechFunctor g V).obj G).d q (q + 1) b)) := by
  let W := (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)
  apply (TopCat.Presheaf.cechComplexFunctorXAddEquiv W
    (scalarPresheaf (pullback.fst f g ≫ f) (externalCupCoefficients f g F G))
    (p + q + 1)).injective
  simp only [map_add, map_zsmul]
  funext y
  rw [scalarEquiv_d]
  simp only [Pi.add_apply, Pi.smul_apply]
  rw [scalarEquiv_cast (pullback.fst f g ≫ f) W (externalCupCoefficients f g F G)
      (Nat.add_right_comm p 1 q),
    scalarEquiv_cast (pullback.fst f g ≫ f) W (externalCupCoefficients f g F G)
      (Nat.add_assoc p q 1).symm]
  conv_lhs =>
    arg 2
    ext i
    arg 2
    erw [externalFace_cup f g U V F G l hl]
  erw [externalFace_cup f g U V F G l hl, externalFace_cup f g U V F G l hl]
  change _ =
    tmulSection
      (pulledFace (pullback.fst f g) U W Prod.fst (fun _ij ↦ inf_le_left) F
        (TopCat.Presheaf.cechComplexFunctorXAddEquiv U (scalarPresheaf f F) (p + 1)
          (((picardCechFunctor f U).obj F).d p (p + 1) a))
        y (Fin.cast _ ∘ cupFront (p + 1) q))
      (pulledFace (pullback.snd f g) V W Prod.snd (fun _ij ↦ inf_le_right) G
        (TopCat.Presheaf.cechComplexFunctorXAddEquiv V (scalarPresheaf g G) q b)
        y (Fin.cast _ ∘ cupBack (p + 1) q)) +
    (-1 : ℤ) ^ p • tmulSection
      (pulledFace (pullback.fst f g) U W Prod.fst (fun _ij ↦ inf_le_left) F
        (TopCat.Presheaf.cechComplexFunctorXAddEquiv U (scalarPresheaf f F) p a)
        y (Fin.cast _ ∘ cupFront p (q + 1)))
      (pulledFace (pullback.snd f g) V W Prod.snd (fun _ij ↦ inf_le_right) G
        (TopCat.Presheaf.cechComplexFunctorXAddEquiv V (scalarPresheaf g G) (q + 1)
          (((picardCechFunctor g V).obj G).d q (q + 1) b))
        y (Fin.cast _ ∘ cupBack p (q + 1)))
  rw [pulledFace_d, pulledFace_d, tmul_sum_left, tmul_sum_right]
  exact aw_faces_sum p q
    (pulledFace (pullback.fst f g) U W Prod.fst (fun _ij ↦ inf_le_left) F
      (TopCat.Presheaf.cechComplexFunctorXAddEquiv U (scalarPresheaf f F) p a) y)
    (pulledFace (pullback.snd f g) V W Prod.snd (fun _ij ↦ inf_le_right) G
      (TopCat.Presheaf.cechComplexFunctorXAddEquiv V (scalarPresheaf g G) q b) y)
    tmulSection

end

/-- Assemble specified bidegree maps by the tensor-total coproduct universal property.
Source: Stacks Project, Tag 0BED, equation-kunneth-on-cech.
(blueprint: lem-sc-picard-external-cech-cup-differential-coordinate). -/
def picardExternalCechCupDegreeMaps
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    {ι κ : Type w} (U : ι → X.Opens) (V : κ → Y.Opens) (F : X.Modules) (G : Y.Modules)
    (l : ∀ p q : ℕ, ((curriedTensor (ModuleCat.{w} k)).obj
        (((picardCechFunctor f U).obj F).X p)).obj
          (((picardCechFunctor g V).obj G).X q) ⟶
      ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G)).X (p + q)) :
    ∀ n : ℕ, (HomologicalComplex.mapBifunctor ((picardCechFunctor f U).obj F)
        ((picardCechFunctor g V).obj G) (curriedTensor (ModuleCat.{w} k))
          (ComplexShape.up ℕ)).X n ⟶ ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G)).X n :=
  fun _n ↦ HomologicalComplex.mapBifunctorDesc
    (fun p q hpq ↦ l p q ≫ eqToHom (congrArg
      (fun j ↦ ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G)).X j) hpq))

/-- Each specified bidegree map is recovered by its tensor-total inclusion.
Source: the coproduct universal property, Stacks Project Tag 0BED.
(blueprint: lem-sc-picard-external-cech-cup-differential). -/
theorem picardExternalCechCupDegreeMaps_ι
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    {ι κ : Type w} (U : ι → X.Opens) (V : κ → Y.Opens) (F : X.Modules) (G : Y.Modules)
    (l : ∀ p q : ℕ, ((curriedTensor (ModuleCat.{w} k)).obj
        (((picardCechFunctor f U).obj F).X p)).obj
          (((picardCechFunctor g V).obj G).X q) ⟶
      ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G)).X (p + q))
    (p q : ℕ) :
    HomologicalComplex.ιMapBifunctor ((picardCechFunctor f U).obj F)
      ((picardCechFunctor g V).obj G) (curriedTensor (ModuleCat.{w} k))
        (ComplexShape.up ℕ) p q (p + q) rfl ≫
      picardExternalCechCupDegreeMaps f g U V F G l (p + q) = l p q := by
  dsimp only [picardExternalCechCupDegreeMaps]
  rw [HomologicalComplex.ι_mapBifunctorDesc]
  simp

/- Adjacent differential compatibility. -/
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Coordinate differential compatibility for one tensor-total summand.
Source: Stacks Project, Tag 07MB; this is the inclusion-level calculation
used to assemble the total differential identity.
(blueprint: lem-sc-picard-external-cech-cup-differential-coordinate).
Proof: Substitute hpq to work in degree p+q. Tensor-product extensionality reduces the equality
to a pure tensor a tensor b, and Cech product extensionality reduces it to a tuple y of length
p+q+2. Use the degree-map inclusion equation and hl to identify the target coordinates.
Naturality of each pullback adjunction unit identifies pulling a restricted section with
restricting its pullback; presheaf composition identifies successive restrictions, and tensor
sections commute with restriction. In d(a) cup b, the omitted-front terms indexed j=0,...,p
have coefficient (-1)^j and match target faces j=0,...,p. Its final term has coefficient
(-1)^(p+1). In (-1)^p a cup d(b), the first back term has coefficient (-1)^p and is the same
restricted tensor section as that final front term, so they cancel. The remaining back terms
indexed r=1,...,q+1 have coefficient (-1)^(p+r) and match target faces j=p+1,...,p+q+1. These
exhaust the target alternating differential. The tensor-total inclusion differential has
precisely the d(a) tensor b term and the (-1)^p a tensor d(b) term; its inclusion formulas and
the degree-map inclusion equation therefore give the same coordinates. Tensor and product
extensionality conclude the summand equality. The cancellation also applies when p=0 or q=0 and
in characteristic two. Empty index families give vacuous coordinate equalities; zero
coefficients give zero maps. -/
theorem picardExternalCechCupDegreeMaps_comm_ι
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    {ι κ : Type w} (U : ι → X.Opens) (V : κ → Y.Opens) (F : X.Modules) (G : Y.Modules)
    (l : ∀ p q : ℕ, ((curriedTensor (ModuleCat.{w} k)).obj
        (((picardCechFunctor f U).obj F).X p)).obj
          (((picardCechFunctor g V).obj G).X q) ⟶
      ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G)).X (p + q))
    (hl : ∀ p q, IsPicardExternalCechCupBidegree f g U V F G p q (l p q))
    (n p q : ℕ) (hpq : p + q = n) :
    HomologicalComplex.ιMapBifunctor ((picardCechFunctor f U).obj F)
      ((picardCechFunctor g V).obj G) (curriedTensor (ModuleCat.{w} k))
        (ComplexShape.up ℕ) p q n hpq ≫
      picardExternalCechCupDegreeMaps f g U V F G l n ≫
      ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G)).d n (n + 1) =
    HomologicalComplex.ιMapBifunctor ((picardCechFunctor f U).obj F)
      ((picardCechFunctor g V).obj G) (curriedTensor (ModuleCat.{w} k))
        (ComplexShape.up ℕ) p q n hpq ≫
      (HomologicalComplex.mapBifunctor ((picardCechFunctor f U).obj F)
        ((picardCechFunctor g V).obj G) (curriedTensor (ModuleCat.{w} k))
          (ComplexShape.up ℕ)).d n (n + 1) ≫
      picardExternalCechCupDegreeMaps f g U V F G l (n + 1) := by
  subst n
  rw [← Category.assoc, picardExternalCechCupDegreeMaps_ι]
  simp only [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    Preadditive.add_comp, HomologicalComplex.mapBifunctor.ι_D₁_assoc,
    HomologicalComplex.mapBifunctor.ι_D₂_assoc]
  rw [HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ (by rfl) q (p + q + 1)
      (by dsimp; omega),
    HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ p (by rfl) (p + q + 1)
      (by dsimp; omega)]
  simp only [Linear.units_smul_comp, Category.assoc]
  dsimp only [picardExternalCechCupDegreeMaps]
  rw [HomologicalComplex.ι_mapBifunctorDesc, HomologicalComplex.ι_mapBifunctorDesc]
  have hε₁ : ComplexShape.ε₁ (ComplexShape.up ℕ) (ComplexShape.up ℕ)
      (ComplexShape.up ℕ) (p, q) = 1 := rfl
  have hε₂ : ComplexShape.ε₂ (ComplexShape.up ℕ) (ComplexShape.up ℕ)
      (ComplexShape.up ℕ) (p, q) = (-1 : ℤˣ) ^ p := rfl
  rw [hε₁, hε₂]
  simp only [one_smul, Units.smul_def, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro a b
  exact externalCup_leibniz f g U V F G l hl p q a b

end
end AlgebraicGeometry.Scheme.Modules
