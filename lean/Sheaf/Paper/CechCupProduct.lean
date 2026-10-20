/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.Paper.ModuleCohomologyCupProduct
import Mathlib.LinearAlgebra.Quotient.Bilinear
import Mathlib.Algebra.BigOperators.Fin

/-! # The Cech cup product

Source: Stacks Project, Cohomology, Tag 07MB
(blueprint: def-sc-cech-cup-product).
For coefficient sheaves in degree zero the total-complex sign is +1 on each
Alexander--Whitney component; the differential still has the signed Leibniz rule.
-/

@[expose] public section

universe uC
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- The front face of a tuple for the Alexander--Whitney product.
Source: Stacks, Tag 07MB (blueprint: def-sc-cech-cup-product). -/
def cupFront (p q : ℕ) : Fin (p + 1) → Fin (p + q + 1) :=
  fun i ↦ ⟨i.val, by omega⟩

/-- The back face, sharing the vertex of index p with the front face.
Source: Stacks, Tag 07MB (blueprint: def-sc-cech-cup-product). -/
def cupBack (p q : ℕ) : Fin (q + 1) → Fin (p + q + 1) :=
  fun j ↦ ⟨p + j.val, by omega⟩

/-- Restriction to a face intersection; tuples may have repeated indices.
Source: Stacks, Tag 07MB (blueprint: def-sc-cech-cup-product). -/
def cupFaceRestriction {X : Scheme.{uC}} {ι : Type uC} (U : ι → X.Opens)
    {n m : ℕ} (y : Fin n → ι) (face : Fin m → Fin n) :
    (⨅ i, U (y i)) ⟶ (⨅ j, U (y (face j))) :=
  homOfLE (le_iInf fun j ↦ iInf_le (fun i ↦ U (y i)) (face j))

/-- The cochain cup product: restrict the front and back factors to the common
intersection and tensor their sections. For sheaves in degree zero this is precisely
the component of the signed total tensor map of Tag 07MB.
Source: Stacks, Tag 07MB (blueprint: def-sc-cech-cup-product). -/
def cechCupCochain {X : Scheme.{uC}} {ι : Type uC} (U : ι → X.Opens)
    (F G : X.Modules) (p q : ℕ)
    (a : ((cechComplexFunctor U).obj F.presheafModuleCat).X p)
    (b : ((cechComplexFunctor U).obj G.presheafModuleCat).X q) :
    ((cechComplexFunctor U).obj (F ⊗ G).presheafModuleCat).X (p + q) :=
  (TopCat.Presheaf.cechComplexFunctorXAddEquiv U (F ⊗ G).presheafModuleCat (p + q)).symm
    (fun y ↦ tmulSection
      (F.presheaf.map (cupFaceRestriction U y (cupFront p q)).op
        (TopCat.Presheaf.cechComplexFunctorXAddEquiv U F.presheafModuleCat p a
          (y ∘ cupFront p q)))
      (G.presheaf.map (cupFaceRestriction U y (cupBack p q)).op
        (TopCat.Presheaf.cechComplexFunctorXAddEquiv U G.presheafModuleCat q b
          (y ∘ cupBack p q))))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def faceSection {X : Scheme.{uC}} {ι : Type uC} (U : ι → X.Opens)
    (F : X.Modules) {m n : ℕ} (c : ∀ y : Fin m → ι, Γ(F, ⨅ i, U (y i)))
    (y : Fin n → ι) (face : Fin m → Fin n) : Γ(F, ⨅ i, U (y i)) :=
  F.presheaf.map (cupFaceRestriction U y face).op (c (y ∘ face))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma faceSection_comp {X : Scheme.{uC}} {ι : Type uC} (U : ι → X.Opens)
    (F : X.Modules) {m n k : ℕ} (c : ∀ y : Fin m → ι, Γ(F, ⨅ i, U (y i)))
    (y : Fin n → ι) (face : Fin k → Fin n) (face' : Fin m → Fin k) :
    F.presheaf.map (cupFaceRestriction U y face).op
      (faceSection U F c (y ∘ face) face') = faceSection U F c y (face ∘ face') := by
  dsimp only [faceSection]
  exact TopCat.Presheaf.map_homOfLE_map_homOfLE_apply F.presheaf _ _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma eq_cast {X : Scheme.{uC}} {ι : Type uC} (U : ι → X.Opens)
    (F : X.Modules) {m n : ℕ} (h : m = n)
    (c : ((cechComplexFunctor U).obj F.presheafModuleCat).X m)
    (y : Fin (n + 1) → ι) :
    TopCat.Presheaf.cechComplexFunctorXAddEquiv U F.presheafModuleCat n
      (eqToHom (congrArg (fun i ↦ ((cechComplexFunctor U).obj F.presheafModuleCat).X i)
        h) c) y =
      faceSection U F
        (TopCat.Presheaf.cechComplexFunctorXAddEquiv U F.presheafModuleCat m c)
        y (Fin.cast (congrArg (fun i ↦ i + 1) h)) := by
  subst n
  dsimp only [eqToHom_refl]
  change TopCat.Presheaf.cechComplexFunctorXAddEquiv U F.presheafModuleCat m c y =
    F.presheaf.map (𝟙 (op (⨅ i, U (y i))))
      (TopCat.Presheaf.cechComplexFunctorXAddEquiv U F.presheafModuleCat m c y)
  exact (ConcreteCategory.congr_hom (F.presheaf.map_id _) _).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma equiv_d {X : Scheme.{uC}} {ι : Type uC} (U : ι → X.Opens)
    (F : X.Modules) (n : ℕ)
    (a : ((cechComplexFunctor U).obj F.presheafModuleCat).X n)
    (y : Fin (n + 2) → ι) :
    TopCat.Presheaf.cechComplexFunctorXAddEquiv U F.presheafModuleCat (n + 1)
      (((cechComplexFunctor U).obj F.presheafModuleCat).d n (n + 1) a) y =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        F.presheaf.map (cupFaceRestriction U y i.succAbove).op
          (TopCat.Presheaf.cechComplexFunctorXAddEquiv U F.presheafModuleCat n a
            (y ∘ i.succAbove)) := by
  have h := (congrArg (fun f ↦ f a y)
    ((TopCat.Presheaf.cechComplexFunctorIso U F.presheafModuleCat).hom.comm n (n + 1))).symm
  change TopCat.Presheaf.cechComplexFunctorXAddEquiv U F.presheafModuleCat (n + 1)
    (((cechComplexFunctor U).obj F.presheafModuleCat).d n (n + 1) a) y =
      ((TopCat.Presheaf.cechComplex U).obj
        (F.presheafModuleCat ⋙ forget₂ (ModuleCat _) AddCommGrpCat)).d n (n + 1)
          (TopCat.Presheaf.cechComplexFunctorXAddEquiv U F.presheafModuleCat n a) y at h
  rw [TopCat.Presheaf.cechComplex_d_apply] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma faceSection_d {X : Scheme.{uC}} {ι : Type uC} (U : ι → X.Opens)
    (F : X.Modules) (m n : ℕ)
    (a : ((cechComplexFunctor U).obj F.presheafModuleCat).X m)
    (y : Fin n → ι) (face : Fin (m + 2) → Fin n) :
    faceSection U F
        (TopCat.Presheaf.cechComplexFunctorXAddEquiv U F.presheafModuleCat (m + 1)
          (((cechComplexFunctor U).obj F.presheafModuleCat).d m (m + 1) a)) y face =
      ∑ i : Fin (m + 2), (-1 : ℤ) ^ i.val • faceSection U F
        (TopCat.Presheaf.cechComplexFunctorXAddEquiv U F.presheafModuleCat m a)
        y (face ∘ i.succAbove) := by
  unfold faceSection
  rw [equiv_d, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_zsmul]
  exact congrArg ((-1 : ℤ) ^ i.val • ·)
    (faceSection_comp U F _ y face i.succAbove)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma faceSection_cup {X : Scheme.{uC}} {ι : Type uC} (U : ι → X.Opens)
    (F G : X.Modules) (p q n : ℕ)
    (a : ((cechComplexFunctor U).obj F.presheafModuleCat).X p)
    (b : ((cechComplexFunctor U).obj G.presheafModuleCat).X q)
    (y : Fin n → ι) (face : Fin (p + q + 1) → Fin n) :
    faceSection U (F ⊗ G)
        (TopCat.Presheaf.cechComplexFunctorXAddEquiv U (F ⊗ G).presheafModuleCat (p + q)
          (cechCupCochain U F G p q a b)) y face =
      tmulSection
        (faceSection U F
          (TopCat.Presheaf.cechComplexFunctorXAddEquiv U F.presheafModuleCat p a)
          y (face ∘ cupFront p q))
        (faceSection U G
          (TopCat.Presheaf.cechComplexFunctorXAddEquiv U G.presheafModuleCat q b)
          y (face ∘ cupBack p q)) := by
  simp only [faceSection, cechCupCochain, AddEquiv.apply_symm_apply]
  exact (tmulSection_map (cupFaceRestriction U y face).le _ _).trans
    (congrArg₂ tmulSection (faceSection_comp U F _ y face (cupFront p q))
      (faceSection_comp U G _ y face (cupBack p q)))


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma aw_sum {A : Type*} [AddCommGroup A] (p q : ℕ)
    (L : Fin (p + 2) → A) (R : Fin (q + 2) → A) (S : Fin (p + q + 2) → A)
    (hl : ∀ i : Fin (p + 1), S ⟨i.val, by omega⟩ = L i.castSucc)
    (hr : ∀ j : Fin (q + 1), S ⟨p + 1 + j.val, by omega⟩ = R j.succ)
    (hm : L (Fin.last (p + 1)) = R 0) :
    (∑ i, (-1 : ℤ) ^ i.val • S i) =
      (∑ i, (-1 : ℤ) ^ i.val • L i) + (-1 : ℤ) ^ p • ∑ j, (-1 : ℤ) ^ j.val • R j := by
  have hn : (p + 1) + (q + 1) = p + q + 2 := by omega
  have hd : (∑ i, (-1 : ℤ) ^ i.val • S i) =
      (∑ i : Fin (p + 1), (-1 : ℤ) ^ i.val • L i.castSucc) +
        ∑ j : Fin (q + 1), (-1 : ℤ) ^ (p + 1 + j.val) • R j.succ := by
    rw [← Fin.sum_congr' (fun i ↦ (-1 : ℤ) ^ i.val • S i) hn, Fin.sum_univ_add]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      exact congrArg ((-1 : ℤ) ^ i.val • ·) (hl i)
    · apply Finset.sum_congr rfl
      intro j _
      exact congrArg ((-1 : ℤ) ^ (p + 1 + j.val) • ·) (hr j)
  rw [hd, Fin.sum_univ_castSucc (fun i : Fin (p + 2) ↦ (-1 : ℤ) ^ i.val • L i),
    Fin.sum_univ_succ (fun j : Fin (q + 2) ↦ (-1 : ℤ) ^ j.val • R j)]
  simp only [Fin.val_castSucc, Fin.val_last, Fin.val_zero, pow_zero, one_smul,
    Fin.val_succ, hm, smul_add, Finset.smul_sum]
  have ht : (∑ j : Fin (q + 1), (-1 : ℤ) ^ (p + 1 + j.val) • R j.succ) =
      ∑ j : Fin (q + 1), (-1 : ℤ) ^ p • ((-1 : ℤ) ^ (j.val + 1) • R j.succ) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [← mul_smul, ← pow_add]
    congr 2
    omega
  rw [ht, pow_succ', mul_smul, neg_one_zsmul]
  abel

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma tmul_sum_left {X : Scheme.{uC}} (F G : X.Modules) (V : X.Opens)
    (n : ℕ) (a : Fin n → Γ(F, V)) (b : Γ(G, V)) :
    tmulSection (∑ i, (-1 : ℤ) ^ i.val • a i) b =
      ∑ i, (-1 : ℤ) ^ i.val • tmulSection (a i) b := by
  let f : Γ(F, V) →+ Γ(F ⊗ G, V) :=
    { toFun := (tmulSection · b)
      map_zero' := zero_tmulSection b
      map_add' := fun x x' ↦ add_tmulSection x x' b }
  change f (∑ i, (-1 : ℤ) ^ i.val • a i) = _
  rw [map_sum]
  exact Finset.sum_congr rfl (fun i _ ↦ f.map_zsmul ((-1 : ℤ) ^ i.val) (a i))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma tmul_sum_right {X : Scheme.{uC}} (F G : X.Modules) (V : X.Opens)
    (n : ℕ) (a : Γ(F, V)) (b : Fin n → Γ(G, V)) :
    tmulSection a (∑ i, (-1 : ℤ) ^ i.val • b i) =
      ∑ i, (-1 : ℤ) ^ i.val • tmulSection a (b i) := by
  let f : Γ(G, V) →+ Γ(F ⊗ G, V) :=
    { toFun := tmulSection a
      map_zero' := tmulSection_zero a
      map_add' := fun y y' ↦ tmulSection_add a y y' }
  change f (∑ i, (-1 : ℤ) ^ i.val • b i) = _
  rw [map_sum]
  exact Finset.sum_congr rfl (fun i _ ↦ f.map_zsmul ((-1 : ℤ) ^ i.val) (b i))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The signed Leibniz identity makes the cochain pairing a map out of the total
 tensor complex. In degree zero the sign on the second differential is +1.
Source: Stacks, Tag 07MB (blueprint: def-sc-cech-cup-product).
Proof: expand the alternating restriction differential. Faces lying entirely in the
front or back factors give the two displayed terms; the shared-vertex terms cancel.
The remaining back terms have the sign (-1)^p. Restriction commutes with tensor
sections, so this calculation is valid on every intersection. -/
theorem cechCupCochain_leibniz {X : Scheme.{uC}} {ι : Type uC} (U : ι → X.Opens)
    (F G : X.Modules) (p q : ℕ)
    (a : ((cechComplexFunctor U).obj F.presheafModuleCat).X p)
    (b : ((cechComplexFunctor U).obj G.presheafModuleCat).X q) :
    ((cechComplexFunctor U).obj (F ⊗ G).presheafModuleCat).d
        (p + q) (p + q + 1) (cechCupCochain U F G p q a b) =
      (eqToHom (congrArg
        (fun n ↦ ((cechComplexFunctor U).obj (F ⊗ G).presheafModuleCat).X n)
        (Nat.add_right_comm p 1 q)))
          (cechCupCochain U F G (p + 1) q
            (((cechComplexFunctor U).obj F.presheafModuleCat).d p (p + 1) a) b) +
      (-1 : ℤ) ^ p • (eqToHom (congrArg
        (fun n ↦ ((cechComplexFunctor U).obj (F ⊗ G).presheafModuleCat).X n)
        (Nat.add_assoc p q 1).symm))
          (cechCupCochain U F G p (q + 1) a
            (((cechComplexFunctor U).obj G.presheafModuleCat).d q (q + 1) b)) := by
  apply (TopCat.Presheaf.cechComplexFunctorXAddEquiv
    U (F ⊗ G).presheafModuleCat (p + q + 1)).injective
  simp only [map_add, map_zsmul]
  funext y
  rw [equiv_d]
  simp only [Pi.add_apply, Pi.smul_apply]
  rw [eq_cast U (F ⊗ G) (Nat.add_right_comm p 1 q),
    eq_cast U (F ⊗ G) (Nat.add_assoc p q 1).symm]
  change (∑ i : Fin (p + q + 2), (-1 : ℤ) ^ i.val •
      faceSection U (F ⊗ G)
        (TopCat.Presheaf.cechComplexFunctorXAddEquiv U (F ⊗ G).presheafModuleCat (p + q)
          (cechCupCochain U F G p q a b)) y i.succAbove) = _
  simp_rw [faceSection_cup]
  rw [faceSection_d, faceSection_d]
  rw [tmul_sum_left, tmul_sum_right]
  apply aw_sum p q
  · intro i
    apply congrArg₂ tmulSection
    · apply congrArg (faceSection U F _ y)
      funext k
      apply Fin.ext
      simp only [Function.comp_apply, cupFront, Fin.succAbove, Fin.lt_def,
        Fin.val_castSucc, Fin.val_cast]
      split_ifs <;> simp_all
    · apply congrArg (faceSection U G _ y)
      funext k
      apply Fin.ext
      simp only [Function.comp_apply, cupBack, Fin.succAbove, Fin.lt_def,
        Fin.val_castSucc, Fin.val_cast]
      split_ifs <;> simp_all <;> omega
  · intro j
    apply congrArg₂ tmulSection
    · apply congrArg (faceSection U F _ y)
      funext k
      apply Fin.ext
      simp only [Function.comp_apply, cupFront, Fin.succAbove, Fin.lt_def,
        Fin.val_castSucc, Fin.val_cast]
      split_ifs <;> simp_all
      omega
    · apply congrArg (faceSection U G _ y)
      funext k
      apply Fin.ext
      simp only [Function.comp_apply, cupBack, Fin.succAbove, Fin.lt_def,
        Fin.val_castSucc, Fin.val_cast]
      split_ifs <;> simp_all <;> omega
  · apply congrArg₂ tmulSection
    · apply congrArg (faceSection U F _ y)
      funext k
      apply Fin.ext
      simp only [Function.comp_apply, cupFront, Fin.succAbove, Fin.lt_def,
        Fin.val_castSucc, Fin.val_cast]
      split_ifs <;> simp_all
      omega
    · apply congrArg (faceSection U G _ y)
      funext k
      apply Fin.ext
      simp only [Function.comp_apply, cupBack, Fin.succAbove, Fin.lt_def,
        Fin.val_castSucc, Fin.val_cast]
      split_ifs <;> simp_all
      omega

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def cycleClassLinear {R : Type uC} [Ring R]
    (K : CochainComplex (ModuleCat.{uC} R) ℕ) (n : ℕ) :
    (K.sc n).moduleCatLeftHomologyData.K →ₗ[R] K.homology n :=
  ((K.sc n).moduleCatCyclesIso.inv ≫ (K.sc n).homologyπ).hom

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma cycleClassLinear_surjective {R : Type uC} [Ring R]
    (K : CochainComplex (ModuleCat.{uC} R) ℕ) (n : ℕ) :
    Function.Surjective (cycleClassLinear K n) := by
  exact (ModuleCat.epi_iff_surjective
    ((K.sc n).moduleCatCyclesIso.inv ≫ (K.sc n).homologyπ)).mp inferInstance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma cycleClassLinear_eq_zero {R : Type uC} [Ring R]
    (K : CochainComplex (ModuleCat.{uC} R) ℕ) (n : ℕ)
    (a : (K.sc n).moduleCatLeftHomologyData.K) :
    cycleClassLinear K n a = 0 ↔
      a ∈ LinearMap.range (K.sc n).moduleCatToCycles := by
  have h := (K.sc n).moduleCatCyclesIso_inv_π
  have ha := congrArg (fun f ↦ f a) h
  change cycleClassLinear K n a = _ at ha
  rw [ha]
  change (K.sc n).moduleCatHomologyIso.inv (Submodule.Quotient.mk a) = 0 ↔ _
  rw [← (K.sc n).moduleCatHomologyIso.inv.hom.map_zero]
  exact ((ModuleCat.mono_iff_injective (K.sc n).moduleCatHomologyIso.inv).mp
    inferInstance).eq_iff.trans (Submodule.Quotient.mk_eq_zero _)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma cechEquiv_smul {X : Scheme.{uC}} {ι : Type uC}
    (U : ι → X.Opens) (F : X.Modules) (n : ℕ) (r : Γ(X, ⊤))
    (a : ((cechComplexFunctor U).obj F.presheafModuleCat).X n)
    (y : Fin (n + 1) → ι) :
    TopCat.Presheaf.cechComplexFunctorXAddEquiv U F.presheafModuleCat n (r • a) y =
      r • (show F.presheafModuleCat.obj (op (⨅ i, U (y i))) from
        TopCat.Presheaf.cechComplexFunctorXAddEquiv U F.presheafModuleCat n a y) := by
  simp only [TopCat.Presheaf.cechComplexFunctorXAddEquiv_apply]
  exact _root_.map_smul
    ((F.presheafModuleCat.map _).hom.comp
      (TopCat.Presheaf.cechComplexFunctorπ U F.presheafModuleCat n y).hom) r a

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma cechCupCochain_add_left {X : Scheme.{uC}} {ι : Type uC}
    (U : ι → X.Opens) (F G : X.Modules) (p q : ℕ)
    (a a' : ((cechComplexFunctor U).obj F.presheafModuleCat).X p)
    (b : ((cechComplexFunctor U).obj G.presheafModuleCat).X q) :
    cechCupCochain U F G p q (a + a') b =
      cechCupCochain U F G p q a b + cechCupCochain U F G p q a' b := by
  apply (TopCat.Presheaf.cechComplexFunctorXAddEquiv
    U (F ⊗ G).presheafModuleCat (p + q)).injective
  simp only [cechCupCochain, AddEquiv.apply_symm_apply, map_add]
  funext y
  simp only [Pi.add_apply, map_add, add_tmulSection]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma cechCupCochain_add_right {X : Scheme.{uC}} {ι : Type uC}
    (U : ι → X.Opens) (F G : X.Modules) (p q : ℕ)
    (a : ((cechComplexFunctor U).obj F.presheafModuleCat).X p)
    (b b' : ((cechComplexFunctor U).obj G.presheafModuleCat).X q) :
    cechCupCochain U F G p q a (b + b') =
      cechCupCochain U F G p q a b + cechCupCochain U F G p q a b' := by
  apply (TopCat.Presheaf.cechComplexFunctorXAddEquiv
    U (F ⊗ G).presheafModuleCat (p + q)).injective
  simp only [cechCupCochain, AddEquiv.apply_symm_apply, map_add]
  funext y
  simp only [Pi.add_apply, map_add, tmulSection_add]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma cechCupCochain_smul_left {X : Scheme.{uC}} {ι : Type uC}
    (U : ι → X.Opens) (F G : X.Modules) (p q : ℕ) (r : Γ(X, ⊤))
    (a : ((cechComplexFunctor U).obj F.presheafModuleCat).X p)
    (b : ((cechComplexFunctor U).obj G.presheafModuleCat).X q) :
    cechCupCochain U F G p q (r • a) b = r • cechCupCochain U F G p q a b := by
  apply (TopCat.Presheaf.cechComplexFunctorXAddEquiv
    U (F ⊗ G).presheafModuleCat (p + q)).injective
  funext y
  rw [cechEquiv_smul]
  simp only [cechCupCochain, AddEquiv.apply_symm_apply, cechEquiv_smul]
  change tmulSection (F.presheafModuleCat.map _ (r • _)) _ =
    r • (show (F ⊗ G).presheafModuleCat.obj (op (⨅ i, U (y i))) from tmulSection _ _)
  rw [_root_.map_smul]
  exact smul_tmulSection _ _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma cechCupCochain_smul_right {X : Scheme.{uC}} {ι : Type uC}
    (U : ι → X.Opens) (F G : X.Modules) (p q : ℕ) (r : Γ(X, ⊤))
    (a : ((cechComplexFunctor U).obj F.presheafModuleCat).X p)
    (b : ((cechComplexFunctor U).obj G.presheafModuleCat).X q) :
    cechCupCochain U F G p q a (r • b) = r • cechCupCochain U F G p q a b := by
  apply (TopCat.Presheaf.cechComplexFunctorXAddEquiv
    U (F ⊗ G).presheafModuleCat (p + q)).injective
  funext y
  rw [cechEquiv_smul]
  simp only [cechCupCochain, AddEquiv.apply_symm_apply, cechEquiv_smul]
  change tmulSection _ (G.presheafModuleCat.map _ (r • _)) =
    r • (show (F ⊗ G).presheafModuleCat.obj (op (⨅ i, U (y i))) from tmulSection _ _)
  rw [_root_.map_smul]
  exact tmulSection_smul _ _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def cechCupLinear {X : Scheme.{uC}} {ι : Type uC}
    (U : ι → X.Opens) (F G : X.Modules) (p q : ℕ) :
    ((cechComplexFunctor U).obj F.presheafModuleCat).X p →ₗ[Γ(X, ⊤)]
      ((cechComplexFunctor U).obj G.presheafModuleCat).X q →ₗ[Γ(X, ⊤)]
        ((cechComplexFunctor U).obj (F ⊗ G).presheafModuleCat).X (p + q) :=
  LinearMap.mk₂ _ (cechCupCochain U F G p q)
    (cechCupCochain_add_left U F G p q) (cechCupCochain_smul_left U F G p q)
    (fun a b b' ↦ cechCupCochain_add_right U F G p q a b b')
    (fun r a b ↦ cechCupCochain_smul_right U F G p q r a b)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma cycle_d_zero {R : Type uC} [Ring R]
    (K : CochainComplex (ModuleCat.{uC} R) ℕ) (n : ℕ)
    (a : (K.sc n).moduleCatLeftHomologyData.K) : K.d n (n + 1) a.val = 0 := by
  have h := a.property
  change K.d n ((ComplexShape.up ℕ).next n) a.val = 0 at h
  rw [(ComplexShape.up ℕ).next_eq' (show n + 1 = n + 1 from rfl)] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma cechCupCochain_cycle {X : Scheme.{uC}} {ι : Type uC}
    (U : ι → X.Opens) (F G : X.Modules) (p q : ℕ)
    (a : (((cechComplexFunctor U).obj F.presheafModuleCat).sc p).moduleCatLeftHomologyData.K)
    (b : (((cechComplexFunctor U).obj G.presheafModuleCat).sc q).moduleCatLeftHomologyData.K) :
    ((cechComplexFunctor U).obj (F ⊗ G).presheafModuleCat).d
      (p + q) (p + q + 1) (cechCupCochain U F G p q a.val b.val) = 0 := by
  rw [cechCupCochain_leibniz, cycle_d_zero, cycle_d_zero]
  have hl : cechCupCochain U F G (p + 1) q 0 b.val = 0 := by
    exact congrArg (fun f ↦ f b.val) (cechCupLinear U F G (p + 1) q).map_zero
  have hr : cechCupCochain U F G p (q + 1) a.val 0 = 0 :=
    (cechCupLinear U F G p (q + 1) a.val).map_zero
  rw [hl, hr]
  simp only [map_zero, smul_zero, add_zero]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def cechCupCycles {X : Scheme.{uC}} {ι : Type uC}
    (U : ι → X.Opens) (F G : X.Modules) (p q : ℕ) :
    (((cechComplexFunctor U).obj F.presheafModuleCat).sc p).moduleCatLeftHomologyData.K
      →ₗ[Γ(X, ⊤)]
    (((cechComplexFunctor U).obj G.presheafModuleCat).sc q).moduleCatLeftHomologyData.K
      →ₗ[Γ(X, ⊤)]
    (((cechComplexFunctor U).obj
      (F ⊗ G).presheafModuleCat).sc (p + q)).moduleCatLeftHomologyData.K :=
  LinearMap.mk₂ _ (fun a b ↦ ⟨cechCupCochain U F G p q a.val b.val, by
    change ((cechComplexFunctor U).obj (F ⊗ G).presheafModuleCat).d
      (p + q) ((ComplexShape.up ℕ).next (p + q))
        (cechCupCochain U F G p q a.val b.val) = 0
    rw [(ComplexShape.up ℕ).next_eq' (show p + q + 1 = p + q + 1 from rfl)]
    exact cechCupCochain_cycle U F G p q a b⟩)
    (fun a a' b ↦ Subtype.ext (cechCupCochain_add_left U F G p q a.val a'.val b.val))
    (fun r a b ↦ Subtype.ext (cechCupCochain_smul_left U F G p q r a.val b.val))
    (fun a b b' ↦ Subtype.ext (cechCupCochain_add_right U F G p q a.val b.val b'.val))
    (fun r a b ↦ Subtype.ext (cechCupCochain_smul_right U F G p q r a.val b.val))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma cycle_mem_range_of_d {R : Type uC} [Ring R]
    (K : CochainComplex (ModuleCat.{uC} R) ℕ) (m n : ℕ) (hn : m + 1 = n)
    (c : (K.sc n).moduleCatLeftHomologyData.K) (x : K.X m)
    (hc : K.d m n x = c.val) : c ∈ LinearMap.range (K.sc n).moduleCatToCycles := by
  have hi : (ComplexShape.up ℕ).prev n = m := (ComplexShape.up ℕ).prev_eq' hn
  refine ⟨(K.XIsoOfEq hi).inv x, Subtype.ext ?_⟩
  change K.d ((ComplexShape.up ℕ).prev n) n ((K.XIsoOfEq hi).inv x) = c.val
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.XIsoOfEq_inv_comp_d]
  exact hc

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma toCycles_zero {R : Type uC} [Ring R]
    (K : CochainComplex (ModuleCat.{uC} R) ℕ) (a : (K.sc 0).X₁) :
    (K.sc 0).moduleCatToCycles a = 0 := by
  apply Subtype.ext
  change K.d ((ComplexShape.up ℕ).prev 0) 0 a = 0
  rw [K.shape _ _ (by intro h; change _ + 1 = 0 at h; omega)]
  rfl

set_option maxHeartbeats 1600000 in
-- Degree transports require extra unification work in the Leibniz calculation.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma cechCupCycles_boundary_left {X : Scheme.{uC}} {ι : Type uC}
    (U : ι → X.Opens) (F G : X.Modules) (p q : ℕ)
    (a : (((cechComplexFunctor U).obj F.presheafModuleCat).sc p).X₁)
    (b : (((cechComplexFunctor U).obj G.presheafModuleCat).sc q).moduleCatLeftHomologyData.K) :
    cechCupCycles U F G p q
        ((((cechComplexFunctor U).obj F.presheafModuleCat).sc p).moduleCatToCycles a) b
      ∈ LinearMap.range
        (((cechComplexFunctor U).obj (F ⊗ G).presheafModuleCat).sc (p + q)).moduleCatToCycles := by
  cases p with
  | zero =>
    rw [toCycles_zero, LinearMap.map_zero, LinearMap.zero_apply]
    exact Submodule.zero_mem _
  | succ p =>
    let C := (cechComplexFunctor U).obj (F ⊗ G).presheafModuleCat
    have hi : (ComplexShape.up ℕ).prev (p + 1) = p :=
      (ComplexShape.up ℕ).prev_eq' rfl
    let a' := (((cechComplexFunctor U).obj F.presheafModuleCat).XIsoOfEq hi).hom a
    have ha : (((((cechComplexFunctor U).obj
        F.presheafModuleCat).sc (p + 1)).moduleCatToCycles) a).val =
        ((cechComplexFunctor U).obj F.presheafModuleCat).d p (p + 1) a' := by
      dsimp only [a']
      rw [← ConcreteCategory.comp_apply, HomologicalComplex.XIsoOfEq_hom_comp_d]
      rfl
    have h := cechCupCochain_leibniz U F G p q a' b.val
    rw [cycle_d_zero ((cechComplexFunctor U).obj G.presheafModuleCat) q b] at h
    have hz : cechCupCochain U F G p (q + 1) a' 0 = 0 :=
      (cechCupLinear U F G p (q + 1) a').map_zero
    rw [hz, map_zero, smul_zero, add_zero] at h
    apply cycle_mem_range_of_d C (p + q) ((p + 1) + q) (by omega) _
      (cechCupCochain U F G p q a' b.val)
    have hd := congrArg (fun f ↦ f (cechCupCochain U F G p q a' b.val))
      (C.d_comp_XIsoOfEq_hom (Nat.add_right_comm p 1 q).symm (p + q))
    rw [ConcreteCategory.comp_apply, h] at hd
    simp only [HomologicalComplex.XIsoOfEq, eqToIso] at hd
    rw [← ConcreteCategory.comp_apply, eqToHom_trans, eqToHom_refl,
      CategoryTheory.id_apply] at hd
    change C.d (p + q) (p + 1 + q) _ = cechCupCochain U F G (p + 1) q _ b.val
    rw [ha]
    exact hd.symm

set_option maxHeartbeats 1600000 in
-- Degree transports require extra unification work in the Leibniz calculation.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma cechCupCycles_boundary_right {X : Scheme.{uC}} {ι : Type uC}
    (U : ι → X.Opens) (F G : X.Modules) (p q : ℕ)
    (a : (((cechComplexFunctor U).obj F.presheafModuleCat).sc p).moduleCatLeftHomologyData.K)
    (b : (((cechComplexFunctor U).obj G.presheafModuleCat).sc q).X₁) :
    cechCupCycles U F G p q a
        ((((cechComplexFunctor U).obj G.presheafModuleCat).sc q).moduleCatToCycles b)
      ∈ LinearMap.range
        (((cechComplexFunctor U).obj (F ⊗ G).presheafModuleCat).sc (p + q)).moduleCatToCycles := by
  cases q with
  | zero =>
    rw [toCycles_zero, LinearMap.map_zero]
    exact Submodule.zero_mem _
  | succ q =>
    let C := (cechComplexFunctor U).obj (F ⊗ G).presheafModuleCat
    have hi : (ComplexShape.up ℕ).prev (q + 1) = q :=
      (ComplexShape.up ℕ).prev_eq' rfl
    let b' := (((cechComplexFunctor U).obj G.presheafModuleCat).XIsoOfEq hi).hom b
    have hb : (((((cechComplexFunctor U).obj
        G.presheafModuleCat).sc (q + 1)).moduleCatToCycles) b).val =
        ((cechComplexFunctor U).obj G.presheafModuleCat).d q (q + 1) b' := by
      dsimp only [b']
      rw [← ConcreteCategory.comp_apply, HomologicalComplex.XIsoOfEq_hom_comp_d]
      rfl
    have h := cechCupCochain_leibniz U F G p q a.val b'
    rw [cycle_d_zero ((cechComplexFunctor U).obj F.presheafModuleCat) p a] at h
    have hz : cechCupCochain U F G (p + 1) q 0 b' = 0 := by
      exact congrArg (fun f ↦ f b') (cechCupLinear U F G (p + 1) q).map_zero
    rw [hz, map_zero, zero_add] at h
    have hs : ((-1 : ℤ) ^ p) * ((-1 : ℤ) ^ p) = 1 := by
      rw [← mul_pow]
      simp
    have h' := congrArg (fun z ↦ (-1 : ℤ) ^ p • z) h
    rw [smul_smul, hs, one_smul] at h'
    apply cycle_mem_range_of_d C (p + q) (p + (q + 1)) (by omega) _
      ((-1 : ℤ) ^ p • cechCupCochain U F G p q a.val b')
    have hd := congrArg
      (fun f ↦ f ((-1 : ℤ) ^ p • cechCupCochain U F G p q a.val b'))
      (C.d_comp_XIsoOfEq_hom (Nat.add_assoc p q 1) (p + q))
    rw [ConcreteCategory.comp_apply, map_zsmul, h'] at hd
    simp only [HomologicalComplex.XIsoOfEq, eqToIso, eqToHom_refl] at hd
    change C.d (p + q) (p + (q + 1)) _ = cechCupCochain U F G p (q + 1) a.val _
    rw [hb]
    exact hd.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma bilinear_homology_desc {R : Type uC} [CommRing R]
    (A B C : CochainComplex (ModuleCat.{uC} R) ℕ) (p q n : ℕ)
    (f : (A.sc p).moduleCatLeftHomologyData.K →ₗ[R]
      (B.sc q).moduleCatLeftHomologyData.K →ₗ[R] (C.sc n).moduleCatLeftHomologyData.K)
    (hl : ∀ a b, f ((A.sc p).moduleCatToCycles a) b ∈
      LinearMap.range (C.sc n).moduleCatToCycles)
    (hr : ∀ a b, f a ((B.sc q).moduleCatToCycles b) ∈
      LinearMap.range (C.sc n).moduleCatToCycles) :
    ∃ cup : A.homology p →ₗ[R] B.homology q →ₗ[R] C.homology n,
      ∀ a b, cup (cupCycleClass A p a) (cupCycleClass B q b) =
        cupCycleClass C n (f a b) := by
  let g := f.compr₂ (cycleClassLinear C n)
  have hgl : LinearMap.range (A.sc p).moduleCatToCycles ≤ g.ker := by
    rintro _ ⟨a, rfl⟩
    ext b
    exact (cycleClassLinear_eq_zero C n _).mpr (hl a b)
  have hgr : LinearMap.range (B.sc q).moduleCatToCycles ≤ g.flip.ker := by
    rintro _ ⟨b, rfl⟩
    ext a
    exact (cycleClassLinear_eq_zero C n _).mpr (hr a b)
  let cup := (g.liftQ₂ _ _ hgl hgr).compl₁₂
    (A.sc p).moduleCatHomologyIso.hom.hom (B.sc q).moduleCatHomologyIso.hom.hom
  refine ⟨cup, ?_⟩
  intro a b
  have hc (K : CochainComplex (ModuleCat.{uC} R) ℕ) (i : ℕ)
      (z : (K.sc i).moduleCatLeftHomologyData.K) :
      (K.sc i).moduleCatHomologyIso.hom (cupCycleClass K i z) =
        (K.sc i).moduleCatLeftHomologyData.π z := by
    simp only [cupCycleClass, ← ConcreteCategory.comp_apply]
    rw [Category.assoc, ShortComplex.π_moduleCatCyclesIso_hom,
      Iso.inv_hom_id_assoc]
  dsimp only [cup, LinearMap.compl₁₂_apply, ModuleCat.Hom.hom]
  exact (congrArg₂ (fun x y ↦ g.liftQ₂ _ _ hgl hgr x y)
    (hc A p a) (hc B q b)).trans (by rfl)

/-- The induced bilinear product on Cech cohomology is fixed by its values on cocycles,
using the explicit Alexander--Whitney formula, rather than arbitrary unary maps.
Source: Stacks, Tag 07MB (blueprint: def-sc-cech-cup-product). -/
def IsCechCupProduct {X : Scheme.{uC}} {ι : Type uC} (U : ι → X.Opens)
    (F G : X.Modules) (p q : ℕ)
    (cup : ((cechComplexFunctor U).obj F.presheafModuleCat).homology p →ₗ[Γ(X, ⊤)]
      ((cechComplexFunctor U).obj G.presheafModuleCat).homology q →ₗ[Γ(X, ⊤)]
        ((cechComplexFunctor U).obj (F ⊗ G).presheafModuleCat).homology (p + q)) : Prop :=
  ∀ (a : (((cechComplexFunctor U).obj F.presheafModuleCat).sc p).moduleCatLeftHomologyData.K)
    (b : (((cechComplexFunctor U).obj G.presheafModuleCat).sc q).moduleCatLeftHomologyData.K)
    (c : (((cechComplexFunctor U).obj (F ⊗ G).presheafModuleCat).sc
      (p + q)).moduleCatLeftHomologyData.K),
    c.val = cechCupCochain U F G p q a.val b.val →
      cup (cupCycleClass _ p a) (cupCycleClass _ q b) = cupCycleClass _ (p + q) c

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The cochain cup product descends uniquely to a bilinear map on Cech cohomology.
Source: Stacks, Tag 07MB (blueprint: def-sc-cech-cup-product).
Proof: expand the alternating restriction differential of the front/back formula.
The interior omitted-vertex terms cancel in pairs, giving
 d(a cup b) = d(a) cup b + (-1)^p a cup d(b).
Thus products of cocycles are cocycles. The same equation shows that a product with
a boundary is a boundary. Section tensor is bilinear over global sections, so the
formula descends to the two quotient modules. Every cohomology class is represented
by a cocycle, which gives uniqueness. This holds for every index set, without a
cover condition or finiteness assumption. -/
theorem exists_unique_cechCupProduct {X : Scheme.{uC}} {ι : Type uC} (U : ι → X.Opens)
    (F G : X.Modules) (p q : ℕ) :
    ∃! cup : ((cechComplexFunctor U).obj F.presheafModuleCat).homology p →ₗ[Γ(X, ⊤)]
      ((cechComplexFunctor U).obj G.presheafModuleCat).homology q →ₗ[Γ(X, ⊤)]
        ((cechComplexFunctor U).obj (F ⊗ G).presheafModuleCat).homology (p + q),
      IsCechCupProduct U F G p q cup := by
  obtain ⟨cup, hcup⟩ := bilinear_homology_desc
    ((cechComplexFunctor U).obj F.presheafModuleCat)
    ((cechComplexFunctor U).obj G.presheafModuleCat)
    ((cechComplexFunctor U).obj (F ⊗ G).presheafModuleCat) p q (p + q)
    (cechCupCycles U F G p q)
    (cechCupCycles_boundary_left U F G p q)
    (cechCupCycles_boundary_right U F G p q)
  refine ⟨cup, ?_, ?_⟩
  · intro a b c hc
    have he : cechCupCycles U F G p q a b = c := Subtype.ext hc.symm
    rw [hcup, he]
  · intro other ho
    ext x y
    obtain ⟨a, ha⟩ := cycleClassLinear_surjective
      ((cechComplexFunctor U).obj F.presheafModuleCat) p x
    obtain ⟨b, hb⟩ := cycleClassLinear_surjective
      ((cechComplexFunctor U).obj G.presheafModuleCat) q y
    change cupCycleClass _ p a = x at ha
    change cupCycleClass _ q b = y at hb
    subst x y
    exact (ho a b (cechCupCycles U F G p q a b) rfl).trans (hcup a b).symm

end
end AlgebraicGeometry.Scheme.Modules
