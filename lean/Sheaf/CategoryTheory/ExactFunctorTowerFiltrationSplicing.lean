module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

import Mathlib.Order.Fin.Basic
import Mathlib.CategoryTheory.Abelian.Refinements
import WeilConjectures.ConstructibleSheaf.Devissage

/-! # Prescribed quotient filtrations in a finite tower of exact functors

Source: literature/blueprint/latest/blueprint/sec-deligne-laumon-general/
sk-i-dl-general-real/thm-zl-real-mixed-by-curves.proof.md, final paragraph:
“Splice the resulting finite filtrations using inverse images under the quotient map”.
(blueprint: lem-zl-exact-functor-tower-filtration-splicing).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe v u

namespace CategoryTheory

open CategoryTheory Limits
open scoped BigOperators

private theorem pullbackQuotient {C : Type u} [Category.{v} C] [Abelian C]
    {X Y : C} (p : X ⟶ Y) [Epi p] (S U : Subobject Y) (h : S ≤ U)
    (h' : (Subobject.pullback p).obj S ≤ (Subobject.pullback p).obj U) :
    Nonempty (cokernel (Subobject.ofLE _ _ h') ≅ cokernel (Subobject.ofLE S U h)) := by
  let R := (Subobject.pullback p).obj S
  let W := (Subobject.pullback p).obj U
  let i := Subobject.ofLE S U h
  let j := Subobject.ofLE R W h'
  let q := Subobject.pullbackπ p U ≫ cokernel.π i
  have hp : Epi (Subobject.pullbackπ p U) :=
    Abelian.epi_fst_of_isLimit U.arrow p (Subobject.isPullback p U).isLimit
  have hcomm : j ≫ Subobject.pullbackπ p U = Subobject.pullbackπ p S ≫ i := by
    apply (cancel_mono U.arrow).1
    rw [Category.assoc, (Subobject.isPullback p U).w, ← Category.assoc]
    rw [show j ≫ W.arrow = R.arrow from Subobject.ofLE_arrow h']
    rw [← (Subobject.isPullback p S).w, Category.assoc]
    rw [show i ≫ U.arrow = S.arrow from Subobject.ofLE_arrow h]
  have hz : j ≫ q = 0 := by
    dsimp only [q]
    rw [← Category.assoc, hcomm, Category.assoc, cokernel.condition, comp_zero]
  let E := ShortComplex.mk j q hz
  have he : E.Exact := by
    rw [ShortComplex.exact_iff_exact_up_to_refinements]
    intro Z x hx
    obtain ⟨Z', e, he, y, hy⟩ :=
      (CokernelCofork.IsColimit.comp_π_eq_zero_iff_up_to_refinements
        (cokernelIsCokernel i) (x ≫ Subobject.pullbackπ p U)).mp
          (by
            change (x ≫ Subobject.pullbackπ p U) ≫ cokernel.π i = 0
            simpa only [E, q, Category.assoc] using hx)
    let z := (Subobject.isPullback p S).lift y (e ≫ x ≫ W.arrow) (by
      calc
        y ≫ S.arrow = (y ≫ i) ≫ U.arrow := by simp [i]
        _ = (e ≫ x ≫ Subobject.pullbackπ p U) ≫ U.arrow := by rw [hy]
        _ = (e ≫ x ≫ W.arrow) ≫ p := by
          simp only [Category.assoc, (Subobject.isPullback p U).w]
          rfl)
    refine ⟨Z', e, he, z, ?_⟩
    apply (cancel_mono W.arrow).1
    change (e ≫ x) ≫ W.arrow = (z ≫ j) ≫ W.arrow
    simp only [Category.assoc]
    rw [show j ≫ W.arrow = R.arrow from Subobject.ofLE_arrow h']
    exact ((Subobject.isPullback p S).lift_snd _ _ _).symm
  have : Epi E.g := inferInstanceAs (Epi q)
  exact ⟨(cokernelIsCokernel j).coconePointUniqueUpToIso he.gIsCokernel⟩

private theorem imageMonoMap {C : Type u} [Category.{v} C] [Abelian C]
    {X Y : C} (u : X ⟶ Y) [Mono u] (S : Subobject X) :
    imageSubobject (S.arrow ≫ u) = (Subobject.map u).obj S := by
  rw [imageSubobject_mono, ← Subobject.map_mk, Subobject.mk_arrow]

private theorem imageMonoQuotient {C : Type u} [Category.{v} C] [Abelian C]
    {X Y : C} (u : X ⟶ Y) [Mono u] (S U : Subobject X) (h : S ≤ U)
    (h' : imageSubobject (S.arrow ≫ u) ≤ imageSubobject (U.arrow ≫ u)) :
    Nonempty (cokernel (Subobject.ofLE _ _ h') ≅ cokernel (Subobject.ofLE S U h)) := by
  revert h'
  rw [imageSubobject_mono, imageSubobject_mono]
  intro h'
  exact ⟨Subobject.cokernelOfLEMkIso _ _ (Iso.refl _) (Subobject.ofLE S U h)
    (by simp) h'⟩

private theorem functorSubobjectMono {C D : Type u} [Category.{v} C] [Category.{v} D]
    [Abelian C] [Abelian D] (T : C ⥤ D) [PreservesFiniteLimits T]
    {X : C} (S U : Subobject X) (h : S ≤ U) :
    imageSubobject (T.map S.arrow) ≤ imageSubobject (T.map U.arrow) := by
  rw [imageSubobject_mono, imageSubobject_mono]
  exact Subobject.mk_le_mk_of_comm (T.map (Subobject.ofLE S U h)) (by
    rw [← T.map_comp, Subobject.ofLE_arrow])

private theorem functorSubobjectQuotient {C D : Type u}
    [Category.{v} C] [Category.{v} D] [Abelian C] [Abelian D]
    (T : C ⥤ D) [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    {X : C} (S U : Subobject X) (h : S ≤ U)
    (h' : imageSubobject (T.map S.arrow) ≤ imageSubobject (T.map U.arrow)) :
    Nonempty (cokernel (Subobject.ofLE _ _ h') ≅ T.obj (cokernel (Subobject.ofLE S U h))) := by
  revert h'
  rw [imageSubobject_mono, imageSubobject_mono]
  intro h'
  exact ⟨Subobject.cokernelOfLEMkIso _ _ (Iso.refl _) (T.map (Subobject.ofLE S U h))
    (by simp [← T.map_comp]) h' ≪≫ (PreservesCokernel.iso T _).symm⟩

private noncomputable def spliceSeq {L : Type*} (n : ℕ) (I R : ℕ → L) (r : ℕ) : L :=
  if r ≤ n then I r else R (r - n)

private theorem spliceSeq_head {L : Type*} (n : ℕ) (I R : ℕ → L) (r : ℕ) (h : r ≤ n) :
    spliceSeq n I R r = I r := by simp [spliceSeq, h]

private theorem spliceSeq_tail {L : Type*} (n : ℕ) (I R : ℕ → L) (hj : I n = R 0)
    (r : ℕ) : spliceSeq n I R (n + r) = R r := by
  by_cases h : r = 0
  · subst r
    simp [spliceSeq, hj]
  · simp [spliceSeq, show ¬ n + r ≤ n by omega]

private theorem spliceSeq_mono {L : Type*} [Preorder L] (n : ℕ) (I R : ℕ → L)
    (hI : ∀ r, r < n → I r ≤ I (r + 1)) (hR : ∀ r, R r ≤ R (r + 1))
    (hj : I n = R 0) (r : ℕ) : spliceSeq n I R r ≤ spliceSeq n I R (r + 1) := by
  by_cases h : r < n
  · rw [spliceSeq_head _ _ _ _ (by omega), spliceSeq_head _ _ _ _ (by omega)]
    exact hI r h
  · obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le (show n ≤ r by omega)
    rw [spliceSeq_tail _ _ _ hj, show n + s + 1 = n + (s + 1) by omega,
      spliceSeq_tail _ _ _ hj]
    exact hR s

private theorem kernelPullback {C : Type u} [Category.{v} C] [Abelian C]
    {K H B : C} (u : K ⟶ H) (p : H ⟶ B) (w : u ≫ p = 0)
    (hu : IsLimit (KernelFork.ofι u w)) [Mono u] :
    Subobject.mk u = (Subobject.pullback p).obj ⊥ := by
  apply le_antisymm
  · exact Subobject.mk_le_of_comm
      ((Subobject.isPullback p ⊥).lift 0 u (by simp [w]))
      ((Subobject.isPullback p ⊥).lift_snd _ _ _)
  · let R := (Subobject.pullback p).obj ⊥
    have hz : R.arrow ≫ p = 0 := by
      rw [← (Subobject.isPullback p ⊥).w, Subobject.bot_arrow, comp_zero]
    exact Subobject.le_mk_of_comm (KernelFork.IsLimit.lift' hu R.arrow hz).1
      (KernelFork.IsLimit.lift' hu R.arrow hz).2

private structure TowerFlag {C : Type u} [Category.{v} C] [Abelian C] (X : C) where
  length : ℕ
  step : ℕ → Subobject X
  zero : step 0 = ⊥
  top : step length = ⊤
  mono : ∀ r, step r ≤ step (r + 1)

private theorem spliceJunction {C D : Type u}
    [Category.{v} C] [Category.{v} D] [Abelian C] [Abelian D]
    (T : D ⥤ C) [T.Additive] [PreservesFiniteLimits T]
    {K H : C} {B : D} (u : K ⟶ H) (p : H ⟶ T.obj B) (w : u ≫ p = 0)
    (hu : IsLimit (KernelFork.ofι u w)) [Mono u] (n : ℕ)
    (Ks : Fin (n + 1) → Subobject K) (hn : Ks (Fin.last n) = ⊤)
    (L : TowerFlag B) :
    imageSubobject ((Ks ⟨min n n, by omega⟩).arrow ≫ u) =
      (Subobject.pullback p).obj (imageSubobject (T.map (L.step 0).arrow)) := by
  rw [show (⟨min n n, by omega⟩ : Fin (n + 1)) = Fin.last n by ext; simp]
  rw [hn, imageMonoMap, Subobject.map_top, L.zero, Subobject.bot_arrow,
    T.map_zero, imageSubobject_zero]
  exact kernelPullback u p w hu

private noncomputable def spliceFlag {C D : Type u}
    [Category.{v} C] [Category.{v} D] [Abelian C] [Abelian D]
    (T : D ⥤ C) [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    {K H : C} {B : D} (u : K ⟶ H) (p : H ⟶ T.obj B) (w : u ≫ p = 0)
    (hu : IsLimit (KernelFork.ofι u w)) [Mono u] (n : ℕ)
    (Ks : Fin (n + 1) → Subobject K) (h0 : Ks 0 = ⊥) (hn : Ks (Fin.last n) = ⊤)
    (hm : ∀ r : Fin n, Ks r.castSucc ≤ Ks r.succ) (L : TowerFlag B) :
    TowerFlag H := by
  let I := fun r ↦ imageSubobject ((Ks ⟨min r n, by omega⟩).arrow ≫ u)
  let R := fun r ↦ (Subobject.pullback p).obj (imageSubobject (T.map (L.step r).arrow))
  have hj : I n = R 0 := spliceJunction T u p w hu n Ks hn L
  refine ⟨n + L.length, spliceSeq n I R, ?_, ?_, ?_⟩
  · rw [spliceSeq_head _ _ _ _ (Nat.zero_le _)]
    dsimp [I]
    rw [show (⟨min 0 n, by omega⟩ : Fin (n + 1)) = 0 by ext; simp]
    rw [h0, Subobject.bot_arrow, zero_comp, imageSubobject_zero]
  · rw [spliceSeq_tail _ _ _ hj]
    dsimp [R]
    rw [L.top, imageSubobject_mono, Subobject.mk_eq_top_of_isIso, Subobject.pullback_top]
  · apply spliceSeq_mono _ _ _ _ _ hj
    · intro r hr
      dsimp [I]
      simp only [imageMonoMap]
      apply (Subobject.map u).monotone
      apply (Fin.monotone_iff_le_succ.mpr hm)
      exact min_le_min (Nat.le_succ r) le_rfl
    · intro r
      apply (Subobject.pullback p).monotone
      exact functorSubobjectMono T _ _ (L.mono r)

section SpliceProperties

private theorem spliceFlag_head {C D : Type u}
    [Category.{v} C] [Category.{v} D] [Abelian C] [Abelian D]
  (T : D ⥤ C) [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
  {K H : C} {B : D} (u : K ⟶ H) (p : H ⟶ T.obj B) (w : u ≫ p = 0)
  (hu : IsLimit (KernelFork.ofι u w)) [Mono u] (n : ℕ)
  (Ks : Fin (n + 1) → Subobject K) (h0 : Ks 0 = ⊥) (hn : Ks (Fin.last n) = ⊤)
  (hm : ∀ r : Fin n, Ks r.castSucc ≤ Ks r.succ) (L : TowerFlag B)
    (r : Fin (n + 1)) :
    (spliceFlag T u p w hu n Ks h0 hn hm L).step r =
      imageSubobject ((Ks r).arrow ≫ u) := by
  dsimp only [spliceFlag]
  change spliceSeq n _ _ r = _
  rw [spliceSeq_head _ _ _ _ (by omega)]
  have he : (⟨min r.val n, by omega⟩ : Fin (n + 1)) = r := by
    apply Fin.ext
    exact Nat.min_eq_left (by omega)
  simp only [imageMonoMap]
  exact congrArg (fun i ↦ (Subobject.map u).obj (Ks i)) he

private theorem spliceFlag_tail {C D : Type u}
    [Category.{v} C] [Category.{v} D] [Abelian C] [Abelian D]
  (T : D ⥤ C) [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
  {K H : C} {B : D} (u : K ⟶ H) (p : H ⟶ T.obj B) (w : u ≫ p = 0)
  (hu : IsLimit (KernelFork.ofι u w)) [Mono u] (n : ℕ)
  (Ks : Fin (n + 1) → Subobject K) (h0 : Ks 0 = ⊥) (hn : Ks (Fin.last n) = ⊤)
  (hm : ∀ r : Fin n, Ks r.castSucc ≤ Ks r.succ) (L : TowerFlag B)
    (r : ℕ) :
    (spliceFlag T u p w hu n Ks h0 hn hm L).step (n + r) =
      (Subobject.pullback p).obj (imageSubobject (T.map (L.step r).arrow)) := by
  dsimp only [spliceFlag]
  change spliceSeq n _ _ (n + r) = _
  exact spliceSeq_tail _ _ _ (spliceJunction T u p w hu n Ks hn L) r

end SpliceProperties

private noncomputable def towerTransport (t : ℕ) (A : Fin (t + 1) → Type u)
    [∀ a, Category.{v} (A a)] (T : ∀ a : Fin t, A a.succ ⥤ A a.castSucc) :
    ∀ (a c : Fin (t + 1)), a ≤ c → A c ⥤ A a :=
  Fin.reverseInduction
    (fun c h ↦ by
      have hc : c = Fin.last t := Fin.ext (by
        have := c.isLt
        have hh : t ≤ c.val := h
        simp only [Fin.val_last]
        omega)
      subst c
      exact 𝟭 _)
    (fun a next c h ↦ by
      by_cases he : c = a.castSucc
      · subst c
        exact 𝟭 _
      · exact next c (by
          have hh : a.val ≤ c.val := h
          have he' : c.val ≠ a.val := fun e ↦ he (Fin.ext e)
          change a.val + 1 ≤ c.val
          omega) ⋙ T a)

private theorem towerTransport_id (t : ℕ) (A : Fin (t + 1) → Type u)
    [∀ a, Category.{v} (A a)] (T : ∀ a : Fin t, A a.succ ⥤ A a.castSucc)
    (a : Fin (t + 1)) : towerTransport t A T a a le_rfl = 𝟭 _ := by
  induction a using Fin.reverseInduction with
  | last => simp [towerTransport]
  | cast a ih => simp [towerTransport, Fin.reverseInduction_castSucc]

private theorem towerTransport_step (t : ℕ) (A : Fin (t + 1) → Type u)
    [∀ a, Category.{v} (A a)] (T : ∀ a : Fin t, A a.succ ⥤ A a.castSucc)
    (a : Fin t) (c : Fin (t + 1)) (h : a.succ ≤ c) :
    towerTransport t A T a.castSucc c ((Fin.castSucc_le_succ a).trans h) =
      towerTransport t A T a.succ c h ⋙ T a := by
  have hn : c ≠ a.castSucc := by
    intro he
    subst c
    simp at h
  simp [towerTransport, Fin.reverseInduction_castSucc, hn]

section TowerConstruction

variable (t : ℕ) (A : Fin (t + 1) → Type u)
  [∀ a, Category.{v} (A a)] [∀ a, Abelian (A a)]
  (T : ∀ a : Fin t, A a.succ ⥤ A a.castSucc)
  (hadd : ∀ a, (T a).Additive) (hlim : ∀ a, PreservesFiniteLimits (T a))
  (hcol : ∀ a, PreservesFiniteColimits (T a))
  (H : ∀ a : Fin (t + 1), A a) (hHt : IsZero (H (Fin.last t)))
  (K : ∀ a : Fin t, A a.castSucc) (u : ∀ a : Fin t, K a ⟶ H a.castSucc)
  (π : ∀ a : Fin t, H a.castSucc ⟶ (T a).obj (H a.succ))
  (huπ : ∀ a, u a ≫ π a = 0)
  (hu : ∀ a, IsLimit (KernelFork.ofι (u a) (huπ a)))
  (n : Fin t → ℕ) (Ks : ∀ a : Fin t, Fin (n a + 1) → Subobject (K a))
  (hKzero : ∀ a, Ks a 0 = ⊥) (hKtop : ∀ a, Ks a (Fin.last (n a)) = ⊤)
  (hKmono : ∀ (a : Fin t) (s : Fin (n a)), Ks a s.castSucc ≤ Ks a s.succ)

private noncomputable def towerFlags : ∀ a, TowerFlag (H a) :=
  Fin.reverseInduction
    (by
      have := Subobject.subsingleton_of_isZero hHt
      exact ⟨0, fun _ ↦ ⊥, rfl, Subsingleton.elim _ _, fun _ ↦ le_rfl⟩)
    (fun a next ↦ by
      have := hadd a
      have := hlim a
      have := hcol a
      have : Mono (u a) := Fork.IsLimit.mono (hu a)
      exact spliceFlag (T a) (u a) (π a) (huπ a) (hu a) (n a) (Ks a)
        (hKzero a) (hKtop a) (hKmono a) next)

private theorem towerFlags_last :
    (towerFlags t A T hadd hlim hcol H hHt K u π huπ hu n Ks hKzero hKtop hKmono
      (Fin.last t)).length = 0 := by
  simp [towerFlags]

private theorem towerFlags_length (a : Fin t) :
    (towerFlags t A T hadd hlim hcol H hHt K u π huπ hu n Ks hKzero hKtop hKmono
      a.castSucc).length = n a +
    (towerFlags t A T hadd hlim hcol H hHt K u π huπ hu n Ks hKzero hKtop hKmono
      a.succ).length := by
  simp [towerFlags, Fin.reverseInduction_castSucc, spliceFlag]

private theorem towerFlags_head (a : Fin t) (r : Fin (n a + 1)) :
    (towerFlags t A T hadd hlim hcol H hHt K u π huπ hu n Ks hKzero hKtop hKmono
      a.castSucc).step r = imageSubobject ((Ks a r).arrow ≫ u a) := by
  have := hadd a
  have := hlim a
  have := hcol a
  have : Mono (u a) := Fork.IsLimit.mono (hu a)
  simpa only [towerFlags, Fin.reverseInduction_castSucc] using
    spliceFlag_head (T a) (u a) (π a) (huπ a) (hu a) (n a) (Ks a)
      (hKzero a) (hKtop a) (hKmono a)
      (towerFlags t A T hadd hlim hcol H hHt K u π huπ hu n Ks hKzero hKtop hKmono a.succ) r

private theorem towerFlags_tail (a : Fin t) (r : ℕ) :
    (towerFlags t A T hadd hlim hcol H hHt K u π huπ hu n Ks hKzero hKtop hKmono
      a.castSucc).step (n a + r) =
    (Subobject.pullback (π a)).obj (imageSubobject ((T a).map
      ((towerFlags t A T hadd hlim hcol H hHt K u π huπ hu n Ks hKzero hKtop hKmono
        a.succ).step r).arrow)) := by
  have := hadd a
  have := hlim a
  have := hcol a
  have : Mono (u a) := Fork.IsLimit.mono (hu a)
  simpa only [towerFlags, Fin.reverseInduction_castSucc] using
    spliceFlag_tail (T a) (u a) (π a) (huπ a) (hu a) (n a) (Ks a)
      (hKzero a) (hKtop a) (hKmono a)
      (towerFlags t A T hadd hlim hcol H hHt K u π huπ hu n Ks hKzero hKtop hKmono a.succ) r

end TowerConstruction

private theorem suffixSum_step {t : ℕ} (n : Fin t → ℕ) (a : Fin t) :
    (∑ b : Fin t, if a.val ≤ b.val then n b else 0) =
      n a + ∑ b : Fin t, if a.val + 1 ≤ b.val then n b else 0 := by
  calc
    _ = ∑ b : Fin t, ((if b = a then n b else 0) +
        (if a.val + 1 ≤ b.val then n b else 0)) := by
      apply Finset.sum_congr rfl
      intro b hb
      by_cases he : b = a
      · subst b
        simp
      · have hne : b.val ≠ a.val := fun h ↦ he (Fin.ext h)
        by_cases h : a.val ≤ b.val <;> simp [he, h, show
          (a.val + 1 ≤ b.val) ↔ a.val ≤ b.val by omega]
    _ = _ := by rw [Finset.sum_add_distrib]; simp

private theorem prefixSum_step {t : ℕ} (n : Fin t → ℕ) (a c : Fin t)
    (h : a.val < c.val) :
    (∑ b : Fin t, if a.val ≤ b.val ∧ b.val < c.val then n b else 0) =
      n a + ∑ b : Fin t, if a.val + 1 ≤ b.val ∧ b.val < c.val then n b else 0 := by
  calc
    _ = ∑ b : Fin t, ((if b = a then n b else 0) +
        (if a.val + 1 ≤ b.val ∧ b.val < c.val then n b else 0)) := by
      apply Finset.sum_congr rfl
      intro b hb
      by_cases he : b = a
      · subst b
        simp [h]
      · have hne : b.val ≠ a.val := fun h ↦ he (Fin.ext h)
        have hh : (a.val + 1 ≤ b.val) ↔ a.val ≤ b.val := by omega
        simp [he, hh]
    _ = _ := by rw [Finset.sum_add_distrib]; simp

private theorem quotientCongr {C : Type u} [Category.{v} C] [Abelian C]
    {X : C} (S U S' U' : Subobject X) (h : S ≤ U) (h' : S' ≤ U')
    (e : S = S') (e' : U = U') :
    Nonempty (cokernel (Subobject.ofLE S U h) ≅ cokernel (Subobject.ofLE S' U' h')) := by
  subst S'
  subst U'
  exact ⟨Iso.refl _⟩

set_option linter.unusedVariables false in
/-- A finite tower of short exact sequences in abelian categories admits the prescribed
filtration obtained by concatenating the kernel filtration and inverse images of the next
filtration. The quotient factors and their labels are retained under exact functors.
Source: the final paragraph cited in the module docstring.
(blueprint: lem-zl-exact-functor-tower-filtration-splicing).

Proof: construct the filtrations by descending induction on the stage. At stage `t`
the length is zero and the object is zero. By lem-sp-exact-functor-preserves-homology,
transport the next filtration through the exact functor, preserving its zero and top
steps and its successive quotients. Form the inverse images as pullbacks; their
inclusions are monic by the pullback universal property. The first is the given
kernel, and the last is the whole object. By lem-sp-abelian-refinements(a), the
projection from every pullback to its transported subobject is epic. For two
successive pullbacks, compose this projection with the transported quotient map.
Refinements(b,c) proves exactness of this composite with the inclusion of the preceding
pullback. By lem-weil-pbc-abelian-exact-epi-cokernel(a) its cokernel is the transported
successive quotient. The kernel-image steps have the original quotients by
lem-sfb-subobject-inclusion-cokernel. Concatenate these steps and the inverse-image
steps, omitting the repeated junction. Lengths add and quotient factors remain in
stage order and then in the original order within each stage. Iterate the functor
preservation of `P` and apply isomorphism invariance to retain every assigned real
label, hence every common upper bound. Repeated steps and either list having length
zero cause no change to the argument; no quotient section is chosen.
-/
theorem exactFunctorTowerFiltrationSplicing
    (t : ℕ)
    (A : Fin (t + 1) → Type u)
    [hcat : ∀ a, Category.{v} (A a)]
    [hab : ∀ a, Abelian (A a)]
    (T : ∀ a : Fin t, A a.succ ⥤ A a.castSucc)
    (hadd : ∀ a, (T a).Additive)
    (hlim : ∀ a, PreservesFiniteLimits (T a))
    (hcol : ∀ a, PreservesFiniteColimits (T a))
    (H : ∀ a : Fin (t + 1), A a)
    (hHt : IsZero (H ⟨t, by omega⟩))
    (K : ∀ a : Fin t, A a.castSucc)
    (u : ∀ a : Fin t, K a ⟶ H a.castSucc)
    (π : ∀ a : Fin t, H a.castSucc ⟶ (T a).obj (H a.succ))
    (huπ : ∀ a, u a ≫ π a = 0)
    (hu : ∀ a, IsLimit (KernelFork.ofι (u a) (huπ a)))
    (hπ : ∀ a, IsColimit (CokernelCofork.ofπ (π a) (huπ a)))
    (n : ∀ a : Fin t, ℕ)
    (Ks : ∀ a : Fin t, Fin (n a + 1) → Subobject (K a))
    (hKzero : ∀ a, Ks a 0 = ⊥)
    (hKtop : ∀ a, Ks a (Fin.last (n a)) = ⊤)
    (hKmono : ∀ (a : Fin t) (s : Fin (n a)), Ks a s.castSucc ≤ Ks a s.succ)
    (P : ∀ a : Fin (t + 1), ℝ → Set (A a))
    (hPinv : ∀ a v X Y, X ∈ P a v → Nonempty (X ≅ Y) → Y ∈ P a v)
    (hPT : ∀ (a : Fin t) v X, X ∈ P a.succ v → (T a).obj X ∈ P a.castSucc v)
    (v : ∀ a : Fin t, Fin (n a) → ℝ)
    (hQ : ∀ (a : Fin t) (s : Fin (n a)),
      cokernel (Subobject.ofLE (Ks a s.castSucc) (Ks a s.succ) (hKmono a s)) ∈
        P a.castSucc (v a s)) :
    ∃ (N : Fin (t + 1) → ℕ)
      (F : ∀ a : Fin (t + 1), ℕ → Subobject (H a))
      (V : ∀ (a c : Fin (t + 1)), a ≤ c → A c ⥤ A a)
      (hVid : ∀ a, V a a le_rfl = 𝟭 (A a))
      (hVstep : ∀ (a : Fin t) (c : Fin (t + 1)) (hac : a.succ ≤ c),
        V a.castSucc c ((Fin.castSucc_le_succ a).trans hac) = V a.succ c hac ⋙ T a)
      (hN : ∀ a, N a = ∑ b : Fin t, if a.val ≤ b.val then n b else 0)
      (hFzero : ∀ a, F a 0 = ⊥)
      (hFtop : ∀ a, F a (N a) = ⊤)
      (hFmono : ∀ a r, F a r ≤ F a (r + 1))
      (hFkernel : ∀ (a : Fin t) (r : Fin (n a + 1)),
        F a.castSucc r = imageSubobject ((Ks a r).arrow ≫ u a))
      (hFpullback : ∀ (a : Fin t) (r : ℕ), r ≤ N a.succ →
        F a.castSucc (n a + r) =
          (Subobject.pullback (π a)).obj
            (imageSubobject ((T a).map (F a.succ r).arrow)))
      (hQFkernel : ∀ (a : Fin t) (r : Fin (n a)),
        Nonempty (cokernel
          (Subobject.ofLE (F a.castSucc r) (F a.castSucc (r + 1))
            (hFmono a.castSucc r)) ≅
          cokernel (Subobject.ofLE (Ks a r.castSucc) (Ks a r.succ) (hKmono a r))))
      (hQFtail : ∀ (a : Fin t) (r : ℕ), r < N a.succ →
        Nonempty (cokernel
          (Subobject.ofLE (F a.castSucc (n a + r)) (F a.castSucc (n a + r + 1))
            (hFmono a.castSucc (n a + r))) ≅
          (T a).obj (cokernel
            (Subobject.ofLE (F a.succ r) (F a.succ (r + 1))
              (hFmono a.succ r))))),
      ∀ (a : Fin (t + 1)) (c : Fin t) (hac : a ≤ c.castSucc)
        (s : Fin (n c)) (r : ℕ),
        r = (∑ b : Fin t, if a.val ≤ b.val ∧ b.val < c.val then n b else 0) + s.val →
        Nonempty (cokernel (Subobject.ofLE (F a r) (F a (r + 1)) (hFmono a r)) ≅
          (V a c.castSucc hac).obj
            (cokernel (Subobject.ofLE (Ks c s.castSucc) (Ks c s.succ) (hKmono c s)))) ∧
        cokernel (Subobject.ofLE (F a r) (F a (r + 1)) (hFmono a r)) ∈ P a (v c s) := by
  classical
  let flags := towerFlags t A T hadd hlim hcol H hHt K u π huπ hu n Ks
    hKzero hKtop hKmono
  let N := fun a ↦ (flags a).length
  let F := fun a ↦ (flags a).step
  let V := towerTransport t A T
  have hVid : ∀ a, V a a le_rfl = 𝟭 (A a) := towerTransport_id t A T
  have hVstep : ∀ (a : Fin t) (c : Fin (t + 1)) (hac : a.succ ≤ c),
      V a.castSucc c ((Fin.castSucc_le_succ a).trans hac) = V a.succ c hac ⋙ T a :=
    towerTransport_step t A T
  have hN : ∀ a, N a = ∑ b : Fin t, if a.val ≤ b.val then n b else 0 := by
    intro a
    induction a using Fin.reverseInduction with
    | last =>
      rw [show N (Fin.last t) = 0 from
        towerFlags_last t A T hadd hlim hcol H hHt K u π huπ hu n Ks
          hKzero hKtop hKmono]
      symm
      apply Finset.sum_eq_zero
      intro b hb
      simp only [Fin.val_last]
      rw [if_neg (by have := b.isLt; omega)]
    | cast a ih =>
      rw [show N a.castSucc = n a + N a.succ from
        towerFlags_length t A T hadd hlim hcol H hHt K u π huπ hu n Ks
          hKzero hKtop hKmono a, ih]
      exact (suffixSum_step n a).symm
  have hFzero : ∀ a, F a 0 = ⊥ := fun a ↦ (flags a).zero
  have hFtop : ∀ a, F a (N a) = ⊤ := fun a ↦ (flags a).top
  have hFmono : ∀ a r, F a r ≤ F a (r + 1) := fun a ↦ (flags a).mono
  have hFkernel : ∀ (a : Fin t) (r : Fin (n a + 1)),
      F a.castSucc r = imageSubobject ((Ks a r).arrow ≫ u a) :=
    towerFlags_head t A T hadd hlim hcol H hHt K u π huπ hu n Ks
      hKzero hKtop hKmono
  have hFpullbackAll : ∀ (a : Fin t) (r : ℕ), F a.castSucc (n a + r) =
      (Subobject.pullback (π a)).obj (imageSubobject ((T a).map (F a.succ r).arrow)) :=
    towerFlags_tail t A T hadd hlim hcol H hHt K u π huπ hu n Ks
      hKzero hKtop hKmono
  have hQFkernel : ∀ (a : Fin t) (r : Fin (n a)), Nonempty (cokernel
      (Subobject.ofLE (F a.castSucc r) (F a.castSucc (r + 1)) (hFmono a.castSucc r)) ≅
      cokernel (Subobject.ofLE (Ks a r.castSucc) (Ks a r.succ) (hKmono a r))) := by
    intro a r
    have : Mono (u a) := Fork.IsLimit.mono (hu a)
    have hm := (Subobject.map (u a)).monotone (hKmono a r)
    rw [← imageMonoMap, ← imageMonoMap] at hm
    obtain ⟨e⟩ := quotientCongr _ _ _ _ (hFmono a.castSucc r) hm
      (hFkernel a r.castSucc) (hFkernel a r.succ)
    obtain ⟨e'⟩ := imageMonoQuotient (u a) _ _ (hKmono a r) hm
    exact ⟨e ≪≫ e'⟩
  have hQFtailAll : ∀ (a : Fin t) (r : ℕ), Nonempty (cokernel
      (Subobject.ofLE (F a.castSucc (n a + r)) (F a.castSucc (n a + r + 1))
        (hFmono a.castSucc (n a + r))) ≅
      (T a).obj (cokernel (Subobject.ofLE (F a.succ r) (F a.succ (r + 1))
        (hFmono a.succ r)))) := by
    intro a r
    have := hadd a
    have := hlim a
    have := hcol a
    have : Epi (π a) := Cofork.IsColimit.epi (hπ a)
    have hS := functorSubobjectMono (T a) _ _ (hFmono a.succ r)
    have hR := (Subobject.pullback (π a)).monotone hS
    obtain ⟨e⟩ := quotientCongr _ _ _ _ (hFmono a.castSucc (n a + r)) hR
      (hFpullbackAll a r) (by simpa only [Nat.add_assoc] using hFpullbackAll a (r + 1))
    obtain ⟨e'⟩ := pullbackQuotient (π a) _ _ hS hR
    obtain ⟨e''⟩ := functorSubobjectQuotient (T a) _ _ (hFmono a.succ r) hS
    exact ⟨e ≪≫ e' ≪≫ e''⟩
  refine ⟨N, F, V, hVid, hVstep, hN, hFzero, hFtop, hFmono, hFkernel,
    fun a r _ ↦ hFpullbackAll a r, fun a r ↦ hQFkernel a r,
    fun a r _ ↦ hQFtailAll a r, ?_⟩
  intro a
  induction a using Fin.reverseInduction with
  | last =>
    intro c hac
    have hh : t ≤ c.val := hac
    have := c.isLt
    omega
  | cast a ih =>
    intro c hac s r hr
    by_cases he : c = a
    · subst c
      have hz : (∑ b : Fin t,
          if a.castSucc.val ≤ b.val ∧ b.val < a.val then n b else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro b hb
        rw [if_neg (by simp)]
      have hr' : r = s.val := by simpa only [hz, zero_add] using hr
      clear hr
      rw [hr']
      obtain ⟨e⟩ := hQFkernel a s
      refine ⟨?_, hPinv _ _ _ _ (hQ a s) ⟨e.symm⟩⟩
      simpa only [hVid, Functor.id_obj] using (show Nonempty _ from ⟨e⟩)
    · have hac' : a.succ ≤ c.castSucc := by
        have hh : a.val ≤ c.val := hac
        have hn : c.val ≠ a.val := fun h ↦ he (Fin.ext h)
        change a.val + 1 ≤ c.val
        omega
      let r' := (∑ b : Fin t,
        if a.succ.val ≤ b.val ∧ b.val < c.val then n b else 0) + s.val
      have hr' : r = n a + r' := by
        simp only [Fin.val_castSucc] at hr
        rw [prefixSum_step n a c (by have hh : a.val + 1 ≤ c.val := hac'; omega)] at hr
        simpa only [r', Fin.val_succ, Fin.val_castSucc, Nat.add_assoc] using hr
      obtain ⟨⟨e⟩, hP⟩ := ih c hac' s r' rfl
      obtain ⟨e'⟩ := hQFtailAll a r'
      clear hr
      rw [hr']
      have := hadd a
      have hobj := hPT a (v c s) _ hP
      refine ⟨?_, hPinv _ _ _ _ hobj ⟨e'.symm⟩⟩
      rw [hVstep a c.castSucc hac']
      exact ⟨e' ≪≫ (T a).mapIso e⟩


end CategoryTheory
