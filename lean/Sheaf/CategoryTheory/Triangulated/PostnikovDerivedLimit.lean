/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
import Mathlib.CategoryTheory.Triangulated.Yoneda
import Mathlib.Data.Int.Order.Lemmas

/-! # Canonical Postnikov reconstruction with exact countable products

Source: Stacks Project, Derived Categories, Tags 08TC and 07KC.
(blueprint: new-lem-sfb-exact-products-postnikov-limit)
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
universe w v u
namespace CategoryTheory

private theorem epi_towerTransition_of_eventually_iso
    {A : Type u} [Category.{v} A] [Preadditive A]
    {K : ℕ → A} [HasProduct K] (f : ∀ n, K (n + 1) ⟶ K n)
    (h : ∃ m : ℕ, ∀ n, m ≤ n → IsIso (f n)) :
    Epi (towerTransitionEndomorphism f) := by
  classical
  obtain ⟨m, hm⟩ := h
  let P := ∏ᶜ K
  let up : ∀ z : ℤ, (m : ℤ) ≤ z → (P ⟶ K z.toNat) → (P ⟶ K (z + 1).toNat) :=
    fun z hz q ↦ by
      have : IsIso (f z.toNat) := hm z.toNat (by omega)
      have e : (z + 1).toNat = z.toNat + 1 := by omega
      exact (q - Pi.π K z.toNat) ≫ inv (f z.toNat) ≫ eqToHom (congrArg K e.symm)
  let down : ∀ z : ℤ, z ≤ (m : ℤ) → (P ⟶ K z.toNat) → (P ⟶ K (z - 1).toNat) :=
    fun z _ q ↦ if h : 0 < z then
      Pi.π K (z - 1).toNat + q ≫
        eqToHom (congrArg K (show (z - 1).toNat + 1 = z.toNat by omega).symm) ≫
          f (z - 1).toNat
    else 0
  let qInt : ∀ z : ℤ, P ⟶ K z.toNat := fun z ↦ z.inductionOn' (m : ℤ) 0 up down
  let q : ∀ n : ℕ, P ⟶ K n := fun n ↦ qInt n
  have hq : ∀ n : ℕ, q n - q (n + 1) ≫ f n = Pi.π K n := by
    intro n
    by_cases hn : m ≤ n
    · have he := Int.inductionOn'_add_one (motive := fun z : ℤ ↦ P ⟶ K z.toNat)
        (zero := (0 : P ⟶ K (m : ℤ).toNat)) (succ := up) (pred := down)
        (show (m : ℤ) ≤ (n : ℤ) by omega)
      have : IsIso (f n) := hm n hn
      dsimp [up] at he
      simp only [Category.comp_id] at he
      change q (n + 1) = (q n - Pi.π K n) ≫ inv (f n) at he
      rw [he, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
      abel
    · have he := Int.inductionOn'_sub_one (motive := fun z : ℤ ↦ P ⟶ K z.toNat)
        (zero := (0 : P ⟶ K (m : ℤ).toNat)) (succ := up) (pred := down)
        (show ((n + 1 : ℕ) : ℤ) ≤ (m : ℤ) by omega)
      dsimp [down] at he
      rw [dif_pos (show 0 < (n : ℤ) + 1 by omega)] at he
      rw! [show (n : ℤ) + 1 - 1 = (n : ℤ) by omega] at he
      simp only [eqToHom_refl, Category.id_comp] at he
      change q n = Pi.π K n + q (n + 1) ≫ f n at he
      rw [he]
      abel
  have hsplit : Pi.lift q ≫ towerTransitionEndomorphism f = 𝟙 P := by
    apply Pi.hom_ext
    intro n
    simpa only [towerTransitionEndomorphism, towerProductShift, Preadditive.comp_sub,
      Preadditive.sub_comp, Category.assoc, Category.id_comp, Pi.lift_π,
      Pi.lift_π_assoc] using hq n
  exact epi_of_epi_fac hsplit

private theorem tower_kernel_of_eventually_iso
    {A : Type u} [Category.{v} A] [Preadditive A]
    {K : ℕ → A} [HasProduct K] (f : ∀ n, K (n + 1) ⟶ K n)
    {B : A} (p : ∀ n, B ⟶ K n) (hp : ∀ n, p (n + 1) ≫ f n = p n)
    (hiso : ∃ m : ℕ, ∀ n, m ≤ n → IsIso (p n)) :
    ∃ hz : Pi.lift p ≫ towerTransitionEndomorphism f = 0,
      Nonempty (IsLimit (KernelFork.ofι (Pi.lift p) hz)) := by
  classical
  obtain ⟨m, hm⟩ := hiso
  have : IsIso (p m) := hm m le_rfl
  have hf (n : ℕ) (hn : m ≤ n) : IsIso (f n) := by
    have : IsIso (p (n + 1)) := hm _ (by omega)
    have : IsIso (p n) := hm n hn
    have he : f n = inv (p (n + 1)) ≫ p n := by
      rw [← hp n, IsIso.inv_hom_id_assoc]
    rw [he]
    infer_instance
  have hz : Pi.lift p ≫ towerTransitionEndomorphism f = 0 := by
    apply Pi.hom_ext
    intro n
    simp [towerTransitionEndomorphism, towerProductShift, hp]
  refine ⟨hz, ⟨Fork.IsLimit.mk' _ ?_⟩⟩
  intro s
  let x : ∀ n, s.pt ⟶ K n := fun n ↦ s.ι ≫ Pi.π K n
  have hx (n : ℕ) : x (n + 1) ≫ f n = x n := by
    have hh := s.condition =≫ Pi.π K n
    simp only [towerTransitionEndomorphism, towerProductShift, Preadditive.comp_sub,
      Preadditive.sub_comp, Category.assoc, Category.id_comp, Pi.lift_π,
      comp_zero, zero_comp, sub_eq_zero] at hh
    simpa only [x, Category.assoc] using hh.symm
  let a := x m ≫ inv (p m)
  have ha0 : a ≫ p m = x m := by simp [a]
  have ha (n : ℕ) : a ≫ p n = x n := by
    by_cases hn : m ≤ n
    · induction n, hn using Nat.le_induction with
      | base => exact ha0
      | succ n hn ih =>
        have : IsIso (f n) := hf n hn
        apply (cancel_mono (f n)).mp
        rw [Category.assoc, hp n, hx n, ih]
    · exact Nat.decreasingInduction (motive := fun k _ ↦ a ≫ p k = x k)
        (fun k hk ih ↦ by rw [← hp k, ← Category.assoc, ih, hx k]) ha0
        (show n ≤ m by omega)
  refine ⟨a, ?_, ?_⟩
  · apply Pi.hom_ext
    intro n
    simpa only [KernelFork.ι_ofι, Category.assoc, Pi.lift_π] using ha n
  · intro b hb
    apply (cancel_mono (p m)).mp
    have hh := hb =≫ Pi.π K m
    simpa only [KernelFork.ι_ofι, Category.assoc, Pi.lift_π, a, IsIso.inv_hom_id,
      Category.comp_id] using hh
end CategoryTheory

namespace DerivedCategory
open CategoryTheory.Pretriangulated

private theorem comparison_transition
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (H : DerivedCategory A ⥤ A) [H.Additive]
    {K : ℕ → DerivedCategory A} [HasProduct K] [HasProduct (fun n ↦ H.obj (K n))]
    (f : ∀ n, K (n + 1) ⟶ K n) :
    H.map (towerTransitionEndomorphism f) ≫ piComparison H K =
      piComparison H K ≫ towerTransitionEndomorphism (fun n ↦ H.map (f n)) := by
  apply Pi.hom_ext
  intro n
  simp only [Category.assoc, piComparison_comp_π, towerTransitionEndomorphism,
    towerProductShift, Preadditive.sub_comp, Preadditive.comp_sub, Category.id_comp,
    Pi.lift_π, Functor.map_sub]
  rw [← H.map_comp (Pi.lift _) (Pi.π K n), Pi.lift_π]
  simp only [H.map_comp]
  rw [H.map_id, Category.id_comp, ← Category.assoc, piComparison_comp_π]

private theorem reconstruction_of_eventually_iso
    (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [HasCountableProducts A] [HasCountableProducts (DerivedCategory A)]
    [∀ i : ℤ, PreservesLimitsOfShape (Discrete ℕ) (homologyFunctor A i)]
    (K : ℕ → DerivedCategory A) (f : ∀ n, K (n + 1) ⟶ K n)
    (B : DerivedCategory A) (p : ∀ n, B ⟶ K n)
    (hp : ∀ n, p (n + 1) ≫ f n = p n)
    (hiso : ∀ i : ℤ, ∃ m : ℕ, ∀ n, m ≤ n →
      IsIso ((homologyFunctor A i).map (p n))) :
    ∃ δ : (∏ᶜ K) ⟶ B⟦(1 : ℤ)⟧,
      IsDerivedLimitTriangle f B (Pi.lift p) δ := by
  classical
  obtain ⟨L, q, δ, hL⟩ := (exists_isDerivedLimit_and_iso K f).1
  let T := Triangle.mk q (towerTransitionEndomorphism f) δ
  have hz : Pi.lift p ≫ towerTransitionEndomorphism f = 0 := by
    apply Pi.hom_ext
    intro n
    simp [towerTransitionEndomorphism, towerProductShift, hp]
  obtain ⟨a, ha⟩ := T.coyoneda_exact₂ hL (Pi.lift p) hz
  change Pi.lift p = a ≫ q at ha
  change B ⟶ L at a
  have hiso_f (i : ℤ) : ∃ m : ℕ, ∀ n, m ≤ n →
      IsIso ((homologyFunctor A i).map (f n)) := by
    obtain ⟨m, hm⟩ := hiso i
    refine ⟨m, fun n hn ↦ ?_⟩
    let H := homologyFunctor A i
    have : IsIso (H.map (p n)) := hm n hn
    have : IsIso (H.map (p (n + 1))) := hm _ (by omega)
    have he : H.map (f n) = inv (H.map (p (n + 1))) ≫ H.map (p n) := by
      rw [← hp n, H.map_comp, IsIso.inv_hom_id_assoc]
    rw [he]
    infer_instance
  have hconj (i : ℤ) := comparison_transition (homologyFunctor A i) f
  have hep (i : ℤ) : Epi ((homologyFunctor A i).map (towerTransitionEndomorphism f)) := by
    have := epi_towerTransition_of_eventually_iso
      (K := fun n ↦ (homologyFunctor A i).obj (K n))
      (fun n ↦ (homologyFunctor A i).map (f n)) (hiso_f i)
    have hc : IsIso (piComparison (homologyFunctor A i) K) := inferInstance
    have he := hconj i
    have : Epi ((homologyFunctor A i).map (towerTransitionEndomorphism f) ≫
        piComparison (homologyFunctor A i) K) := by
      rw [he]
      infer_instance
    exact (epi_comp_iff_of_isIso _ (piComparison (homologyFunctor A i) K)).mp this
  have hai : IsIso a := by
    rw [DerivedCategory.isIso_iff]
    intro i
    let H := homologyFunctor A i
    let c := PreservesProduct.iso H K
    let j := H.map q ≫ c.hom
    let t := towerTransitionEndomorphism (K := fun n ↦ H.obj (K n))
      (fun n ↦ H.map (f n))
    have hjz : j ≫ t = 0 := by
      change (H.map q ≫ piComparison H K) ≫
        towerTransitionEndomorphism (K := fun n ↦ H.obj (K n)) (fun n ↦ H.map (f n)) = 0
      rw [Category.assoc, ← hconj i, ← Category.assoc, ← H.map_comp]
      have hzq : q ≫ towerTransitionEndomorphism f = 0 :=
        comp_distTriang_mor_zero₁₂ T hL
      rw [hzq, H.map_zero, zero_comp]
    let S := ShortComplex.mk j t hjz
    have hext : S.Exact := by
      apply ShortComplex.exact_of_iso _ (HomologySequence.exact₂ T hL i)
      refine ShortComplex.isoMk (Iso.refl _) c c ?_ ?_
      · simp [S, j, T, H]
      · exact (hconj i).symm
    have : Mono (H.map q) :=
      (HomologySequence.mono_homologyMap_mor₁_iff T hL (i - 1) i (by omega)).2
        ((HomologySequence.epi_homologyMap_mor₂_iff T hL (i - 1) i (by omega)).1
          (hep (i - 1)))
    have : Mono j := inferInstance
    obtain ⟨hz', ⟨hk⟩⟩ := tower_kernel_of_eventually_iso
      (K := fun n ↦ H.obj (K n)) (fun n ↦ H.map (f n)) (fun n ↦ H.map (p n))
      (fun n ↦ by rw [← H.map_comp, hp]) (hiso i)
    let e := hk.conePointUniqueUpToIso hext.fIsKernel
    have he : H.map a = e.hom := by
      apply (cancel_mono j).mp
      have heq : H.map a ≫ j = Pi.lift (fun n ↦ H.map (p n)) := by
        apply Pi.hom_ext
        intro n
        change (H.map a ≫ H.map q ≫ piComparison H K) ≫
          Pi.π (fun n ↦ H.obj (K n)) n = _
        simp only [Category.assoc, piComparison_comp_π, Pi.lift_π,
          ← H.map_comp]
        rw [← Category.assoc, ← ha, Pi.lift_π]
      rw [heq]
      exact (hk.conePointUniqueUpToIso_hom_comp hext.fIsKernel
        WalkingParallelPair.zero).symm
    rw [he]
    infer_instance
  refine ⟨δ ≫ inv (a⟦(1 : ℤ)⟧'), ?_⟩
  apply isomorphic_distinguished T hL
  refine Triangle.isoMk _ _ (asIso a) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · simpa [T] using ha
  · simp [T]
  · simp [T]

/-- Exact countable products reconstruct an object from its lower truncations.

Source: Stacks Project, Derived Categories, Tags 08TC and 07KC.
(blueprint: new-lem-sfb-exact-products-postnikov-limit)

Proof: exact countable products give derived products commuting with homology.
Complete the Roos transition to a distinguished triangle. The canonical compatible
maps factor through its first object. In every degree the maps from K to its
truncations are eventually invertible. The map 1-shift of such a tower is split
surjective: start at a sufficiently late stage, recurse forward with inverses and
backward over the finitely many early stages. The compatible maps give its kernel.
Exactness of the homology sequence therefore identifies the factorization with an
isomorphism in every degree, hence in the derived category. Transporting the triangle
along this isomorphism retains its canonical maps from K to every truncation.
-/
theorem lowerTruncation_isDerivedLimitTriangle
    (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [HasCountableProducts A] [CountableAB4Star A]
    (K : DerivedCategory A)
    [HasProduct (fun n : ℕ ↦ (TStructure.t.truncGE (-(n : ℤ))).obj K)] :
    ∃ δ : (∏ᶜ (fun n : ℕ ↦ (TStructure.t.truncGE (-(n : ℤ))).obj K)) ⟶ K⟦(1 : ℤ)⟧,
      IsDerivedLimitTriangle
        (fun n : ℕ ↦ (TStructure.t.natTransTruncGEOfLE
          (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega)).app K)
        K (Pi.lift (fun n : ℕ ↦ (TStructure.t.truncGEπ (-(n : ℤ))).app K)) δ := by
  obtain ⟨hP, hproducts, hhomology⟩ := derivedCategory_countableProducts_core A
  let := hP
  let (i : ℤ) : PreservesLimitsOfShape (Discrete ℕ) (homologyFunctor A i) :=
    hhomology ℕ i
  apply reconstruction_of_eventually_iso
  · intro n
    exact TStructure.t.π_natTransTruncGEOfLE_app _ _ _ K
  · intro i
    refine ⟨(-i).toNat, fun n hn ↦ ?_⟩
    exact isIso_homologyFunctor_map_truncGEπ_app K (-(n : ℤ)) i (by omega)

end DerivedCategory

end
