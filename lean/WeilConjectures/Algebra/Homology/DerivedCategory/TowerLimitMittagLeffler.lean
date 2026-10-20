/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.CategoryTheory.CofilteredSystem
public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit

/-!
# Mittag-Leffler towers of modules have vanishing `R¹lim`

For a tower `F` of modules satisfying the Mittag-Leffler condition (the images of the
transition maps `Fₖ ⟶ Fₙ` stabilise), the map `1 - t` on `∏ Fₙ` is surjective, where `t` has
components `∏ Fₘ ⟶ Fₙ₊₁ ⟶ Fₙ`; i.e. `R¹lim Fₙ = coker (1 - t) = 0` (Stacks 0598, 07KW).

The proof first corrects a family `a ∈ ∏ Fₙ`, modulo the image of `1 - t`, into the product of
the stable images `Iₙ`, using finite partial sums `yₙ = ∑_{n ≤ k < Mₙ} t_{k,n}(aₖ)`; the tower
of the stable images has surjective transitions, on which `1 - t` is surjective by the
inductive construction of `ModuleCat.epi_one_sub_of_epi`.

## Main results

- `ModuleCat.epi_one_sub_of_mittagLeffler`: Mittag-Leffler towers have `R¹lim = 0`.
- `ModuleCat.mittagLeffler_of_isMittagLeffler`, `ModuleCat.mittagLeffler_of_finite`: the
  explicit Mittag-Leffler condition from `Functor.IsMittagLeffler`, and for finite modules.
- `ModuleCat.epi_one_sub_of_finite`: towers of finite modules have `R¹lim = 0`.
-/

@[expose] public section

open CategoryTheory Limits Opposite

namespace ModuleCat

universe u

variable {R : Type u} [Ring R]

/-- **Mittag-Leffler towers of modules have `R¹lim = 0`** (Stacks 0598, 07KW). Let `F` be a
tower of modules satisfying the Mittag-Leffler condition: for every `n` there is `N ≥ n` such
that the image of `F_N ⟶ Fₙ` is contained in the image of `Fₖ ⟶ Fₙ` for every `k ≥ n`. Then the
map `1 - t` on a product `∏ Fₙ` is surjective, where `t` has components `∏ Fₘ ⟶ Fₙ₊₁ ⟶ Fₙ`. -/
lemma epi_one_sub_of_mittagLeffler {F : ℕᵒᵖ ⥤ ModuleCat.{u} R}
    {P : Fan fun n : ℕ ↦ F.obj (op n)} (hP : IsLimit P) (t : P.pt ⟶ P.pt)
    (ht : ∀ n : ℕ, t ≫ P.proj n = P.proj (n + 1) ≫ F.map (homOfLE n.le_succ).op)
    (hML : ∀ n : ℕ, ∃ N : ℕ, ∃ hN : n ≤ N, ∀ (k : ℕ) (hk : n ≤ k),
      LinearMap.range (F.map (homOfLE hN).op).hom ≤ LinearMap.range (F.map (homOfLE hk).op).hom) :
    Epi (𝟙 P.pt - t) := by
  classical
  let φ {m n : ℕ} (h : n ≤ m) : F.obj (op m) →ₗ[R] F.obj (op n) := (F.map (homOfLE h).op).hom
  have hφid (n : ℕ) (x : F.obj (op n)) : φ (le_refl n) x = x := by
    simp [φ]
  have hφcomp {k m n : ℕ} (h₁ : n ≤ m) (h₂ : m ≤ k) (x : F.obj (op k)) :
      φ h₁ (φ h₂ x) = φ (h₁.trans h₂) x := by
    have : (homOfLE (h₁.trans h₂)).op = (homOfLE h₂).op ≫ (homOfLE h₁).op := Subsingleton.elim _ _
    simp [φ, this]
  choose N hN hNrange using hML
  -- the stable images and a monotone bound `M n ≥ max (N n) (n + 1)`
  let I (n : ℕ) : Submodule R (F.obj (op n)) := LinearMap.range (φ (hN n))
  let M : ℕ → ℕ := fun n ↦ Nat.rec (N 0 + 1) (fun n Mn ↦ max Mn (N (n + 1) + n + 2)) n
  have hMsucc (n : ℕ) : M n ≤ M (n + 1) := le_max_left _ _
  have hMN (n : ℕ) : N n < M n ∧ n < M n := by
    cases n with
    | zero => exact ⟨Nat.lt_succ_self _, Nat.succ_pos _⟩
    | succ n => exact ⟨lt_of_lt_of_le (by lia) (le_max_right _ _),
        lt_of_lt_of_le (by lia) (le_max_right _ _)⟩
  have hI (n k : ℕ) (hk : N n ≤ k) (x : F.obj (op k)) : φ ((hN n).trans hk) x ∈ I n :=
    ⟨φ hk x, hφcomp _ _ _⟩
  -- the transitions of the stable images are surjective
  have hIsurj (n : ℕ) (x : F.obj (op n)) (hx : x ∈ I n) :
      ∃ z : F.obj (op (n + 1)), z ∈ I (n + 1) ∧ φ n.le_succ z = x := by
    obtain ⟨w, hw⟩ := hNrange n (N (n + 1)) ((n.le_succ).trans (hN (n + 1))) hx
    exact ⟨φ (hN (n + 1)) w, ⟨w, rfl⟩, (hφcomp _ _ _).trans hw⟩
  rw [ModuleCat.epi_iff_surjective]
  intro a
  let ψ (k n : ℕ) : F.obj (op n) := if h : n ≤ k then φ h ((P.proj k).hom a) else 0
  have hψ (k n : ℕ) (h : n + 1 ≤ k) : φ n.le_succ (ψ k (n + 1)) = ψ k n := by
    simp only [ψ, dif_pos h, dif_pos (n.le_succ.trans h), hφcomp]
  let y (n : ℕ) : F.obj (op n) := ∑ k ∈ Finset.Ico n (M n), ψ k n
  -- the correction `b = a - (1 - t) y` lies in the stable images
  let b (n : ℕ) : F.obj (op n) := (P.proj n).hom a - y n + φ n.le_succ (y (n + 1))
  have hb (n : ℕ) : b n ∈ I n := by
    have h₁ : y n = ψ n n + ∑ k ∈ Finset.Ico (n + 1) (M n), ψ k n :=
      Finset.sum_eq_sum_Ico_succ_bot (hMN n).2 _
    have h₂ : φ n.le_succ (y (n + 1)) = ∑ k ∈ Finset.Ico (n + 1) (M n), ψ k n +
        ∑ k ∈ Finset.Ico (M n) (M (n + 1)), ψ k n := by
      rw [map_sum, Finset.sum_Ico_consecutive _ (hMN n).2 (hMsucc n)]
      exact Finset.sum_congr rfl fun k hk ↦ hψ k n (Finset.mem_Ico.1 hk).1
    have hψn : ψ n n = (P.proj n).hom a := by simp only [ψ, dif_pos le_rfl, hφid]
    have hb' : b n = ∑ k ∈ Finset.Ico (M n) (M (n + 1)), ψ k n := by
      simp only [b, h₁, h₂, hψn]
      abel
    rw [hb']
    refine Submodule.sum_mem _ fun k hk ↦ ?_
    have hk' : N n ≤ k := ((hMN n).1.le).trans (Finset.mem_Ico.1 hk).1
    simp only [ψ, dif_pos ((hN n).trans hk')]
    exact hI n k hk' _
  -- solve `x - t x = b` inside the stable images
  let x : ∀ n : ℕ, I n := fun n ↦ Nat.rec (motive := fun n ↦ I n) 0
    (fun n xn ↦ ⟨(hIsurj n _ (Submodule.sub_mem _ xn.2 (hb n))).choose,
      (hIsurj n _ (Submodule.sub_mem _ xn.2 (hb n))).choose_spec.1⟩) n
  have hx (n : ℕ) : φ n.le_succ (x (n + 1) : F.obj (op (n + 1))) = x n - b n :=
    (hIsurj n _ (Submodule.sub_mem _ (x n).2 (hb n))).choose_spec.2
  obtain ⟨z, hz⟩ := exists_proj_eq_of_isLimit_fan hP fun n ↦ y n + x n
  refine ⟨z, ext_of_isLimit_fan hP fun n ↦ ?_⟩
  have h₁ := congrArg (fun f ↦ f.hom z) (ht n)
  simp only [hom_comp, LinearMap.coe_comp, Function.comp_apply] at h₁
  simp only [hom_sub, hom_id, LinearMap.sub_apply, LinearMap.id_apply, map_sub, h₁, hz]
  have := hx n
  simp only [φ] at this
  rw [map_add, this]
  simp only [b, φ]
  abel

/-- The Mittag-Leffler condition of Mathlib (`CategoryTheory.Functor.IsMittagLeffler`, for the
underlying tower of sets) for a tower of modules, in the explicit form used by
`ModuleCat.epi_one_sub_of_mittagLeffler`: for every `n` there is `N ≥ n` such that the image
of `F_N ⟶ Fₙ` is contained in the image of `Fₖ ⟶ Fₙ` for every `k ≥ n`. -/
lemma mittagLeffler_of_isMittagLeffler {F : ℕᵒᵖ ⥤ ModuleCat.{u} R}
    (h : (F ⋙ forget (ModuleCat.{u} R)).IsMittagLeffler) (n : ℕ) :
    ∃ N : ℕ, ∃ hN : n ≤ N, ∀ (k : ℕ) (hk : n ≤ k),
      LinearMap.range (F.map (homOfLE hN).op).hom ≤
        LinearMap.range (F.map (homOfLE hk).op).hom := by
  obtain ⟨i, g, hg⟩ := h (op n)
  have hg' : g = (homOfLE (leOfHom g.unop)).op := Subsingleton.elim _ _
  refine ⟨i.unop, leOfHom g.unop, fun k hk ↦ ?_⟩
  rintro _ ⟨y, rfl⟩
  obtain ⟨z, hz⟩ := hg (homOfLE hk).op (⟨y, by rw [hg']⟩ : _ ∈ Set.range _)
  exact ⟨z, hz⟩

/-- **Towers of finite modules are Mittag-Leffler**, in the explicit form used by
`ModuleCat.epi_one_sub_of_mittagLeffler` (Stacks 0596). -/
lemma mittagLeffler_of_finite {F : ℕᵒᵖ ⥤ ModuleCat.{u} R} (h : ∀ n : ℕ, Finite (F.obj (op n)))
    (n : ℕ) :
    ∃ N : ℕ, ∃ hN : n ≤ N, ∀ (k : ℕ) (hk : n ≤ k),
      LinearMap.range (F.map (homOfLE hN).op).hom ≤
        LinearMap.range (F.map (homOfLE hk).op).hom :=
  mittagLeffler_of_isMittagLeffler (Functor.isMittagLeffler_of_exists_finite_range (F ⋙ forget _)
    fun j ↦ ⟨j, 𝟙 j, @Set.finite_range _ _ _ (h j.unop)⟩) n

/-- **Towers of finite modules have `R¹lim = 0`** (Stacks 0596, 0598): for a tower `F` of
finite modules, the map `1 - t` on a product `∏ Fₙ` is surjective, where `t` has components
`∏ Fₘ ⟶ Fₙ₊₁ ⟶ Fₙ`. -/
lemma epi_one_sub_of_finite {F : ℕᵒᵖ ⥤ ModuleCat.{u} R}
    {P : Fan fun n : ℕ ↦ F.obj (op n)} (hP : IsLimit P) (t : P.pt ⟶ P.pt)
    (ht : ∀ n : ℕ, t ≫ P.proj n = P.proj (n + 1) ≫ F.map (homOfLE n.le_succ).op)
    (h : ∀ n : ℕ, Finite (F.obj (op n))) : Epi (𝟙 P.pt - t) :=
  epi_one_sub_of_mittagLeffler hP t ht (mittagLeffler_of_finite h)

end ModuleCat
