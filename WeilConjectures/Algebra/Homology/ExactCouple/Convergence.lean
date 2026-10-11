/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.ExactCouple.Basic
public import WeilConjectures.CategoryTheory.Abelian.Filtration

/-!
# Convergence of the spectral sequence of an exact couple

We consider exact couples indexed by `ℤ × ℤ` whose map `α` has degree `(-1, 0)` and whose map `g`
has degree `0`. We think of an index `(p, n)` as a filtration degree `p` and a total degree `n`:
the bigraded couples of the blueprint, indexed by `(p, q)` with `α` of degree `(-1, 1)`,
correspond to these through `(p, q) ↦ (p, p + q)`.

Such a couple has an *abutment* in total degree `n` when the objects `D^{p, n}` vanish for
`p ≫ 0` and become constant, equal to `Aⁿ`, for `p ≪ 0`. The abutment is filtered by the images
`Fᵖ Aⁿ = im (D^{p, n} ⟶ Aⁿ)`, and the spectral sequence of the couple converges to this
filtration: each entry `E_r^{p, n}` eventually has vanishing incoming and outgoing
differentials, and is then the graded piece `grᵖ Aⁿ`
(`CategoryTheory.ExactCouple.convergesTo_abutmentFiltration`).

## Main definitions

- `CategoryTheory.ExactCouple.IsRegular`, `CategoryTheory.ExactCouple.IsComplete`,
  `CategoryTheory.ExactCouple.ConvergesTo`: regular and complete couples, and convergence of
  the spectral sequence of a couple to a filtration.
- `CategoryTheory.ExactCouple.abutmentFiltration`: the filtration of the abutment by the images
  of the `D`-objects.

## Main statements

- `CategoryTheory.ExactCouple.convergesTo_abutmentFiltration`: convergence of the spectral
  sequence of a couple which is bounded in each total degree.
-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

lemma IsZero.of_epi {X Y : C} (π : X ⟶ Y) [Epi π] (hX : IsZero X) : IsZero Y := by
  rw [IsZero.iff_id_eq_zero, ← cancel_epi π]
  exact hX.eq_of_src _ _

/-- The cokernel of the inclusion of two subobjects given by monomorphisms `u` and `v` is the
cokernel of a morphism `φ` with `φ ≫ v = u`. -/
lemma nonempty_cokernel_ofLE_iso {A U V : C} (u : U ⟶ A) (v : V ⟶ A) [Mono u] [Mono v]
    (φ : U ⟶ V) (hφ : φ ≫ v = u) (P Q : Subobject A) (hP : P = Subobject.mk u)
    (hQ : Q = Subobject.mk v) (h : P ≤ Q) :
    Nonempty (cokernel (Subobject.ofLE P Q h) ≅ cokernel φ) := by
  subst hP hQ
  refine ⟨cokernel.mapIso _ _ (Subobject.underlyingIso u) (Subobject.underlyingIso v) ?_⟩
  rw [← cancel_mono v]
  simp [hφ]

namespace ExactCouple

variable {b : ℤ × ℤ} (X : ExactCouple C ((-1, 0) : ℤ × ℤ) b 0)

/-- A couple is *regular* if for every index `i`, the differentials `d_r` arriving at `i` vanish
for `r ≫ 0`; equivalently, the boundaries `B_r ⊆ E` at `i` are eventually constant.

(blueprint: `def-sp-convergence`) -/
def IsRegular : Prop :=
  ∀ i : ℤ × ℤ, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ j, (X.derivedIter n).d j i = 0

/-- A couple is *complete* if for every index `i` the images of the composites
`αʳ : D (i + (r, 0)) ⟶ D i` have zero intersection.

(blueprint: `def-sp-convergence`) -/
def IsComplete : Prop :=
  ∀ (i : ℤ × ℤ) (P : Subobject (X.D i)),
    (∀ r : ℕ, P ≤ imageSubobject (X.αPow r (i + ((r : ℤ), 0)) i)) → P = ⊥

/-- The spectral sequence of the couple *converges* to the filtrations `F n` of the objects
`A n`: for every index `(p, n)` (filtration degree `p`, total degree `n`), from some derived
couple on, the differentials leaving and arriving at `(p, n)` vanish (so that the entry has
reached its stable value `E_∞^{p, n}`), and this stable value is the graded piece `grᵖ Aⁿ`.

This is the convention for a couple whose map `g` has degree `0`.

(blueprint: `def-sp-convergence`) -/
def ConvergesTo (A : ℤ → C) (F : ∀ n, DecreasingFiltration (A n)) : Prop :=
  ∀ p n : ℤ, ∃ N₀ : ℕ, ∀ N ≥ N₀, (∀ j, (X.derivedIter N).d (p, n) j = 0) ∧
    (∀ j, (X.derivedIter N).d j (p, n) = 0) ∧
    Nonempty ((X.derivedIter N).E (p, n) ≅ (F n).gr p)

section Abutment

variable {A : ℤ → C} (ι : ∀ p n : ℤ, X.D (p, n) ⟶ A n)
  (hι : ∀ p n : ℤ, X.α (p + 1, n) (p, n) ≫ ι p n = ι (p + 1) n)

include hι in
lemma αPow_comp (N : ℕ) (p p' n : ℤ) (h : p' + N = p) :
    X.αPow N (p, n) (p', n) ≫ ι p' n = ι p n := by
  induction N generalizing p' with
  | zero =>
    obtain rfl : p' = p := by simpa using h
    simp [αPow]
  | succ N ih =>
    simp only [αPow, Category.assoc]
    rw [show ((p', n) : ℤ × ℤ) - ((-1, 0) : ℤ × ℤ) = (p' + 1, n) by ext <;> simp, hι,
      ih (p' + 1) (by push_cast at h; omega)]

/-- The filtration of the abutment `Aⁿ` by the images `Fᵖ Aⁿ = im (D^{p, n} ⟶ Aⁿ)`. -/
noncomputable def abutmentFiltration (n : ℤ) : DecreasingFiltration (A n) where
  F p := imageSubobject (ι p n)
  F_succ_le p := by
    rw [← hι p n]
    exact imageSubobject_comp_le _ _

include hι in
lemma imageSubobject_ι_eq_mk (N : ℕ) (p p' n : ℤ) (h : p' + N = p) [IsIso (ι p' n)] :
    imageSubobject (ι p n) = Subobject.mk (X.ιIter N (p', n) ≫ ι p' n) := by
  obtain ⟨π, _, hπ⟩ := X.exists_epi_comp_ιIter N (p, n) (p', n)
    (by ext <;> simp; omega)
  rw [← X.αPow_comp ι hι N p p' n h, ← hπ, Category.assoc, imageSubobject_comp_eq_of_epi,
    imageSubobject_mono]

/-- **Convergence of the spectral sequence of a bounded exact couple.** Let `X` be an exact
couple indexed by `ℤ × ℤ` with `α` of degree `(-1, 0)` and `g` of degree `0`, and let
`ι : D^{p, n} ⟶ Aⁿ` be compatible with `α`. Suppose that in each total degree `n`, the maps
`ι` are isomorphisms for `p ≪ 0` and the objects `D^{p, n}` vanish for `p ≫ 0`. Then the
spectral sequence of `X` converges to the filtration `Fᵖ Aⁿ = im (D^{p, n} ⟶ Aⁿ)`.

(blueprint: `def-sp-convergence`) -/
theorem convergesTo_abutmentFiltration
    (hiso : ∀ n : ℤ, ∃ m : ℤ, ∀ p ≤ m, IsIso (ι p n))
    (hzero : ∀ n : ℤ, ∃ M : ℤ, ∀ p ≥ M, IsZero (X.D (p, n))) :
    X.ConvergesTo A (X.abutmentFiltration ι hι) := by
  intro p n
  obtain ⟨m, hm⟩ := hiso n
  obtain ⟨M, hM⟩ := hzero (n + b.2)
  refine ⟨(p - m + 1).toNat + (M - p - b.1).toNat, fun N hN ↦ ?_⟩
  have hN₁ : p - N + 1 ≤ m := by omega
  have hN₂ : M ≤ p + b.1 + N := by omega
  have hdegg : ExactCouple.degIter ((-1, 0) : ℤ × ℤ) (0 : ℤ × ℤ) N = ((N : ℤ), 0) := by
    rw [degIter_eq]
    ext <;> simp
  let u : ℤ × ℤ := (p + b.1, n + b.2)
  have hu : IsZero ((X.derivedIter N).D u) := by
    obtain ⟨π, _, -⟩ := X.exists_epi_comp_ιIter N (p + b.1 + N, n + b.2) u
      (by ext <;> simp [u])
    exact IsZero.of_epi π (hM _ (by omega))
  have hf₀ : (X.derivedIter N).f (p, n) u = 0 := hu.eq_of_tgt _ _
  have : IsIso (ι (p - N) n) := hm _ (by omega)
  have : IsIso (ι (p - N + 1) n) := hm _ (by omega)
  have : IsIso (ι (p - N - 1) n) := hm _ (by omega)
  -- the inclusions of the `D`-objects of `Y` into the abutment
  have hj (p' : ℤ) : (X.derivedIter N).α (p' + 1, n) (p', n) ≫ X.ιIter N (p', n) ≫ ι p' n =
      X.ιIter N (p' + 1, n) ≫ ι (p' + 1) n := by
    rw [X.α_ιIter_assoc, hι]
  refine ⟨fun j ↦ ?_, fun j ↦ ?_, ?_⟩
  · rw [(X.derivedIter N).d_eq (p, n) u j (by ext <;> simp [u]), hf₀, zero_comp]
  · by_cases h : j + b = (p - N, n)
    · have : Mono ((X.derivedIter N).α (p - N, n) (p - N - 1, n)) := by
        have := hj (p - N - 1)
        rw [sub_add_cancel] at this
        exact mono_of_mono_fac this
      have hf : (X.derivedIter N).f j (p - N, n) = 0 := by
        rw [← cancel_mono ((X.derivedIter N).α (p - N, n) (p - N - 1, n)), zero_comp]
        exact (X.derivedIter N).f_α _ _ _
      rw [(X.derivedIter N).d_eq j (p - N, n) _ h, hf, zero_comp]
    · rw [(X.derivedIter N).d_eq j (j + b) _ rfl, (X.derivedIter N).shape_g, comp_zero]
      intro h'
      apply h
      rw [hdegg] at h'
      ext
      · have := congrArg _root_.Prod.fst h'
        simp at this
        simp
        omega
      · have := congrArg _root_.Prod.snd h'
        simp at this
        simpa using this
  · have hexact₁ := (X.derivedIter N).exact_α_g (p - N + 1, n) (p - N, n) (p, n) (by ext <;> simp)
      (by rw [hdegg]; ext <;> simp)
    have hexact₂ := (X.derivedIter N).exact_g_f (p - N, n) (p, n) u (by rw [hdegg]; ext <;> simp)
      (by ext <;> simp [u])
    have : Epi ((X.derivedIter N).g (p - N, n) (p, n)) := hexact₂.epi_f hf₀
    let e₁ : (X.derivedIter N).E (p, n) ≅ cokernel ((X.derivedIter N).α (p - N + 1, n) (p - N, n)) :=
      (hexact₁.gIsCokernel).coconePointUniqueUpToIso (colimit.isColimit _)
    obtain ⟨e₂⟩ := nonempty_cokernel_ofLE_iso (X.ιIter N (p - N + 1, n) ≫ ι (p - N + 1) n)
      (X.ιIter N (p - N, n) ≫ ι (p - N) n) ((X.derivedIter N).α (p - N + 1, n) (p - N, n)) (hj (p - N))
      ((X.abutmentFiltration ι hι n).F (p + 1)) ((X.abutmentFiltration ι hι n).F p)
      (X.imageSubobject_ι_eq_mk ι hι N (p + 1) (p - N + 1) n (by omega))
      (X.imageSubobject_ι_eq_mk ι hι N p (p - N) n (by omega))
      ((X.abutmentFiltration ι hι n).F_succ_le p)
    exact ⟨e₁ ≪≫ e₂.symm⟩

end Abutment

end ExactCouple

end CategoryTheory
