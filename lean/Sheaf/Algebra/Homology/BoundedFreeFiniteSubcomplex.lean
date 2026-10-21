/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic

/-!
# Finite free subcomplexes of a bounded-above free complex

Source: Stacks Project, Tag 0FNR, `more-algebra.tex`,
`lemma-complex-bounded-above-free-colim-bounded-finite-free`
(blueprint: lem-zl-bounded-free-finite-subcomplex).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace CochainComplex

-- A finite collection of vectors uses only finitely many coordinates of a basis.
private theorem finite_coordinate_submodule
    {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]
    [Module.Free A M] (s : Set M) (hs : s.Finite) :
    ∃ (E : Submodule A M) (y : Finset M),
      s ⊆ E ∧ Submodule.span A (↑y : Set M) = E ∧
      ∃ r : ℕ, Nonempty (E ≃ₗ[A] (Fin r → A)) := by
  classical
  let b := Module.Free.chooseBasis A M
  let J := hs.toFinset.biUnion (fun x ↦ (b.repr x).support)
  let y := J.image b
  have hy : (↑y : Set M) = Set.range (fun i : J ↦ b i) := by
    ext x
    simp only [y, Finset.mem_coe, Finset.mem_image, Set.mem_range]
    exact ⟨fun ⟨i, hi, h⟩ ↦ ⟨⟨i, hi⟩, h⟩, fun ⟨i, h⟩ ↦ ⟨i, i.2, h⟩⟩
  let E := Submodule.span A (Set.range (fun i : J ↦ b i))
  have hb := b.linearIndependent.comp (fun i : J ↦ i.val) Subtype.val_injective
  let basis : Module.Basis J A E := Module.Basis.span hb
  refine ⟨E, y, ?_, congrArg (Submodule.span A) hy, Fintype.card J,
    ⟨(basis.reindex (Fintype.equivFin J)).equivFun⟩⟩
  intro x hx
  change x ∈ Submodule.span A (Set.range (fun i : J ↦ b i))
  rw [← hy]
  have hsupport : b '' (↑(b.repr x).support : Set _) ⊆ (↑y : Set M) := by
    rintro _ ⟨i, hi, rfl⟩
    exact Finset.mem_image.mpr ⟨i, Finset.mem_biUnion.mpr
      ⟨x, hs.mem_toFinset.mpr hx, hi⟩, rfl⟩
  exact Submodule.span_mono hsupport (b.mem_span_repr_support x)

private theorem bottom_finite_free
    {A : Type u} [CommRing A] (M : Type v) [AddCommGroup M] [Module A M] :
    ∃ r : ℕ, Nonempty ((⊥ : Submodule A M) ≃ₗ[A] (Fin r → A)) :=
  ⟨0, ⟨LinearEquiv.ofSubsingleton _ _⟩⟩

/-- Every finite list of homogeneous elements of a bounded-above free complex lies in a
bounded subcomplex with finite free terms. The subcomplex is specified by its submodules
and their stability under the differential; its differentials are the restrictions of `F.d`.
Source: Stacks Project, Tag 0FNR,
`lemma-complex-bounded-above-free-colim-bounded-finite-free`.
(blueprint: lem-zl-bounded-free-finite-subcomplex).

Proof. For an empty list take the zero subcomplex. Otherwise choose a lower degree `a`
below all input degrees and at most `b + 1`, where `F` vanishes above `b`. Prove by descending
induction on `t`, from `b + 1` down to `a`, that every finite list in degrees at least `t`
lies in a finite free subcomplex supported in `[t, b]`. The base case is the zero complex.
For the induction step choose a basis of `F.X t` and the finite union `J` of the coordinate
supports of the inputs in degree `t`. Its coordinate submodule `E` is finite free, with
coordinates indexed by `J`. Choose a basis of `F.X (t + 1)` and the finite union `K` of the
supports of the differentials of these chosen basis elements. Apply the induction hypothesis
to the basis elements indexed by `K`, together with all original inputs in higher degrees,
obtaining `H`. Set `G` equal to zero below `t`, to `E` in degree `t`, and to `H` above `t`.
Differential stability below `t` follows from the zero domain, at `t` from the coordinate
expansions of the differentials in the span of `K`, and above `t` from stability of `H`.
The restricted differentials square to zero by the cochain identity of
`def-weil-abstract-derived-category`. All inputs belong to `G`; its terms are finite free
and vanish outside `[t, b]`. The finitely many induction steps give the result. Enumerating
each finite coordinate set identifies its module with `Fin r → A` for its cardinality `r`.
-/
theorem exists_bounded_finite_free_subcomplex
    {A : Type u} [CommRing A] (F : CochainComplex (ModuleCat.{v} A) ℤ)
    (hbounded : ∃ b : ℤ, ∀ n : ℤ, b < n → Subsingleton (F.X n))
    (hfree : ∀ n : ℤ, Module.Free A (F.X n))
    (xs : List (Σ n : ℤ, F.X n)) :
    ∃ G : (n : ℤ) → Submodule A (F.X n),
      (∀ p ∈ xs, p.2 ∈ G p.1) ∧
      (∀ n : ℤ, (G n).map (F.d n (n + 1)).hom ≤ G (n + 1)) ∧
      (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → G n = ⊥) ∧
      (∀ n : ℤ, ∃ r : ℕ, Nonempty ((G n) ≃ₗ[A] (Fin r → A))) := by
  classical
  obtain ⟨b, hb⟩ := hbounded
  let P : ℤ → Prop := fun t ↦
    ∀ (s : Set (Σ n : ℤ, F.X n)), s.Finite → (∀ p ∈ s, t ≤ p.1) →
    ∃ G : (n : ℤ) → Submodule A (F.X n),
      (∀ p ∈ s, p.2 ∈ G p.1) ∧
      (∀ n : ℤ, (G n).map (F.d n (n + 1)).hom ≤ G (n + 1)) ∧
      (∀ n : ℤ, n < t ∨ b < n → G n = ⊥) ∧
      (∀ n : ℤ, ∃ r : ℕ, Nonempty ((G n) ≃ₗ[A] (Fin r → A)))
  have base : P (b + 1) := by
    intro s hs hdeg
    refine ⟨fun _ ↦ ⊥, ?_, ?_, ?_, fun n ↦ bottom_finite_free (F.X n)⟩
    · intro p hp
      have := hb p.1 (by have := hdeg p hp; omega)
      exact Subsingleton.elim _ _
    · intro n
      simp
    · intro n hn
      rfl
  have step : ∀ t : ℤ, t ≤ b → P (t + 1) → P t := by
    intro t ht ih s hs hdeg
    have : Module.Free A (F.X t) := hfree t
    have hs₀ : (Sigma.mk t ⁻¹' s).Finite :=
      hs.preimage (fun x _ y _ h ↦ by simpa using h)
    obtain ⟨E, y, hE, hy, r, hr⟩ := finite_coordinate_submodule (A := A) _ hs₀
    let d := (F.d t (t + 1)).hom
    let s' : Set (Σ n : ℤ, F.X n) :=
      {p ∈ s | t < p.1} ∪ (Sigma.mk (t + 1)) '' (d '' (↑y : Set (F.X t)))
    have hs' : s'.Finite :=
      (hs.subset (by intro p hp; exact hp.1)).union
        ((y.finite_toSet.image d).image (Sigma.mk (t + 1)))
    have hdeg' : ∀ p ∈ s', t + 1 ≤ p.1 := by
      intro p hp
      rcases hp with hp | ⟨z, hz, rfl⟩
      · have := hp.2
        omega
      · exact le_refl _
    obtain ⟨H, hH, hdH, hsuppH, hfreeH⟩ := ih s' hs' hdeg'
    let G : (n : ℤ) → Submodule A (F.X n) :=
      fun n ↦ if h : n = t then h.symm ▸ E else H n
    have hGt : G t = E := by simp [G]
    have hGne : ∀ n : ℤ, n ≠ t → G n = H n := by
      intro n hn
      simp [G, hn]
    refine ⟨G, ?_, ?_, ?_, ?_⟩
    · intro p hp
      by_cases heq : p.1 = t
      · rcases p with ⟨n, x⟩
        dsimp at heq
        subst n
        rw [hGt]
        exact hE hp
      · rw [hGne p.1 heq]
        exact hH p (Or.inl ⟨hp, lt_of_le_of_ne (hdeg p hp) (Ne.symm heq)⟩)
    · intro n
      by_cases hn : n < t
      · rw [hGne n (by omega), hsuppH n (Or.inl (by omega))]
        simp
      by_cases heq : n = t
      · subst n
        rw [hGt, hGne (t + 1) (by omega), ← hy]
        rw [Submodule.map_le_iff_le_comap, Submodule.span_le]
        intro z hz
        exact hH ⟨t + 1, d z⟩ (Or.inr ⟨d z, ⟨z, hz, rfl⟩, rfl⟩)
      · rw [hGne n heq, hGne (n + 1) (by omega)]
        exact hdH n
    · intro n hn
      rw [hGne n (by omega)]
      exact hsuppH n (by omega)
    · intro n
      by_cases hn : n = t
      · subst n
        rw [hGt]
        exact ⟨r, hr⟩
      · rw [hGne n hn]
        exact hfreeH n
  have descend : ∀ t : ℤ, t ≤ b + 1 → P t := by
    refine Int.leInductionDown (motive := fun t _ ↦ P t) base ?_
    intro t ht ih
    apply step (t - 1) (by omega)
    convert ih using 1; omega
  have lower : ∃ a : ℤ, a ≤ b + 1 ∧ ∀ p ∈ xs, a ≤ p.1 := by
    induction xs with
    | nil => exact ⟨b + 1, le_refl _, by simp⟩
    | cons p xs ih =>
      obtain ⟨a, ha, hxs⟩ := ih
      refine ⟨min p.1 a, (min_le_right _ _).trans ha, ?_⟩
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (hxs q hq)
  obtain ⟨a, ha, hxs⟩ := lower
  obtain ⟨G, hG, hdG, hsuppG, hfreeG⟩ :=
    descend a ha {p | p ∈ xs} (List.finite_toSet xs) hxs
  exact ⟨G, hG, hdG, ⟨a, b, hsuppG⟩, hfreeG⟩

end CochainComplex
