/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Exact.Basic
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.FrobeniusModuleWeightsEmbedding

/-!
# Extension bounds for mixed Frobenius modules

Source: latest blueprint, unit `sk-thm-wft-affine-curve-upper`, final paragraph,
extension of the boundary-image bound to the middle cohomology group
(blueprint: lem-a1-embedding-extension-bounds).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u₁ u₂ u₃ v

namespace FrobeniusModule

/-- An extension of two Frobenius modules mixed of weights at most `w` is mixed
of weights at most `w`.

Source: latest blueprint, `sk-thm-wft-affine-curve-upper.proof.md`, final paragraph,
extension of the upper bound from the boundary image and the affine-line term
(blueprint: lem-a1-embedding-extension-bounds).

Proof: choose the finite Frobenius-stable filtrations of `A` and `C` supplied
by `def-weil-frobenius-module-weights`. Map the filtration of `A` into `B` by
`f`, and follow it by the inverse images under `g` of the filtration of `C`.
Injectivity of `f`, exactness at `B`, and surjectivity of `g` identify the
joining subspaces and the successive quotients with those of `A` and `C`.
Equivariance of both maps makes this a Frobenius-stable filtration with the
same induced Frobenius on those quotients. Every graded piece is therefore
pure of a weight at most `w`; the definition gives mixedness of `B`.
-/
theorem IsMixedOfWeightsAtMostEmbedding.of_shortExact
    {K : Type v} [Field K] (iota : K →+* ℂ) (q : ℕ)
    (A : FrobeniusModule.{u₁, v} K) (B : FrobeniusModule.{u₂, v} K)
    (C : FrobeniusModule.{u₃, v} K)
    (f : A.carrier →ₗ[K] B.carrier) (g : B.carrier →ₗ[K] C.carrier)
    (hf : ∀ x : A.carrier, f (A.frobenius x) = B.frobenius (f x))
    (hg : ∀ x : B.carrier, g (B.frobenius x) = C.frobenius (g x))
    (hinj : Function.Injective f) (hexact : Function.Exact f g)
    (hsurj : Function.Surjective g) (w : ℝ)
    (hA : IsMixedOfWeightsAtMostEmbedding iota q A w)
    (hC : IsMixedOfWeightsAtMostEmbedding iota q C w) :
    IsMixedOfWeightsAtMostEmbedding iota q B w := by
  classical
  obtain ⟨m, V, hV0, hVm, hVle, hVs, hVp⟩ := hA
  obtain ⟨n, Z, hZ0, hZn, hZle, hZs, hZp⟩ := hC
  simp only [Fin.last] at hVm hZn
  have hjoin : (V ⟨m, Nat.lt_succ_self m⟩).map f = (Z 0).comap g := by
    rw [hVm, hZ0, Submodule.map_top, Submodule.comap_bot]
    exact (LinearMap.exact_iff.mp hexact).symm
  let W : Fin (m + n + 1) → Submodule K B.carrier := fun i ↦
    if h : i.val ≤ m then (V ⟨i.val, by omega⟩).map f
    else (Z ⟨i.val - m, by omega⟩).comap g
  have hleft (i : Fin (m + 1)) :
      W ⟨i.val, by omega⟩ = (V i).map f := by
    dsimp [W]
    rw [dif_pos (by omega)]
  have hright (i : Fin (n + 1)) :
      W ⟨m + i.val, by omega⟩ = (Z i).comap g := by
    by_cases hi : i.val = 0
    · have hi0 : i = 0 := Fin.ext hi
      subst i
      simpa only [Fin.val_zero, Nat.add_zero] using (hleft ⟨m, by omega⟩).trans hjoin
    · dsimp [W]
      rw [dif_neg (by omega)]
      congr 2
      exact Fin.ext (by dsimp; omega)
  have hWL (i : Fin (m + n + 1)) (hi : i.val ≤ m) :
      W i = (V ⟨i.val, by omega⟩).map f := hleft ⟨i.val, by omega⟩
  have hWR (i : Fin (m + n + 1)) (hi : m ≤ i.val) :
      W i = (Z ⟨i.val - m, by omega⟩).comap g := by
    have he : (⟨m + (i.val - m), by omega⟩ : Fin (m + n + 1)) = i := by
      apply Fin.ext
      change m + (i.val - m) = i.val
      omega
    exact (congrArg W he).symm.trans (hright ⟨i.val - m, by omega⟩)
  refine ⟨m + n, W, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hleft 0).trans (by rw [hV0, Submodule.map_bot])
  · simp only [Fin.last]
    rw [hWR ⟨m + n, by omega⟩ (by simp)]
    have he : (⟨m + n - m, by omega⟩ : Fin (n + 1)) = ⟨n, by omega⟩ :=
      Fin.ext (by simp)
    rw [he, hZn, Submodule.comap_top]
  · intro r
    by_cases hr : r.val < m
    · rw [hWL r.castSucc (by dsimp; omega), hWL r.succ (by dsimp; omega)]
      exact Submodule.map_mono (hVle ⟨r.val, hr⟩)
    · rw [hWR r.castSucc (by dsimp; omega), hWR r.succ (by dsimp; omega)]
      let j : Fin n := ⟨r.val - m, by omega⟩
      have hj : (⟨r.succ.val - m, by omega⟩ : Fin (n + 1)) = j.succ :=
        Fin.ext (by dsimp [j]; omega)
      rw [hj]
      exact Submodule.comap_mono (f := g) (hZle j)
  · intro i
    by_cases hi : i.val ≤ m
    · rw [hWL i hi]
      exact stable_map A B f hf _ (hVs _)
    · rw [hWR i (by omega)]
      exact stable_comap B C g hg _ (hZs _)
  · intro r
    change boundedPurePiece iota q w B _ _
    by_cases hr : r.val < m
    · rw [hWL r.castSucc (by dsimp; omega), hWL r.succ (by dsimp; omega)]
      let j : Fin m := ⟨r.val, hr⟩
      let T : V j.succ →ₗ[K] (V j.succ).map f :=
        (f.comp (V j.succ).subtype).codRestrict _ (fun x ↦ ⟨x, x.2, rfl⟩)
      have hTi : Function.Injective T := fun x y h ↦
        Subtype.ext (hinj (congrArg Subtype.val h))
      have hTs : Function.Surjective T := by
        rintro ⟨y, hy⟩
        obtain ⟨x, hx, rfl⟩ := hy
        exact ⟨⟨x, hx⟩, rfl⟩
      let e := LinearEquiv.ofBijective T ⟨hTi, hTs⟩
      have he (x : V j.succ) : (e x : B.carrier) = f x := rfl
      have hei (x : (V j.succ).map f) : f (e.symm x) = (x : B.carrier) :=
        congrArg Subtype.val (e.apply_symm_apply x)
      apply transport_piece iota q w B A
        ((V j.castSucc).map f) ((V j.succ).map f) (V j.castSucc) (V j.succ)
        e.symm.toLinearMap e.symm.surjective
      · intro x hx
        apply hinj
        change f (e.symm ⟨B.frobenius x, hx⟩) = f (A.frobenius (e.symm x))
        rw [hei, hf, hei]
      · intro x
        constructor
        · intro hx
          exact ⟨e.symm x, hx, hei x⟩
        · rintro ⟨y, hy, hey⟩
          have heq : y = (e.symm x : A.carrier) := hinj (hey.trans (hei x).symm)
          exact heq ▸ hy
      · exact hVp j
    · rw [hWR r.castSucc (by dsimp; omega), hWR r.succ (by dsimp; omega)]
      let j : Fin n := ⟨r.val - m, by omega⟩
      have hj : (⟨r.succ.val - m, by omega⟩ : Fin (n + 1)) = j.succ :=
        Fin.ext (by dsimp [j]; omega)
      rw [hj]
      let T : (Z j.succ).comap g →ₗ[K] Z j.succ :=
        (g.comp ((Z j.succ).comap g).subtype).codRestrict _ (fun x ↦ x.2)
      apply transport_piece iota q w B C
        ((Z j.castSucc).comap g) ((Z j.succ).comap g) (Z j.castSucc) (Z j.succ) T
      · intro y
        obtain ⟨x, hx⟩ := hsurj y
        exact ⟨⟨x, by change g x ∈ Z j.succ; rw [hx]; exact y.2⟩, Subtype.ext hx⟩
      · intro x hx
        exact hg x
      · intro x
        rfl
      · exact hZp j

end FrobeniusModule
