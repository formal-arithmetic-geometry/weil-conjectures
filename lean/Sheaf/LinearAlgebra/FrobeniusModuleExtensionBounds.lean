/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Sheaf.LinearAlgebra.FrobeniusModuleWeights

/-!
# Extension bounds for mixed Frobenius modules

Source: Weil-conjectures blueprint, chapter `sec-deligne-laumon-a1`, unit
`sk-thm-dl-a1-upper`, lemma `lem-a1-extension-bounds`, order 3134 in
`main-20261015` (blueprint: lem-a1-extension-bounds).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u₁ u₂ u₃ v

namespace FrobeniusModule

private theorem transport_piece
    {K : Type v} [Field K] (iota : K →+* ℂ) (q : ℕ) (w : ℝ)
    (M : FrobeniusModule.{u₁, v} K) (N : FrobeniusModule.{u₂, v} K)
    (L U : Submodule K M.carrier) (L' U' : Submodule K N.carrier)
    (f : U →ₗ[K] U') (hsurj : Function.Surjective f)
    (hf : ∀ (x : U) (hx : M.frobenius (x : M.carrier) ∈ U),
      (f ⟨M.frobenius x, hx⟩ : N.carrier) = N.frobenius (f x))
    (hL : ∀ x : U, (f x : N.carrier) ∈ L' ↔ (x : M.carrier) ∈ L)
    (hpiece : ∃ (t : ℝ)
      (G : (U' ⧸ L'.comap U'.subtype) ≃ₗ[K] (U' ⧸ L'.comap U'.subtype)),
      t ≤ w ∧ (∀ (x : U') (hx : N.frobenius (x : N.carrier) ∈ U'),
        G (Submodule.Quotient.mk x) =
          Submodule.Quotient.mk ⟨N.frobenius x, hx⟩) ∧
      (FrobeniusModule.mk _ G).IsPureOfWeight iota q t) :
    ∃ (t : ℝ) (G : (U ⧸ L.comap U.subtype) ≃ₗ[K] (U ⧸ L.comap U.subtype)),
      t ≤ w ∧ (∀ (x : U) (hx : M.frobenius (x : M.carrier) ∈ U),
        G (Submodule.Quotient.mk x) =
          Submodule.Quotient.mk ⟨M.frobenius x, hx⟩) ∧
      (FrobeniusModule.mk _ G).IsPureOfWeight iota q t := by
  classical
  have hpre : (L'.comap U'.subtype).comap f = L.comap U.subtype := by
    ext x
    exact hL x
  let F := (L.comap U.subtype).mapQ (L'.comap U'.subtype) f (by rw [hpre])
  have hFinj : Function.Injective F := by
    apply LinearMap.ker_eq_bot.mp
    dsimp [F]
    rw [Submodule.ker_mapQ, hpre, Submodule.mkQ_map_self]
  have hFsurj : Function.Surjective F := by
    intro z
    obtain ⟨z, rfl⟩ := (L'.comap U'.subtype).mkQ_surjective z
    obtain ⟨x, rfl⟩ := hsurj z
    exact ⟨Submodule.Quotient.mk x, rfl⟩
  let e := LinearEquiv.ofBijective F ⟨hFinj, hFsurj⟩
  have he (x : U) : e (Submodule.Quotient.mk x) = Submodule.Quotient.mk (f x) := rfl
  obtain ⟨t, G', ht, hG', hpure⟩ := hpiece
  let G := (e.trans G').trans e.symm
  refine ⟨t, G, ht, ?_, ?_⟩
  · intro x hx
    have hfx : N.frobenius (f x : N.carrier) ∈ U' := by
      rw [← hf x hx]
      exact (f ⟨M.frobenius x, hx⟩).2
    apply e.injective
    calc
      e (G (Submodule.Quotient.mk x)) = G' (e (Submodule.Quotient.mk x)) :=
        e.apply_symm_apply _
      _ = G' (Submodule.Quotient.mk (f x)) := congrArg G' (he x)
      _ = Submodule.Quotient.mk ⟨N.frobenius (f x), hfx⟩ := hG' (f x) hfx
      _ = e (Submodule.Quotient.mk ⟨M.frobenius x, hx⟩) := by
        rw [he]
        congr 1
        exact Subtype.ext (hf x hx).symm
  · intro α hα
    obtain ⟨x, hx⟩ := hα.exists_hasEigenvector
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at hx
    apply hpure α
    apply Module.End.hasEigenvalue_of_hasEigenvector (x := e x)
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
    refine ⟨?_, fun h ↦ hx.2 (e.injective (h.trans (map_zero e).symm))⟩
    change G' (e x) = α • e x
    calc
      G' (e x) = e (G x) := (e.apply_symm_apply _).symm
      _ = e (α • x) := congrArg e hx.1
      _ = α • e x := e.map_smul _ _

private theorem stable_map
    {K : Type v} [Field K]
    (M : FrobeniusModule.{u₁, v} K) (N : FrobeniusModule.{u₂, v} K)
    (f : M.carrier →ₗ[K] N.carrier)
    (hf : ∀ x, f (M.frobenius x) = N.frobenius (f x))
    (U : Submodule K M.carrier) (hU : U.map M.frobenius.toLinearMap = U) :
    (U.map f).map N.frobenius.toLinearMap = U.map f := by
  ext y
  constructor
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    have hMx : M.frobenius x ∈ U := by
      rw [← hU]
      exact ⟨x, hx, rfl⟩
    exact ⟨M.frobenius x, hMx, hf x⟩
  · rintro ⟨x, hx, rfl⟩
    rw [← hU] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    exact ⟨f z, ⟨z, hz, rfl⟩, (hf z).symm⟩

private theorem mem_stable
    {K : Type v} [Field K] (M : FrobeniusModule.{u₁, v} K)
    (U : Submodule K M.carrier) (hU : U.map M.frobenius.toLinearMap = U)
    (x : M.carrier) : M.frobenius x ∈ U ↔ x ∈ U := by
  constructor
  · intro hx
    rw [← hU] at hx
    obtain ⟨y, hy, he⟩ := hx
    exact M.frobenius.injective he ▸ hy
  · intro hx
    rw [← hU]
    exact ⟨x, hx, rfl⟩

private theorem stable_comap
    {K : Type v} [Field K]
    (M : FrobeniusModule.{u₁, v} K) (N : FrobeniusModule.{u₂, v} K)
    (f : M.carrier →ₗ[K] N.carrier)
    (hf : ∀ x, f (M.frobenius x) = N.frobenius (f x))
    (U : Submodule K N.carrier) (hU : U.map N.frobenius.toLinearMap = U) :
    (U.comap f).map M.frobenius.toLinearMap = U.comap f := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    change f (M.frobenius x) ∈ U
    rw [hf]
    exact (mem_stable N U hU (f x)).mpr hx
  · intro x hx
    refine ⟨M.frobenius.symm x, ?_, M.frobenius.apply_symm_apply x⟩
    change f (M.frobenius.symm x) ∈ U
    apply (mem_stable N U hU _).mp
    rw [← hf, M.frobenius.apply_symm_apply]
    exact hx

private def boundedPurePiece
    {K : Type v} [Field K] (iota : K →+* ℂ) (q : ℕ) (w : ℝ)
    (M : FrobeniusModule.{u₁, v} K) (L U : Submodule K M.carrier) : Prop :=
  ∃ (t : ℝ) (G : (U ⧸ L.comap U.subtype) ≃ₗ[K] (U ⧸ L.comap U.subtype)),
    t ≤ w ∧ (∀ (x : U) (hx : M.frobenius (x : M.carrier) ∈ U),
      G (Submodule.Quotient.mk x) =
        Submodule.Quotient.mk ⟨M.frobenius x, hx⟩) ∧
    (FrobeniusModule.mk _ G).IsPureOfWeight iota q t

/-- An extension of two Frobenius modules mixed of weights at most `w` is mixed
of weights at most `w`.

Source: Weil-conjectures blueprint, `sec-deligne-laumon-a1/sk-thm-dl-a1-upper`,
lemma `lem-a1-extension-bounds`, order 3134 in `main-20261015`
(blueprint: lem-a1-extension-bounds).

Proof: choose the finite Frobenius-stable filtrations of `A` and `C` supplied
by `def-weil-frobenius-module-weights`. Map the filtration of `A` into `B` by
`f`, and follow it by the inverse images under `g` of the filtration of `C`.
Injectivity of `f`, exactness at `B`, and surjectivity of `g` identify the
joining subspaces and the successive quotients with those of `A` and `C`.
Equivariance of both maps makes this a Frobenius-stable filtration with the
same induced Frobenius on those quotients. Every graded piece is therefore
pure of a weight at most `w`; the definition gives mixedness of `B`.
-/
theorem IsMixedOfWeightsAtMost.of_shortExact
    (p a ell : ℕ) [Fact (Nat.Prime p)] (ha : 1 ≤ a)
    [Fact (Nat.Prime ell)] (hellp : ell ≠ p) (Qlb : Type v) [Field Qlb]
    [Algebra (ℚ_[ell]) Qlb] (hQ : IsAlgClosure (ℚ_[ell]) Qlb)
    (iota : Qlb ≃+* ℂ)
    (A : FrobeniusModule.{u₁, v} Qlb) (B : FrobeniusModule.{u₂, v} Qlb)
    (C : FrobeniusModule.{u₃, v} Qlb)
    (f : A.carrier →ₗ[Qlb] B.carrier) (g : B.carrier →ₗ[Qlb] C.carrier)
    (hf : ∀ x : A.carrier, f (A.frobenius x) = B.frobenius (f x))
    (hg : ∀ x : B.carrier, g (B.frobenius x) = C.frobenius (g x))
    (hinj : Function.Injective f) (hexact : Function.Exact f g)
    (hsurj : Function.Surjective g) (w : ℝ)
    (hA : IsMixedOfWeightsAtMost p a ell ha hellp Qlb hQ iota A w)
    (hC : IsMixedOfWeightsAtMost p a ell ha hellp Qlb hQ iota C w) :
    IsMixedOfWeightsAtMost p a ell ha hellp Qlb hQ iota B w := by
  classical
  obtain ⟨m, V, hV0, hVm, hVle, hVs, hVp⟩ := hA
  obtain ⟨n, Z, hZ0, hZn, hZle, hZs, hZp⟩ := hC
  have hjoin : (V ⟨m, Nat.lt_succ_self m⟩).map f = (Z 0).comap g := by
    rw [hVm, hZ0, Submodule.map_top, Submodule.comap_bot]
    exact (LinearMap.exact_iff.mp hexact).symm
  let W : Fin (m + n + 1) → Submodule Qlb B.carrier := fun i ↦
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
  · rw [hWR ⟨m + n, by omega⟩ (by simp)]
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
    change boundedPurePiece (iota : Qlb →+* ℂ) (p ^ a) w B _ _
    by_cases hr : r.val < m
    · rw [hWL r.castSucc (by dsimp; omega), hWL r.succ (by dsimp; omega)]
      let j : Fin m := ⟨r.val, hr⟩
      let T : V j.succ →ₗ[Qlb] (V j.succ).map f :=
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
      apply transport_piece (iota : Qlb →+* ℂ) (p ^ a) w B A
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
      let T : (Z j.succ).comap g →ₗ[Qlb] Z j.succ :=
        (g.comp ((Z j.succ).comap g).subtype).codRestrict _ (fun x ↦ x.2)
      apply transport_piece (iota : Qlb →+* ℂ) (p ^ a) w B C
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
