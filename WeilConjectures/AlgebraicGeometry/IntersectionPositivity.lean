/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.IntersectionNumber
public import WeilConjectures.AlgebraicGeometry.Modules.HyperplaneSection

/-!
# The hyperplane recursion for intersection numbers

The positivity of the top self-intersection number of an ample line bundle,
`prop:deg-ample-positive` of the blueprint chapter on the degree of an isogeny, is proved by an
induction which removes one line bundle at a time from the intersection number
`(L₁ ⋯ L_d · F)`, at the cost of replacing the coefficient sheaf `F` by a coherent sheaf whose
support has smaller dimension. This file supplies that recursion, together with the reduction of
the positivity statement to a positive tensor power of the line bundle.

The step is the following. Let `M` be a line bundle on `X` and let

```text
  0 ⟶ F ⟶ F ⊗ M ⟶ G ⟶ 0
```

be a short exact sequence of coherent sheaves — the hyperplane sequence of
`AlgebraicGeometry.Scheme.Modules.exists_shortExact_supportDim_add_one_le`, whose cokernel `G`
satisfies `dim G + 1 ≤ dim F`. Then

`(M · L₁ ⋯ L_r · F) = (L₁ ⋯ L_r · G)`.

This is the comparison of the two Snapper polynomials of the blueprint proof. It rests on an
identity which needs no hypothesis at all,

`(M · L₁ ⋯ L_r · F) = (L₁ ⋯ L_r · F ⊗ M) - (L₁ ⋯ L_r · F)`,

expressing the first of the `r + 1` difference operators of `def:deg-intersection` as the
difference of the Snapper functions of `F ⊗ M` and of `F`, together with the additivity of the
intersection number in the coefficient sheaf, `lem:deg-intersection-additive`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.intersectionNumber_cons_eq_sub`: the difference identity
  `(M · L₁ ⋯ L_r · F) = (L₁ ⋯ L_r · F ⊗ M) - (L₁ ⋯ L_r · F)`.
* `AlgebraicGeometry.Scheme.Modules.intersectionNumber_cons_eq_of_shortExact`: the hyperplane
  recursion `(M · L₁ ⋯ L_r · F) = (L₁ ⋯ L_r · G)` along a short exact sequence
  `0 ⟶ F ⟶ F ⊗ M ⟶ G ⟶ 0`.
* `AlgebraicGeometry.Scheme.Modules.exists_intersectionNumber_cons_eq` and
  `AlgebraicGeometry.Scheme.Modules.exists_intersectionNumber_const_succ_eq`: the recursion in
  the form in which the induction uses it, producing the coherent sheaf `G` with
  `dim G + 1 ≤ dim F` from a globally generated `M`.
* `AlgebraicGeometry.Scheme.Modules.intersectionNumber_const_tensorPow_pos_iff`: the reduction
  of the positivity of `(L ^ g · F)` to that of `((L ^⊗ e) ^ g · F)` for `e ≥ 1`, which is how
  the proof of `prop:deg-ample-positive` passes from an ample line bundle to a very ample one.

## What is still missing for `prop:deg-ample-positive`

Two inputs of the blueprint proof are not available yet, and the positivity statement itself is
therefore not proved here:

* the base case, that `χ(X, F) > 0` for a nonzero coherent sheaf `F` whose support has dimension
  `0`;
* the *lower* bound `dim F ≤ dim G + 1` on the support of the cokernel of the hyperplane
  sequence, that is, Krull's principal ideal theorem together with the fact that a hyperplane
  section meets every positive-dimensional component of a proper scheme.

Only the upper bound `dim G + 1 ≤ dim F` is part of
`AlgebraicGeometry.Scheme.Modules.exists_shortExact_supportDim_add_one_le`, and the recursion
below therefore computes `(L ^ g · F)` as `χ(X, G_g)` for a coherent sheaf `G_g` which is not yet
known to be nonzero.

## Blueprint

This file contributes two steps of the proof of `prop:deg-ample-positive` of
`curve_estimates/28_degree_of_the_isogeny.tex`; neither is a node of the blueprint graph of its
own.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory SheafOfModules fwdDiff

namespace AlgebraicGeometry.Scheme.Modules

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

variable {r : ℕ} {M : X.Modules}

private lemma eulerChar_tensorZPow_cons_zero (F : X.Modules) (hM : M.Invertible)
    (L : Fin r → X.Modules) (hL : ∀ j, (L j).Invertible) (m : Fin r → ℤ) :
    eulerChar k (tensorZPow F (Fin.cons M L) (invertible_cons hM hL) (Fin.cons 0 m)) =
      eulerChar k (tensorZPow F L hL m) := by
  refine eulerChar_tensorZPow_congr F _ hL ?_
  rw [Fin.prod_univ_succ]
  simp

private lemma eulerChar_tensorZPow_cons_one (F : X.Modules) (hM : M.Invertible)
    (L : Fin r → X.Modules) (hL : ∀ j, (L j).Invertible) (m : Fin r → ℤ) :
    eulerChar k (tensorZPow F (Fin.cons M L) (invertible_cons hM hL) (Fin.cons 1 m)) =
      eulerChar k (tensorZPow (F ⊗ M) L hL m) := by
  have hpic : Pic.mk (zpowProd (Fin.cons M L) (invertible_cons hM hL) (Fin.cons 1 m))
      (invertible_zpowProd _ _ _) =
      Pic.mk (M ⊗ zpowProd L hL m) (hM.tensorObj (invertible_zpowProd L hL m)) := by
    rw [Pic.mk_zpowProd, Pic.mk_tensorObj (hM := hM) (hN := invertible_zpowProd L hL m),
      Pic.mk_zpowProd, Fin.prod_univ_succ]
    simp
  obtain ⟨e⟩ := Pic.mk_eq_mk_iff.1 hpic
  exact eulerChar_congr k (tensorIso (Iso.refl F) e ≪≫ (α_ F M (zpowProd L hL m)).symm)

/-- **The intersection number as a difference of intersection numbers in one variable fewer**:

`(M · L₁ ⋯ L_r · F) = (L₁ ⋯ L_r · F ⊗ M) - (L₁ ⋯ L_r · F)`.

This needs no hypothesis on `X`, on `F` or on the line bundles: it is the statement that the
first of the `r + 1` difference operators of `def:deg-intersection` is the difference of the
Snapper functions of `F ⊗ M` and of `F`. -/
theorem intersectionNumber_cons_eq_sub (F : X.Modules) (hM : M.Invertible)
    (L : Fin r → X.Modules) (hL : ∀ j, (L j).Invertible) :
    intersectionNumber k F (Fin.cons M L) (invertible_cons hM hL) =
      intersectionNumber k (F ⊗ M) L hL - intersectionNumber k F L hL := by
  have hK : ∀ j, ((Fin.cons M L : Fin (r + 1) → X.Modules) j).Invertible := invertible_cons hM hL
  -- the additive map `m ↦ (0, m)` placing the exponents of `L₁, …, L_r` after a zero exponent
  -- for `M`
  let φ : (Fin r → ℤ) →ₙ+ (Fin (r + 1) → ℤ) :=
    AddHom.mk (fun m ↦ Fin.cons 0 m) fun m m' ↦ by
      funext j
      induction j using Fin.cases with
      | zero => simp
      | succ i => simp
  have hφ0 : φ (0 : Fin r → ℤ) = 0 := by
    funext j
    induction j using Fin.cases with
    | zero => rfl
    | succ i => rfl
  have hveq : (⇑φ ∘ fun i : Fin r ↦ (Pi.single i 1 : Fin r → ℤ)) =
      fun i : Fin r ↦ (Pi.single i.succ 1 : Fin (r + 1) → ℤ) := by
    funext i j
    induction j using Fin.cases with
    | zero => simp [φ, (Fin.succ_ne_zero i).symm]
    | succ j => simp [φ, Pi.single_apply, Fin.succ_inj]
  -- the Snapper function of `(M, L₁, …, L_r)`
  set P : (Fin (r + 1) → ℤ) → ℤ :=
    fun m ↦ eulerChar k (tensorZPow F (Fin.cons M L) hK m) with hP
  -- differencing `P` in the direction of the exponent of `M` compares the Snapper functions of
  -- `F ⊗ M` and of `F`
  have hstep : (fun m : Fin r → ℤ ↦ eulerChar k (tensorZPow (F ⊗ M) L hL m)) =
      (Δ_[(Pi.single 0 1 : Fin (r + 1) → ℤ)] P) ∘ ⇑φ +
        fun m : Fin r → ℤ ↦ eulerChar k (tensorZPow F L hL m) := by
    funext m
    have hcons : (Fin.cons 0 m : Fin (r + 1) → ℤ) + Pi.single 0 1 = Fin.cons 1 m := by
      funext j
      induction j using Fin.cases with
      | zero => simp
      | succ i => simp [Fin.succ_ne_zero i]
    simp only [Pi.add_apply, Function.comp_apply, fwdDiff_apply, hP]
    rw [show (φ m : Fin (r + 1) → ℤ) = Fin.cons 0 m from rfl, hcons,
      eulerChar_tensorZPow_cons_one k F hM L hL m, eulerChar_tensorZPow_cons_zero k F hM L hL m]
    ring
  have hmain : fwdDiffComp (fun i : Fin r ↦ (Pi.single i 1 : Fin r → ℤ))
      ((Δ_[(Pi.single 0 1 : Fin (r + 1) → ℤ)] P) ∘ ⇑φ) 0 =
      fwdDiffComp (fun j : Fin (r + 1) ↦ (Pi.single j 1 : Fin (r + 1) → ℤ)) P 0 := by
    rw [fwdDiffComp_succ' (fun j : Fin (r + 1) ↦ (Pi.single j 1 : Fin (r + 1) → ℤ)) P,
      fwdDiffComp_comp_addHom, Function.comp_apply, hφ0, hveq]
  have hadd := congrFun (fwdDiffComp_add (fun i : Fin r ↦ (Pi.single i 1 : Fin r → ℤ))
    ((Δ_[(Pi.single 0 1 : Fin (r + 1) → ℤ)] P) ∘ ⇑φ)
    (fun m : Fin r → ℤ ↦ eulerChar k (tensorZPow F L hL m))) 0
  rw [← hstep] at hadd
  rw [intersectionNumber_eq_fwdDiffComp_zero k F (Fin.cons M L) hK, ← hmain,
    intersectionNumber_eq_fwdDiffComp_zero k (F ⊗ M) L hL,
    intersectionNumber_eq_fwdDiffComp_zero k F L hL, hadd]
  simp only [Pi.add_apply]
  ring

/-! ### The hyperplane recursion -/

section Proper

variable [IsProper (X ↘ Spec (.of k))]

/-- **The hyperplane recursion for intersection numbers.** If

```text
  0 ⟶ F ⟶ F ⊗ M ⟶ G ⟶ 0
```

is a short exact sequence of coherent sheaves on a scheme proper over a field, with `M` a line
bundle, then

`(M · L₁ ⋯ L_r · F) = (L₁ ⋯ L_r · G)`.

This is the comparison of the two Snapper polynomials in the proof of `prop:deg-ample-positive`:
`AlgebraicGeometry.Scheme.Modules.intersectionNumber_cons_eq_sub` turns the left-hand side into
`(L₁ ⋯ L_r · F ⊗ M) - (L₁ ⋯ L_r · F)`, and `lem:deg-intersection-additive` identifies that
difference with `(L₁ ⋯ L_r · G)`. -/
theorem intersectionNumber_cons_eq_of_shortExact (F G : X.Modules) [F.IsCoherent] [G.IsCoherent]
    (hM : M.Invertible) {u : F ⟶ F ⊗ M} {v : F ⊗ M ⟶ G} {hw : u ≫ v = 0}
    (hC : (ShortComplex.mk u v hw).ShortExact) (L : Fin r → X.Modules)
    (hL : ∀ j, (L j).Invertible) :
    intersectionNumber k F (Fin.cons M L) (invertible_cons hM hL) =
      intersectionNumber k G L hL := by
  have h₁ : (ShortComplex.mk u v hw).X₁.IsCoherent := ‹F.IsCoherent›
  have h₂ : (ShortComplex.mk u v hw).X₂.IsCoherent := isCoherent_tensorObj_of_invertible F hM
  have h₃ : (ShortComplex.mk u v hw).X₃.IsCoherent := ‹G.IsCoherent›
  have hadd : intersectionNumber k F L hL + intersectionNumber k G L hL =
      intersectionNumber k (F ⊗ M) L hL := intersectionNumber_add_intersectionNumber k hC L hL
  rw [intersectionNumber_cons_eq_sub k F hM L hL]
  omega

/-- **The hyperplane recursion, with the drop of the dimension of the support.** Let `X` be
proper over an infinite field `k`, let `F` be coherent and let `M` be a globally generated line
bundle — a very ample one, in the application. Then there is a coherent sheaf `G` with
`dim G + 1 ≤ dim F` and

`(M · L₁ ⋯ L_r · F) = (L₁ ⋯ L_r · G)`.

This is the inductive step of `prop:deg-ample-positive`: it removes one line bundle from the
intersection number at the cost of lowering the dimension of the coefficient sheaf by at least
one. -/
theorem exists_intersectionNumber_cons_eq [Infinite k] (F : X.Modules) [F.IsCoherent]
    (hM : M.Invertible) [M.IsGloballyGenerated] (L : Fin r → X.Modules)
    (hL : ∀ j, (L j).Invertible) :
    ∃ (G : X.Modules) (_ : G.IsCoherent), G.supportDim + 1 ≤ F.supportDim ∧
      intersectionNumber k F (Fin.cons M L) (invertible_cons hM hL) =
        intersectionNumber k G L hL := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  obtain ⟨G, hG, u, v, hw, hSE, hGle⟩ := exists_shortExact_supportDim_add_one_le k F hM
  have : G.IsCoherent := hG
  exact ⟨G, hG, hGle, intersectionNumber_cons_eq_of_shortExact k F G hM hSE L hL⟩

/-- **The hyperplane recursion for a self-intersection number.** The case `L₁ = ⋯ = L_r = M` of
`AlgebraicGeometry.Scheme.Modules.exists_intersectionNumber_cons_eq`: for a globally generated
line bundle `M` on a scheme proper over an infinite field and a coherent sheaf `F` there is a
coherent `G` with `dim G + 1 ≤ dim F` and `(M ^ (r + 1) · F) = (M ^ r · G)`. -/
theorem exists_intersectionNumber_const_succ_eq [Infinite k] (F : X.Modules) [F.IsCoherent]
    (hM : M.Invertible) [M.IsGloballyGenerated] :
    ∃ (G : X.Modules) (_ : G.IsCoherent), G.supportDim + 1 ≤ F.supportDim ∧
      intersectionNumber k F (fun _ : Fin (r + 1) ↦ M) (fun _ ↦ hM) =
        intersectionNumber k G (fun _ : Fin r ↦ M) (fun _ ↦ hM) := by
  obtain ⟨G, hG, hGle, hnum⟩ :=
    exists_intersectionNumber_cons_eq k F hM (fun _ : Fin r ↦ M) (fun _ ↦ hM)
  refine ⟨G, hG, hGle, ?_⟩
  rw [← hnum]
  exact intersectionNumber_congr k F _ _ fun j ↦ Pic.mk_congr (by
    induction j using Fin.cases with
    | zero => rw [Fin.cons_zero]
    | succ i => rw [Fin.cons_succ])

/-! ### The reduction to a very ample line bundle -/

/-- **A tensor power scales a self-intersection number**: `((L ^⊗ e) ^ g · F) = e ^ g (L ^ g · F)`
for a coherent sheaf `F` with `dim F ≤ g`.

This is the natural-number case of `cor:deg-intersection-powers`, which is stated there for an
integer power; it is the form used in the reduction of `prop:deg-ample-positive` to a very ample
line bundle. -/
theorem intersectionNumber_const_tensorPow [Infinite k] {A : X.Modules} (hA : A.Invertible)
    (hAa : A.IsAmple) (F : X.Modules) [F.IsCoherent] {g : ℕ} {L : X.Modules} (hL : L.Invertible)
    (hd : F.supportDim ≤ (g : WithBot ℕ∞)) (e : ℕ) :
    intersectionNumber k F (fun _ : Fin g ↦ L ^⊗ e) (fun _ ↦ hL.tensorPow e) =
      (e : ℤ) ^ g * intersectionNumber k F (fun _ : Fin g ↦ L) fun _ ↦ hL := by
  exact intersectionNumber_const_zpow k hA hAa F hL hd (e : ℤ)

/-- **The reduction of the positivity of a top self-intersection number to a positive tensor
power**: for `e ≥ 1` the self-intersection numbers of `L ^⊗ e` and of `L` are positive together.

This is the first step of the proof of `prop:deg-ample-positive`, where `e` is chosen so that
`L ^⊗ e` is very ample. -/
theorem intersectionNumber_const_tensorPow_pos_iff [Infinite k] {A : X.Modules}
    (hA : A.Invertible) (hAa : A.IsAmple) (F : X.Modules) [F.IsCoherent] {g : ℕ} {L : X.Modules}
    (hL : L.Invertible) (hd : F.supportDim ≤ (g : WithBot ℕ∞)) {e : ℕ} (he : 1 ≤ e) :
    0 < intersectionNumber k F (fun _ : Fin g ↦ L ^⊗ e) (fun _ ↦ hL.tensorPow e) ↔
      0 < intersectionNumber k F (fun _ : Fin g ↦ L) fun _ ↦ hL := by
  have hpos : (0 : ℤ) < (e : ℤ) ^ g := pow_pos (by exact_mod_cast he) g
  rw [intersectionNumber_const_tensorPow k hA hAa F hL hd e]
  exact mul_pos_iff_of_pos_left hpos

end Proper

end AlgebraicGeometry.Scheme.Modules
