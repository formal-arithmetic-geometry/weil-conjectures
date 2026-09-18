/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerCharacteristic
public import WeilConjectures.AlgebraicGeometry.Modules.HyperplaneSection
public import WeilConjectures.AlgebraicGeometry.Modules.ZPow
public import WeilConjectures.Mathlib.Data.ENat.Basic
public import WeilConjectures.RingTheory.NumericalPolynomial

/-!
# Snapper's theorem

Let `X` be a projective scheme over a field `k`, let `F` be a coherent sheaf of `𝒪ₓ`-modules and
let `L₁, …, L_r` be line bundles on `X`. Snapper's theorem says that

`P(m₁, …, m_r) = χ(X, F ⊗ L₁ ^⊗ m₁ ⊗ ⋯ ⊗ L_r ^⊗ m_r)`

is a numerical polynomial on `ℤ ^ r` of total degree at most the dimension of the support of `F`.
It is the theorem the whole theory of intersection numbers rests on: the intersection number of
`r` line bundles against `F` is the coefficient of `m₁ ⋯ m_r` in `P`.

## The proof

The proof is the one of the blueprint, an induction on `dim F` with two preliminary reductions.

* **The base case** is `dim F = -1`, that is `F = 0`
  (`AlgebraicGeometry.Scheme.Modules.supportDim_eq_bot_iff`), where `P` vanishes identically.
* **The reduction to very ample `Lⱼ`** writes `Lⱼ ≅ Mⱼ ⊗ N⁻¹` with `Mⱼ := Lⱼ ⊗ A ^⊗ n` and
  `N := A ^⊗ n` all very ample, `A` being an ample line bundle on `X` and `n` large
  (`AlgebraicGeometry.Scheme.Modules.IsAmple.exists_isVeryAmple_tensorObj_tensorPow`). Snapper's
  theorem for the `2r` very ample bundles `M₁ … M_r N … N` gives a numerical polynomial `Q` on
  `ℤ ^ (r + r)` with `P(m) = Q(m, -m)`, and `IsNumericalPolynomial.comp_append_neg` concludes.
* **The induction** takes the hyperplane exact sequence `0 ⟶ F ⟶ F ⊗ Lⱼ ⟶ G ⟶ 0` of
  `AlgebraicGeometry.Scheme.Modules.exists_shortExact_supportDim_add_one_le`, which is
  `lem:deg-general-hyperplane`, and reads off it that the `j`-th difference operator of `P` is
  the polynomial of `G`, whose support has strictly smaller dimension. So `dim F + 1` difference
  operators annihilate `P`, and `isNumericalPolynomial_of_fwdDiffComp_eq_zero` — the converse of
  the degree-lowering lemma — says that `P` is a numerical polynomial of total degree at most
  `dim F`.

## Projective, and infinite rather than algebraically closed

The blueprint states the theorem for a projective scheme over an algebraically closed field.
Projectivity is spelled here as properness together with an ample line bundle `A` on `X`, which
is equivalent by `AlgebraicGeometry.Scheme.Modules.IsAmple.exists_isClosedImmersion`, and is the
form in which the hypothesis arises downstream (see `rem:deg-snapper-proper` of the blueprint).
Of the algebraic closedness of `k` only its infiniteness is used, and only to produce the
hyperplane section; this is the same hypothesis `lem:deg-generic-section` is formalised with in
`WeilConjectures.AlgebraicGeometry.Modules.Vanishing`.

## Main results

- `AlgebraicGeometry.Scheme.Modules.isNumericalPolynomial_eulerChar_tensorZPow_of_isVeryAmple`
  and `AlgebraicGeometry.Scheme.Modules.isNumericalPolynomial_eulerChar_tensorZPow`:
  **`thm:deg-snapper`**, Snapper's theorem, first for very ample `Lⱼ` and then in general.

## TODO

The blueprint node `thm:deg-snapper` is not `\leanok`: Snapper's theorem rests on the two sorried
statements `AlgebraicGeometry.Scheme.Modules.H.finite` and
`AlgebraicGeometry.Scheme.Modules.H.subsingleton_of_topologicalKrullDim_lt` behind the Euler
characteristic, and on the sorried
`AlgebraicGeometry.Scheme.Modules.IsAmple.exists_isVeryAmple_tensorObj_tensorPow`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory SheafOfModules fwdDiff

namespace AlgebraicGeometry.Scheme.Modules

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-! ### The Euler characteristic of a twist -/

variable {k}

/-- Twists of a sheaf of modules by invertible sheaves with the same class in the Picard group
have the same Euler characteristic. -/
lemma eulerChar_tensorObj_congr (F : X.Modules) {A B : X.Modules} (hA : A.Invertible)
    (hB : B.Invertible) (h : Pic.mk A hA = Pic.mk B hB) :
    eulerChar k (F ⊗ A) = eulerChar k (F ⊗ B) :=
  eulerChar_congr k (tensorIso (Iso.refl F) (Pic.mk_eq_mk_iff.1 h).some)

variable (k)

/-! ### The induction -/

section VeryAmple

variable [Infinite k] [IsProper (X ↘ Spec (.of k))]

include k

/-- **The heart of Snapper's theorem**: for very ample `L₁, …, L_r` and a coherent sheaf `F`
whose support has dimension less than `n`, any `n` of the standard difference operators
annihilate `m ↦ χ(F ⊗ L₁ ^⊗ m₁ ⊗ ⋯ ⊗ L_r ^⊗ m_r)`.

This is the induction on `dim F` of the blueprint proof of `thm:deg-snapper`; it is the carrier
of that induction, equivalent to
`AlgebraicGeometry.Scheme.Modules.isNumericalPolynomial_eulerChar_tensorZPow_of_isVeryAmple`
below by `isNumericalPolynomial_iff_fwdDiffComp_eq_zero`. -/
private theorem fwdDiffComp_eulerChar_tensorZPow_eq_zero_aux {r : ℕ} (L : Fin r → X.Modules)
    (hL : ∀ j, IsVeryAmple (Spec (.of k)) (L j)) (n : ℕ) (F : X.Modules) [F.IsCoherent]
    (hd : F.supportDim < (n : WithBot ℕ∞)) (j : Fin n → Fin r) :
    fwdDiffComp (fun a ↦ Pi.single (j a) 1)
      (fun m ↦ eulerChar k (tensorZPow F L (fun i ↦ (hL i).invertible) m)) = 0 := by
  have hcpt : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have hnoeth : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have hL' : ∀ i, (L i).Invertible := fun i ↦ (hL i).invertible
  induction n generalizing F with
  | zero =>
    rw [fwdDiffComp_zero]
    funext m
    exact eulerChar_eq_zero_of_isZero k ((invertible_zpowProd L hL' m).isZero_tensorObj
      ((supportDim_eq_bot_iff F).1 (ENat.WithBot.lt_natCast_zero_iff.1 hd)))
  | succ n ih =>
    have := (hL (j 0)).isGloballyGenerated
    obtain ⟨G, hG, u, v, hw, hSE, hGle⟩ :=
      exists_shortExact_supportDim_add_one_le k F ((hL (j 0)).invertible)
    have hGn : G.supportDim < (n : WithBot ℕ∞) :=
      ENat.WithBot.lt_natCast_of_add_one_le_natCast
        (hGle.trans (ENat.WithBot.lt_natCast_add_one_iff.1 hd))
    have hstep : ∀ m : Fin r → ℤ,
        eulerChar k (tensorZPow F L hL' m) + eulerChar k (tensorZPow G L hL' m) =
          eulerChar k (tensorZPow F L hL' (m + Pi.single (j 0) 1)) := by
      intro m
      have hEq : (tensorRight (zpowProd L hL' m)).IsEquivalence :=
        (invertible_zpowProd L hL' m).isEquivalence_tensorRight
      have e₁ : ((ShortComplex.mk u v hw).map (tensorRight (zpowProd L hL' m))).X₁.IsCoherent :=
        isCoherent_tensorObj_of_invertible F (invertible_zpowProd L hL' m)
      have e₂ : ((ShortComplex.mk u v hw).map (tensorRight (zpowProd L hL' m))).X₂.IsCoherent :=
        have : (F ⊗ L (j 0)).IsCoherent := isCoherent_tensorObj_of_invertible F (hL' (j 0))
        isCoherent_tensorObj_of_invertible _ (invertible_zpowProd L hL' m)
      have e₃ : ((ShortComplex.mk u v hw).map (tensorRight (zpowProd L hL' m))).X₃.IsCoherent :=
        isCoherent_tensorObj_of_invertible G (invertible_zpowProd L hL' m)
      refine (eulerChar_add_eulerChar k
        (hSE.map_of_exact (tensorRight (zpowProd L hL' m)))).trans ?_
      refine (eulerChar_congr k (α_ F (L (j 0)) (zpowProd L hL' m))).trans ?_
      refine eulerChar_tensorObj_congr F ((hL' (j 0)).tensorObj (invertible_zpowProd L hL' m))
        (invertible_zpowProd L hL' (m + Pi.single (j 0) 1)) ?_
      rw [Pic.mk_tensorObj (hM := hL' (j 0)) (hN := invertible_zpowProd L hL' m)]
      exact (Pic.mk_zpowProd_add_single L hL' m (j 0)).symm
    have hdiff : Δ_[Pi.single (j 0) 1] (fun m ↦ eulerChar k (tensorZPow F L hL' m)) =
        fun m ↦ eulerChar k (tensorZPow G L hL' m) := by
      funext m
      have h := hstep m
      rw [fwdDiff_apply]
      omega
    rw [fwdDiffComp_succ', hdiff]
    exact ih G hGn fun a ↦ j a.succ

/-- **Snapper's theorem for very ample line bundles**, the case the general one is reduced to:
if `L₁, …, L_r` are very ample and `F` is coherent with `dim F ≤ d`, then
`m ↦ χ(F ⊗ L₁ ^⊗ m₁ ⊗ ⋯ ⊗ L_r ^⊗ m_r)` is a numerical polynomial of total degree at most `d`. -/
theorem isNumericalPolynomial_eulerChar_tensorZPow_of_isVeryAmple (F : X.Modules) [F.IsCoherent]
    {r : ℕ} (L : Fin r → X.Modules) (hL : ∀ j, IsVeryAmple (Spec (.of k)) (L j)) (d : ℕ)
    (hd : F.supportDim ≤ (d : WithBot ℕ∞)) :
    IsNumericalPolynomial d
      (fun m ↦ eulerChar k (tensorZPow F L (fun i ↦ (hL i).invertible) m)) :=
  isNumericalPolynomial_of_fwdDiffComp_eq_zero fun j ↦
    fwdDiffComp_eulerChar_tensorZPow_eq_zero_aux k L hL (d + 1) F
      (ENat.WithBot.lt_natCast_add_one_iff.2 hd) j

/-- **Snapper's theorem** (`thm:deg-snapper`). Let `X` be a projective scheme over an infinite
field `k` — proper, with an ample line bundle `A` — let `F` be a coherent sheaf of `𝒪ₓ`-modules
and let `L₁, …, L_r` be line bundles on `X`. Then

`m ↦ χ(X, F ⊗ L₁ ^⊗ m₁ ⊗ ⋯ ⊗ L_r ^⊗ m_r)`

is a numerical polynomial on `ℤ ^ r` of total degree at most the dimension `dim F` of the support
of `F`, the bound being spelled as any natural number `d` with `dim F ≤ d`.

The proof reduces to the very ample case
`AlgebraicGeometry.Scheme.Modules.isNumericalPolynomial_eulerChar_tensorZPow_of_isVeryAmple`:
for `n` large both `Mⱼ := Lⱼ ⊗ A ^⊗ n` and `N := A ^⊗ n` are very ample, and the polynomial of
the `2r`-tuple `M₁ … M_r N … N` evaluated at `(m, -m)` is the polynomial of `L₁ … L_r` at `m`,
because the two twisting factors have the same class in the Picard group. -/
theorem isNumericalPolynomial_eulerChar_tensorZPow {A : X.Modules} (hA : A.Invertible)
    (hAa : A.IsAmple) (F : X.Modules) [F.IsCoherent] {r : ℕ} (L : Fin r → X.Modules)
    (hL : ∀ j, (L j).Invertible) (d : ℕ) (hd : F.supportDim ≤ (d : WithBot ℕ∞)) :
    IsNumericalPolynomial d (fun m ↦ eulerChar k (tensorZPow F L hL m)) := by
  -- for one and the same large `n`, all the `L i ⊗ A ^⊗ n` and `A ^⊗ n` are very ample
  obtain ⟨n₀, hn₀⟩ := hAa.exists_isVeryAmple_tensorObj_tensorPow k hA
    (SheafOfModules.invertible_tensorUnit X.sheaf)
  choose n₁ hn₁ using fun i : Fin r ↦ hAa.exists_isVeryAmple_tensorObj_tensorPow k hA (hL i)
  set n := max (Finset.univ.sup n₁) n₀
  have hMva : ∀ i, IsVeryAmple (Spec (.of k)) (L i ⊗ A ^⊗ n) := fun i ↦
    hn₁ i n ((Finset.le_sup (Finset.mem_univ i)).trans (le_max_left _ _))
  have hNva : IsVeryAmple (Spec (.of k)) (A ^⊗ n) :=
    (hn₀ n (le_max_right _ _)).of_iso (λ_ (A ^⊗ n))
  -- the `2r`-tuple `M₁ … M_r N … N` of very ample line bundles
  have hMN : ∀ i : Fin (r + r),
      IsVeryAmple (Spec (.of k)) (Fin.append (fun i ↦ L i ⊗ A ^⊗ n) (fun _ ↦ A ^⊗ n) i) := by
    intro i
    induction i using Fin.addCases with
    | left i =>
      rw [Fin.append_left]
      exact hMva i
    | right i =>
      rw [Fin.append_right]
      exact hNva
  have hQ := isNumericalPolynomial_eulerChar_tensorZPow_of_isVeryAmple k F _ hMN d hd
  have key : (fun m : Fin r → ℤ ↦ eulerChar k
        (tensorZPow F _ (fun i ↦ (hMN i).invertible) (Fin.append m (-m)))) =
      fun m ↦ eulerChar k (tensorZPow F L hL m) := by
    funext m
    refine eulerChar_tensorObj_congr F
      (invertible_zpowProd _ (fun i ↦ (hMN i).invertible) (Fin.append m (-m)))
      (invertible_zpowProd L hL m) ?_
    rw [Pic.mk_zpowProd_append (hM := fun i ↦ (hL i).tensorObj (hA.tensorPow n))
        (hN := fun _ : Fin r ↦ hA.tensorPow n), Pic.mk_zpowProd, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [Pic.mk_tensorObj (hM := hL i) (hN := hA.tensorPow n), Pic.mk_tensorPow (hM := hA),
      Pi.neg_apply, mul_zpow, zpow_neg, mul_assoc, mul_inv_cancel, mul_one]
  exact key ▸ hQ.comp_append_neg

end VeryAmple

end AlgebraicGeometry.Scheme.Modules
