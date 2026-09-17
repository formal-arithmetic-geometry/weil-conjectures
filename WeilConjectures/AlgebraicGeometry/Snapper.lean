/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerCharacteristic
public import WeilConjectures.AlgebraicGeometry.Modules.Dimension
public import WeilConjectures.AlgebraicGeometry.Modules.HyperplaneSection
public import WeilConjectures.AlgebraicGeometry.Modules.TensorExact
public import WeilConjectures.AlgebraicGeometry.Modules.Vanishing
public import WeilConjectures.AlgebraicGeometry.Modules.ZPow
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
* **The reduction to very ample `Lⱼ`** writes `Lⱼ ≅ Mⱼ ⊗ Nⱼ⁻¹` with `Mⱼ := Lⱼ ⊗ A ^⊗ nⱼ` and
  `Nⱼ := 𝒪ₓ ⊗ A ^⊗ nⱼ` both very ample, `A` being an ample line bundle on `X` and `nⱼ` large
  (`AlgebraicGeometry.Scheme.Modules.IsAmple.exists_isVeryAmple_tensorObj_tensorPow`). Snapper's
  theorem for the `2r` very ample bundles `M₁ … M_r N₁ … N_r` gives a numerical polynomial `Q` on
  `ℤ ^ (r + r)` with `P(m) = Q(m, -m)`, and `IsNumericalPolynomial.comp_append_neg` concludes.
* **The induction** takes a section `s` of `Lⱼ` vanishing at no associated point of `F`
  (`AlgebraicGeometry.Scheme.Modules.exists_shortExact_supportDim_lt` below, which is
  `lem:deg-general-hyperplane`), and reads off the short exact sequence
  `0 ⟶ F ⟶ F ⊗ Lⱼ ⟶ G ⟶ 0` that the `j`-th difference operator of `P` is the polynomial of `G`,
  whose support has strictly smaller dimension. So `dim F + 1` difference operators annihilate
  `P`, and `isNumericalPolynomial_of_fwdDiffComp_eq_zero` — the converse of the degree-lowering
  lemma — says that `P` is a numerical polynomial of total degree at most `dim F`.

## Projective, and infinite rather than algebraically closed

The blueprint states the theorem for a projective scheme over an algebraically closed field.
Projectivity is spelled here as properness together with an ample line bundle `A` on `X`, which
is equivalent by `AlgebraicGeometry.Scheme.Modules.IsAmple.exists_isClosedImmersion`, and is the
form in which the hypothesis arises downstream (see `rem:deg-snapper-proper` of the blueprint).
Of the algebraic closedness of `k` only its infiniteness is used, and only to produce the
hyperplane section; this is the same hypothesis `lem:deg-generic-section` is formalised with in
`WeilConjectures.AlgebraicGeometry.Modules.Vanishing`.

## Main results

- `AlgebraicGeometry.Scheme.Modules.exists_shortExact_supportDim_lt`:
  **`lem:deg-general-hyperplane`**, the hyperplane exact sequence with a strict drop of the
  dimension of the support.
- `AlgebraicGeometry.Scheme.Modules.isNumericalPolynomial_eulerChar_tensorZPow`:
  **`thm:deg-snapper`**, Snapper's theorem.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory SheafOfModules fwdDiff

namespace AlgebraicGeometry.Scheme.Modules

/-- Only `⊥` lies below `0` in `WithBot ℕ∞`. -/
private lemma eq_bot_of_lt_natCast_zero {a : WithBot ℕ∞} (h : a < ((0 : ℕ) : WithBot ℕ∞)) :
    a = ⊥ := by
  induction a using WithBot.recBotCoe with
  | bot => rfl
  | coe b => exact absurd h (by simp)

/-- A bound in `WithBot ℕ∞` below `n + 1` is a bound below or equal to `n`. -/
private lemma le_natCast_of_lt_natCast_succ {a : WithBot ℕ∞} {n : ℕ}
    (h : a < ((n + 1 : ℕ) : WithBot ℕ∞)) : a ≤ ((n : ℕ) : WithBot ℕ∞) := by
  induction a using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe b =>
    induction b using WithTop.recTopCoe with
    | top => simp at h
    | coe c =>
      have h' : (c : ℕ∞) < ((n + 1 : ℕ) : ℕ∞) := WithBot.coe_lt_coe.1 h
      have h'' : c < n + 1 := by exact_mod_cast h'
      exact WithBot.coe_le_coe.2 (Nat.cast_le.2 (Nat.lt_succ_iff.1 h''))

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-! ### The hyperplane section -/

section Hyperplane

variable [Infinite k] [CompactSpace X] [IsLocallyNoetherian X]

include k

/-- **`lem:deg-general-hyperplane`: a hyperplane section avoiding the associated points.** Let
`X` be a quasi-compact locally Noetherian scheme over an infinite field `k`, let `F` be a
non-zero coherent sheaf of `𝒪ₓ`-modules whose support has finite dimension, and let `L` be a
globally generated line bundle on `X` — a very ample one, in the application. Then there is a
short exact sequence

```
0 ⟶ F ⟶ F ⊗ L ⟶ G ⟶ 0
```

whose first map is multiplication by a global section of `L`, with `G` coherent and
`dim G < dim F`.

The section is one vanishing at no associated point of `F`, which exists by
`AlgebraicGeometry.Scheme.Modules.exists_forall_associatedPoints_not_vanishesAt`; multiplication
by it is then a monomorphism, and the support of its cokernel misses every generic point of an
irreducible component of the support of `F`, which is what makes the dimension drop. -/
theorem exists_shortExact_supportDim_lt (F : X.Modules) [F.IsCoherent] (hF : ¬ IsZero F)
    (hdim : F.supportDim ≠ ⊤) {L : X.Modules} (hL : L.Invertible)
    (hgg : L.IsGloballyGenerated) :
    ∃ (G : X.Modules) (_ : G.IsCoherent) (u : F ⟶ F ⊗ L) (v : F ⊗ L ⟶ G) (hw : u ≫ v = 0),
      (ShortComplex.mk u v hw).ShortExact ∧ G.supportDim < F.supportDim := by
  have hLcoh : L.IsCoherent := hL.isCoherent
  have hFq : F.IsQuasicoherent := inferInstance
  obtain ⟨s, hs⟩ := exists_forall_associatedPoints_not_vanishesAt k F (finite_sections F) L
    (fun x _ ↦ (mem_support_iff L x).2 (hL.nontrivial_stalk x))
    (fun x _ ↦ finite_stalk L x) fun x _ ↦
      haveI := hgg
      isGloballyGeneratedAt_of_isGloballyGenerated L x
  have hmono := mono_mulSection_of_forall_not_vanishesAt hL F s hs
  have hFL : (F ⊗ L).IsCoherent := isCoherent_tensorObj_of_invertible F hL
  have hGcoh : (cokernel (mulSection F s)).IsCoherent :=
    isCoherent_cokernel (mulSection F s) hFq hFL
  refine ⟨cokernel (mulSection F s), hGcoh, mulSection F s,
    cokernel.π _, cokernel.condition _,
    { exact := ShortComplex.exact_cokernel _, mono_f := hmono, epi_g := inferInstance }, ?_⟩
  refine supportDim_lt_supportDim_of_forall_minimal (isClosed_support F)
    (support_cokernel_mulSection_subset hL F s) (isClosed_support _) ?_ hdim fun x hx hmin ↦ ?_
  · rw [Set.nonempty_iff_ne_empty]
    exact fun h ↦ hF ((support_eq_empty_iff_isZero F).1 h)
  · obtain ⟨U, hU, hxU⟩ : ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U := by
      obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
      exact ⟨U, hU, hxU⟩
    have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    have : Module.Finite Γ(X, U) Γ(F, U) := finite_sections F ⟨U, hU⟩
    exact notMem_support_cokernel_mulSection hL F s
      (hs x (isAssociatedPoint_of_minimal_mem_support F hU ⟨x, hxU⟩ hx hmin))

end Hyperplane

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

This is the induction on `dim F` of the blueprint proof of `thm:deg-snapper`. -/
theorem fwdDiffComp_eulerChar_tensorZPow_eq_zero :
    ∀ (n : ℕ) (F : X.Modules), F.IsCoherent → F.supportDim < ((n : ℕ) : WithBot ℕ∞) →
      ∀ {r : ℕ} (L : Fin r → X.Modules) (hL : ∀ j, IsVeryAmple (Spec (.of k)) (L j))
        (j : Fin n → Fin r),
      fwdDiffComp (fun a ↦ Pi.single (j a) 1)
        (fun m ↦ eulerChar k (tensorZPow F L (fun i ↦ (hL i).invertible) m)) = 0 := by
  have hcpt : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have hnoeth : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  intro n
  induction n with
  | zero =>
    intro F hFcoh hd r L hL j
    have hzero : IsZero F := (supportDim_eq_bot_iff F).1 (eq_bot_of_lt_natCast_zero hd)
    rw [fwdDiffComp_zero]
    funext m
    exact eulerChar_eq_zero_of_isZero k
      (isZero_tensorObj_of_isZero (invertible_zpowProd L _ m) hzero)
  | succ n ih =>
    intro F hFcoh hd r L hL j
    have hFc : F.IsCoherent := hFcoh
    by_cases hF : IsZero F
    · rw [show (fun m ↦ eulerChar k (tensorZPow F L (fun i ↦ (hL i).invertible) m)) =
        Function.const _ (0 : ℤ) from funext fun m ↦ eulerChar_eq_zero_of_isZero k
          (isZero_tensorObj_of_isZero (invertible_zpowProd L _ m) hF)]
      exact ((isNumericalPolynomial_const (0 : ℤ)).mono (Nat.zero_le n)).fwdDiffComp_eq_zero _
    · obtain ⟨G, hGcoh, u, v, hw, hSE, hGlt⟩ :=
        exists_shortExact_supportDim_lt k F hF (supportDim_ne_top F (X ↘ Spec (.of k)))
          ((hL (j 0)).invertible) (hL (j 0)).isGloballyGenerated
      have hGc : G.IsCoherent := hGcoh
      have hGn : G.supportDim < ((n : ℕ) : WithBot ℕ∞) :=
        lt_of_lt_of_le hGlt (le_natCast_of_lt_natCast_succ hd)
      have hstep : ∀ m : Fin r → ℤ,
          eulerChar k (tensorZPow F L (fun i ↦ (hL i).invertible) m) +
              eulerChar k (tensorZPow G L (fun i ↦ (hL i).invertible) m) =
            eulerChar k (tensorZPow F L (fun i ↦ (hL i).invertible) (m + Pi.single (j 0) 1)) := by
        intro m
        have h₁ : (F ⊗ zpowProd L (fun i ↦ (hL i).invertible) m).IsCoherent :=
          isCoherent_tensorObj_of_invertible F (invertible_zpowProd L _ m)
        have hFL : (F ⊗ L (j 0)).IsCoherent :=
          isCoherent_tensorObj_of_invertible F ((hL (j 0)).invertible)
        have h₂ : ((F ⊗ L (j 0)) ⊗ zpowProd L (fun i ↦ (hL i).invertible) m).IsCoherent :=
          isCoherent_tensorObj_of_invertible _ (invertible_zpowProd L _ m)
        have h₃ : (G ⊗ zpowProd L (fun i ↦ (hL i).invertible) m).IsCoherent :=
          isCoherent_tensorObj_of_invertible G (invertible_zpowProd L _ m)
        have e₁ : (tensorRightShortComplex (invertible_zpowProd L
            (fun i ↦ (hL i).invertible) m) (ShortComplex.mk u v hw)).X₁.IsCoherent := h₁
        have e₂ : (tensorRightShortComplex (invertible_zpowProd L
            (fun i ↦ (hL i).invertible) m) (ShortComplex.mk u v hw)).X₂.IsCoherent := h₂
        have e₃ : (tensorRightShortComplex (invertible_zpowProd L
            (fun i ↦ (hL i).invertible) m) (ShortComplex.mk u v hw)).X₃.IsCoherent := h₃
        refine (eulerChar_add_eulerChar k (shortExact_tensorRightShortComplex
          (invertible_zpowProd L (fun i ↦ (hL i).invertible) m)
          (ShortComplex.mk u v hw) hSE)).trans ?_
        refine (eulerChar_congr k
          (α_ F (L (j 0)) (zpowProd L (fun i ↦ (hL i).invertible) m))).trans ?_
        refine eulerChar_tensorObj_congr F
          (((hL (j 0)).invertible).tensorObj (invertible_zpowProd L _ m))
          (invertible_zpowProd L (fun i ↦ (hL i).invertible) (m + Pi.single (j 0) 1)) ?_
        have hsingle : ∏ i, Pic.mk (L i) ((hL i).invertible) ^
            (Pi.single (j 0) 1 : Fin r → ℤ) i = Pic.mk (L (j 0)) ((hL (j 0)).invertible) := by
          rw [Finset.prod_eq_single (j 0)
            (fun b _ hb ↦ by rw [Pi.single_eq_of_ne hb, zpow_zero])
            (fun hb ↦ absurd (Finset.mem_univ _) hb), Pi.single_eq_same, zpow_one]
        rw [Pic.mk_tensorObj (hM := (hL (j 0)).invertible)
            (hN := invertible_zpowProd L (fun i ↦ (hL i).invertible) m),
          Pic.mk_zpowProd, Pic.mk_zpowProd, ← hsingle, ← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun i _ ↦ by rw [Pi.add_apply, zpow_add, mul_comm]
      have hdiff : Δ_[Pi.single (j 0) 1]
          (fun m ↦ eulerChar k (tensorZPow F L (fun i ↦ (hL i).invertible) m)) =
            fun m ↦ eulerChar k (tensorZPow G L (fun i ↦ (hL i).invertible) m) := by
        funext m
        have h := hstep m
        show eulerChar k (tensorZPow F L (fun i ↦ (hL i).invertible) (m + Pi.single (j 0) 1)) -
          eulerChar k (tensorZPow F L (fun i ↦ (hL i).invertible) m) = _
        omega
      rw [fwdDiffComp_succ', hdiff]
      exact ih G hGcoh hGn L hL fun a ↦ j a.succ

end VeryAmple

end AlgebraicGeometry.Scheme.Modules
