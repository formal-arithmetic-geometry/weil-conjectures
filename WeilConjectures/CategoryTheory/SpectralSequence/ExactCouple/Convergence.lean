/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.SpectralSequence.ExactCouple.Iterate
public import WeilConjectures.CategoryTheory.SpectralSequence.Filtration

/-!
# Half-plane convergence of exact couples

Let `X = (D, E, α, f, g)` be an exact couple (of type `0`) in an abelian category and `a : ℤ`
such that `D^{p,q} = 0` for `q < a` and `E^{p,q} = 0` unless `p ≥ 0` and `q ≥ a`
(`CategoryTheory.ExactCouple.IsHalfPlane`). Then:

* the maps `α : D^{p,q} ⟶ D^{p-1,q+1}` are isomorphisms for `p ≤ 0`;
* the `E`-terms stabilise: `E_{r+1}^{p,q} ≅ E_r^{p,q}` as soon as `r > max (q - a + 1) p`, the
  isomorphism coming from the vanishing of the differentials into and out of `(p, q)`
  (`CategoryTheory.ExactCouple.IsHalfPlane.iterSuccEIso`); we write `E_∞^{p,q}` for the stable
  value (`CategoryTheory.ExactCouple.EInfty`);
* the abutment `Aⁿ = D^{0,n}` carries the finite filtration
  `Fᵖ Aⁿ = im (αᵖ : D^{p,n-p} ⟶ Aⁿ)` (`p ≥ 0`), `Fᵖ Aⁿ = Aⁿ` (`p ≤ 0`)
  (`CategoryTheory.ExactCouple.abutmentFiltration`), and `E_∞^{p,q} ≅ grᵖ A^{p+q}`
  (`CategoryTheory.ExactCouple.IsHalfPlane.grIsoEInfty`).

In the numbering of `CategoryTheory.ExactCouple.iter`, the page `E_r` is `(X.iter (r - 2)).E`.
This is blueprint `thm-sp-half-plane-convergence`.

## References

* [Stacks Project, Tag 011P](https://stacks.math.columbia.edu/tag/011P)
-/

@[expose] public section

namespace CategoryTheory

open Category Limits

namespace ExactCouple

variable {C : Type*} [Category* C] [Abelian C]

/-- The hypotheses of half-plane convergence for an exact couple: `D^{p,q} = 0` for `q < a` and
`E^{p,q} = 0` unless `p ≥ 0` and `q ≥ a` (`thm-sp-half-plane-convergence`). -/
structure IsHalfPlane (X : ExactCouple C 0) (a : ℤ) : Prop where
  isZero_D (p q : ℤ) (hq : q < a) : IsZero (X.D p q)
  isZero_E (p q : ℤ) (h : p < 0 ∨ q < a) : IsZero (X.E p q)

section General

variable (X : ExactCouple C 0)

lemma isZero_iter_D_of_isZero (k : ℕ) (p q : ℤ) (hz : IsZero (X.D (p + k) (q - k))) :
    IsZero ((X.iter k).D p q) := by
  rw [IsZero.iff_id_eq_zero,
    ← cancel_epi (X.αbarIter k (p + k) (q - k) p q rfl (sub_add_cancel q k))]
  exact hz.eq_of_src _ _

/-- The image filtration of the abutment `Aⁿ = D^{0,n}`: `Fᵖ Aⁿ` is the image of
`αᵖ : D^{p,n-p} ⟶ D^{0,n}` for `p ≥ 0` and `Fᵖ Aⁿ = Aⁿ` for `p < 0`
(`thm-sp-half-plane-convergence`, with `Fᵖ Aⁿ = G_{n-p} Aⁿ`). -/
noncomputable def abutmentFiltration (n : ℤ) : DecreasingFiltration (X.D 0 n) where
  F p := if hp : 0 ≤ p then imageSubobject (X.αPow p.toNat p (n - p) 0 n (by lia) (by lia))
    else ⊤
  antitone p p' hpp' := by
    dsimp only
    by_cases hp' : 0 ≤ p'
    · by_cases hp : 0 ≤ p
      · rw [dif_pos hp', dif_pos hp,
          X.αPow_congr p'.toNat ((p' - p).toNat + p.toNat) (by lia),
          X.αPow_add (p' - p).toNat p.toNat p' (n - p') p (n - p) 0 n (by lia) (by lia) (by lia)
            (by lia)]
        exact imageSubobject_comp_le _ _
      · rw [dif_neg hp]
        exact le_top
    · rw [dif_neg hp', dif_neg (by lia : ¬ 0 ≤ p)]

lemma abutmentFiltration_F_of_nonneg (n p : ℤ) (hp : 0 ≤ p) (k : ℕ) (hk : (k : ℤ) = p) :
    (X.abutmentFiltration n).F p = imageSubobject (X.αPow k p (n - p) 0 n (by lia) (by lia)) := by
  obtain rfl : k = p.toNat := by lia
  exact dif_pos hp

lemma abutmentFiltration_F_of_nonpos (n p : ℤ) (hp : p ≤ 0) :
    (X.abutmentFiltration n).F p = ⊤ := by
  by_cases hp' : 0 ≤ p
  · obtain rfl : p = 0 := by lia
    rw [X.abutmentFiltration_F_of_nonneg n 0 le_rfl 0 rfl, ← Subobject.isIso_arrow_iff_eq_top]
    have : Epi (imageSubobject (X.αPow 0 0 (n - 0) 0 n (by lia) (by lia))).arrow := by
      have : Epi (X.αPow 0 0 (n - 0) 0 n (by lia) (by lia)) := by
        rw [αPow_zero']; infer_instance
      exact epi_of_epi_fac (imageSubobject_arrow_comp _)
    exact isIso_of_mono_of_epi _
  · exact dif_neg hp'


/-- `αᵏ : D^{j,n-j} ⟶ D^{u,v}` (`u + k = j`, `u ≤ 0`) factors as `αʲ : D^{j,n-j} ⟶ D^{0,n}`
followed by `α^{-u} : D^{0,n} ⟶ D^{u,v}`. -/
lemma αPow_eq_comp (n j : ℤ) (k : ℕ) (u v : ℤ) (hj : 0 ≤ j) (hu : u + k = j)
    (hv : n - j + k = v) (hu0 : u ≤ 0) :
    X.αPow k j (n - j) u v hu (by lia) =
      X.αPow j.toNat j (n - j) 0 n (by lia) (by lia) ≫
        X.αPow (-u).toNat 0 n u v (by lia) (by lia) := by
  rw [X.αPow_congr k (j.toNat + (-u).toNat) (by lia)]
  exact X.αPow_add _ _ _ _ _ _ _ _ _ _ _ _ _ _


lemma kernel_ι_factorThruImageSubobject_αbarIter (n j : ℤ) (k : ℕ) (u v : ℤ) (hj : 0 ≤ j)
    (hu : u + k = j) (hv : n - j + k = v) (hu0 : u ≤ 0) :
    kernel.ι (factorThruImageSubobject (X.αPow j.toNat j (n - j) 0 n (by lia) (by lia))) ≫
      X.αbarIter k j (n - j) u v hu (by lia) = 0 := by
  rw [← cancel_mono (X.ιIter k u v), assoc, αbarIter_ιIter, zero_comp,
    X.αPow_eq_comp n j k u v hj hu hv hu0,
    ← imageSubobject_arrow_comp_assoc (X.αPow j.toNat j (n - j) 0 n (by lia) (by lia)),
    kernel.condition_assoc, zero_comp]
/-- The map `Fʲ Aⁿ ⟶ D_{k+2}^{u,v}` (`u + k = j`, `u ≤ 0`) induced by
`α^{-u} : Aⁿ = D^{0,n} ⟶ D^{u,v}`: by claim 4 of `lem-sp-derived-couple-exact`
(`CategoryTheory.ExactCouple.imageSubobject_αPow`) the subobject `D_{k+2}^{u,v}` of `D^{u,v}` is
the image of `αᵏ = α^{-u} ∘ αʲ`, i.e. the image of `Fʲ Aⁿ` under `α^{-u}`. -/
noncomputable def abutmentStepToIter (n j : ℤ) (k : ℕ) (u v : ℤ) (hj : 0 ≤ j) (hu : u + k = j)
    (hv : n - j + k = v) (hu0 : u ≤ 0) :
    ((X.abutmentFiltration n).F j : C) ⟶ (X.iter k).D u v :=
  Subobject.ofLE _ _ (X.abutmentFiltration_F_of_nonneg n j hj j.toNat (by lia)).le ≫
    Abelian.epiDesc (factorThruImageSubobject (X.αPow j.toNat j (n - j) 0 n (by lia) (by lia)))
      (X.αbarIter k j (n - j) u v hu (by lia))
      (X.kernel_ι_factorThruImageSubobject_αbarIter n j k u v hj hu hv hu0)

@[reassoc]
lemma abutmentStepToIter_ιIter (n j : ℤ) (k : ℕ) (u v : ℤ) (hj : 0 ≤ j) (hu : u + k = j)
    (hv : n - j + k = v) (hu0 : u ≤ 0) :
    X.abutmentStepToIter n j k u v hj hu hv hu0 ≫ X.ιIter k u v =
      ((X.abutmentFiltration n).F j).arrow ≫ X.αPow (-u).toNat 0 n u v (by lia) (by lia) := by
  have : Abelian.epiDesc (factorThruImageSubobject (X.αPow j.toNat j (n - j) 0 n (by lia)
      (by lia))) (X.αbarIter k j (n - j) u v hu (by lia))
      (X.kernel_ι_factorThruImageSubobject_αbarIter n j k u v hj hu hv hu0) ≫ X.ιIter k u v =
      (imageSubobject (X.αPow j.toNat j (n - j) 0 n (by lia) (by lia))).arrow ≫
        X.αPow (-u).toNat 0 n u v (by lia) (by lia) := by
    rw [← cancel_epi (factorThruImageSubobject _), Abelian.comp_epiDesc_assoc,
      αbarIter_ιIter, imageSubobject_arrow_comp_assoc, X.αPow_eq_comp n j k u v hj hu hv hu0]
  rw [abutmentStepToIter, assoc, this, Subobject.ofLE_arrow_assoc]

lemma epi_abutmentStepToIter (n j : ℤ) (k : ℕ) (u v : ℤ) (hj : 0 ≤ j) (hu : u + k = j)
    (hv : n - j + k = v) (hu0 : u ≤ 0) :
    Epi (X.abutmentStepToIter n j k u v hj hu hv hu0) := by
  have e := X.abutmentFiltration_F_of_nonneg n j hj j.toNat (by lia)
  have : IsIso (Subobject.ofLE _ _ e.le) :=
    ⟨⟨Subobject.ofLE _ _ e.ge, by simp, by simp⟩⟩
  have : Epi (Abelian.epiDesc (factorThruImageSubobject (X.αPow j.toNat j (n - j) 0 n (by lia)
      (by lia))) (X.αbarIter k j (n - j) u v hu (by lia))
      (X.kernel_ι_factorThruImageSubobject_αbarIter n j k u v hj hu hv hu0)) :=
    epi_of_epi_fac (Abelian.comp_epiDesc _ _ _)
  rw [abutmentStepToIter]
  infer_instance

/-- The steps `Fᵖ⁺¹ Aⁿ ⊆ Fᵖ Aⁿ` correspond to `α_{k+2} : D_{k+2}^{u+1,v-1} ⟶ D_{k+2}^{u,v}`. -/
@[reassoc]
lemma abutmentFiltration_incl_stepToIter (n p : ℤ) (k : ℕ) (u v : ℤ) (hp : 0 ≤ p)
    (hu : u + k = p) (hv : n - p + k = v) (hu0 : u + 1 ≤ 0) :
    (X.abutmentFiltration n).incl p (p + 1) ≫ X.abutmentStepToIter n p k u v hp hu hv (by lia) =
      X.abutmentStepToIter n (p + 1) k (u + 1) (v - 1) (by lia) (by lia) (by lia) hu0 ≫
        (X.iter k).α (u + 1) (v - 1) u v := by
  rw [← cancel_mono (X.ιIter k u v), assoc, assoc, X.abutmentStepToIter_ιIter,
    X.iter_α_ιIter k (u + 1) (v - 1) u v (by lia) (by lia), X.abutmentStepToIter_ιIter_assoc,
    DecreasingFiltration.incl, Subobject.ofLE_arrow_assoc,
    X.αPow_congr (-u).toNat ((-(u + 1)).toNat + 1) (by lia),
    X.αPow_succ' (-(u + 1)).toNat 0 n u v (by lia) (by lia)]
end General

namespace IsHalfPlane

variable {X : ExactCouple C 0} {a : ℤ} (h : X.IsHalfPlane a)
include h

lemma isIso_α (p q p' q' : ℤ) (hp : p' + 1 = p) (hq : q + 1 = q') (hp0 : p ≤ 0) :
    IsIso (X.α p q p' q' hp hq) := by
  have : Mono (X.α p q p' q' hp hq) :=
    (X.exact_f_α (p - 2) (q + 1) p q p' q').mono_g
      ((h.isZero_E _ _ (Or.inl (by lia))).eq_of_src _ _)
  have : Epi (X.α p q p' q' hp hq) :=
    (X.exact_α_g p q p' q' p' q').epi_f ((h.isZero_E _ _ (Or.inl (by lia))).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

lemma isIso_αPow (k : ℕ) (p q p' q' : ℤ) (hp : p' + k = p) (hq : q + k = q') (hp0 : p ≤ 0) :
    IsIso (X.αPow k p q p' q' hp hq) := by
  induction k generalizing p q with
  | zero => rw [αPow_zero']; infer_instance
  | succ k ih =>
    rw [αPow_succ]
    have := h.isIso_α p q (p - 1) (q + 1) (by lia) rfl hp0
    have := ih (p - 1) (q + 1) (by lia) (by lia) (by lia)
    infer_instance

lemma isZero_iter_E (k : ℕ) (p q : ℤ) (hpq : p < 0 ∨ q < a) : IsZero ((X.iter k).E p q) :=
  X.isZero_iter_E k p q (h.isZero_E p q hpq)

lemma isZero_iter_D (k : ℕ) (p q : ℤ) (hq : q < a + k) : IsZero ((X.iter k).D p q) :=
  X.isZero_iter_D_of_isZero k p q (h.isZero_D _ _ (by lia))

/-- Stabilisation of the pages: for `p ≤ k + 1` and `q ≤ a + k`, i.e. `r = k + 2 > p` and
`r > q - a + 1`, the differentials of `E_r` into and out of `(p, q)` vanish and
`E_{r+1}^{p,q} = ker d_r / im d_r ≅ E_r^{p,q}` (`thm-sp-half-plane-convergence`). -/
noncomputable def iterSuccEIso (k : ℕ) (p q : ℤ) (hk : p ≤ k + 1) (hk' : q ≤ a + k) :
    (X.iter (k + 1)).E p q ≅ (X.iter k).E p q := by
  let S := (X.iter k).dSc p q
  have hf : S.f = 0 := (h.isZero_iter_E k _ _ (Or.inl (by lia))).eq_of_src _ _
  have hg : S.g = 0 := (h.isZero_iter_E k _ _ (Or.inr (by lia))).eq_of_tgt _ _
  have := S.isIso_homologyπ hf
  have := S.isIso_iCycles hg
  exact (asIso S.homologyπ).symm ≪≫ asIso S.iCycles

/-- The composite of the stabilisation isomorphisms `E_l^{p,q} ≅ E_k^{p,q}` for `k ≤ l`. -/
noncomputable def iterEIsoOfLE (p q : ℤ) (k : ℕ) (hk : p ≤ k + 1) (hk' : q ≤ a + k) :
    (l : ℕ) → k ≤ l → ((X.iter l).E p q ≅ (X.iter k).E p q)
  | 0, hl => eqToIso (by obtain rfl : k = 0 := (by lia); rfl)
  | l + 1, hl =>
    if hkl : k = l + 1 then eqToIso (by subst hkl; rfl)
    else h.iterSuccEIso l p q (by lia) (by lia) ≪≫ iterEIsoOfLE p q k hk hk' l (by lia)

end IsHalfPlane

/-- The index `k = max (p + 1) (q - a)` of the page `E_{k+2}` at which we read off the stable
value `E_∞^{p,q}` of a half-plane exact couple; from `k = max (p - 1) (q - a)` on the pages are
already stable (`CategoryTheory.ExactCouple.IsHalfPlane.iterSuccEIso`). -/
def stableIndex (a p q : ℤ) : ℕ := (max (p + 1) (q - a)).toNat

/-- The term `E_∞^{p,q}` of a half-plane exact couple, the stable value of the pages
(`def-sp-convergence`, `thm-sp-half-plane-convergence`). -/
noncomputable def EInfty (X : ExactCouple C 0) (a p q : ℤ) : C :=
  (X.iter (stableIndex a p q)).E p q

namespace IsHalfPlane

variable {X : ExactCouple C 0} {a : ℤ} (h : X.IsHalfPlane a)
include h

/-- `E_r^{p,q} ≅ E_∞^{p,q}` as soon as the page `E_r = (X.iter k).E` is stable at `(p, q)`. -/
noncomputable def iterEIsoEInfty (p q : ℤ) (k : ℕ) (hk : p ≤ k + 1) (hk' : q ≤ a + k) :
    (X.iter k).E p q ≅ X.EInfty a p q :=
  if hkl : k ≤ stableIndex a p q then
    (h.iterEIsoOfLE p q k hk hk' _ hkl).symm
  else
    h.iterEIsoOfLE p q (stableIndex a p q) (by simp only [stableIndex]; lia)
      (by simp only [stableIndex]; lia) k (by lia)

end IsHalfPlane


namespace IsHalfPlane

variable {X : ExactCouple C 0} {a : ℤ} (h : X.IsHalfPlane a)
include h

/-- The filtration of the abutment vanishes in degrees `p > n - a`. -/
lemma abutmentFiltration_F_eq_bot (n p : ℤ) (hp : n - a < p) (hp0 : 0 ≤ p) :
    (X.abutmentFiltration n).F p = ⊥ := by
  rw [X.abutmentFiltration_F_of_nonneg n p hp0 p.toNat (by lia),
    (h.isZero_D p (n - p) (by lia)).eq_of_src (X.αPow _ _ _ _ _ _ _) 0, imageSubobject_zero]

/-- The filtration of the abutment `Aⁿ` of a half-plane exact couple is finite: it is `Aⁿ` in
degrees `p ≤ 0` and `0` in degrees `p > n - a` (`thm-sp-half-plane-convergence`). -/
lemma abutmentFiltration_isFinite (n : ℤ) : (X.abutmentFiltration n).IsFinite :=
  ⟨⟨0, fun p hp ↦ X.abutmentFiltration_F_of_nonpos n p hp⟩,
    ⟨max (n - a + 1) 0, fun p hp ↦ h.abutmentFiltration_F_eq_bot n p
      (by have := le_of_max_le_left hp; lia) (le_of_max_le_right hp)⟩⟩

lemma isIso_abutmentStepToIter (n j : ℤ) (k : ℕ) (u v : ℤ) (hj : 0 ≤ j) (hu : u + k = j)
    (hv : n - j + k = v) (hu0 : u ≤ 0) :
    IsIso (X.abutmentStepToIter n j k u v hj hu hv hu0) := by
  have := X.epi_abutmentStepToIter n j k u v hj hu hv hu0
  have := h.isIso_αPow (-u).toNat 0 n u v (by lia) (by lia) le_rfl
  have : Mono (X.abutmentStepToIter n j k u v hj hu hv hu0 ≫ X.ιIter k u v) := by
    rw [X.abutmentStepToIter_ιIter]
    infer_instance
  have : Mono (X.abutmentStepToIter n j k u v hj hu hv hu0) :=
    mono_of_mono _ (X.ιIter k u v)
  exact isIso_of_mono_of_epi _

/-- The isomorphism `Fʲ Aⁿ ≅ D_{k+2}^{u,v}` (`u + k = j ≥ 0`, `u ≤ 0`) induced by
`α^{-u} : Aⁿ ⟶ D^{u,v}`. -/
noncomputable def abutmentStepIsoIter (n j : ℤ) (k : ℕ) (u v : ℤ) (hj : 0 ≤ j) (hu : u + k = j)
    (hv : n - j + k = v) (hu0 : u ≤ 0) :
    ((X.abutmentFiltration n).F j : C) ≅ (X.iter k).D u v :=
  have := h.isIso_abutmentStepToIter n j k u v hj hu hv hu0
  asIso (X.abutmentStepToIter n j k u v hj hu hv hu0)

/-- The short complex `D_{k+2}^{p-k+1,q+k-1} ⟶ D_{k+2}^{p-k,q+k} ⟶ E_{k+2}^{p,q}` given by
`α_{k+2}` and `g_{k+2}`. -/
omit h in
noncomputable abbrev αgSc (X : ExactCouple C 0) (k : ℕ) (p q : ℤ) : ShortComplex C :=
  ShortComplex.mk _ _ ((X.iter k).α_g (p - k + 1) (q + k - 1) (p - k) (q + k) p q)

omit h in
lemma αgSc_exact (k : ℕ) (p q : ℤ) : (αgSc X k p q).Exact :=
  (X.iter k).exact_α_g (p - k + 1) (q + k - 1) (p - k) (q + k) p q

lemma epi_αgSc_g (k : ℕ) (p q : ℤ) (hk' : q - a ≤ k) : Epi (αgSc X k p q).g :=
  ((X.iter k).exact_g_f (p - k) (q + k) p q (p + 2) (q - 1)).epi_f
    ((h.isZero_iter_D k (p + 2) (q - 1) (by lia)).eq_of_tgt _ _)

/-- For `k ≥ p + 1`, `k ≥ q - a` (i.e. `r = k + 2 ≥ max (p + 3) (q - a + 2)`) and `p ≥ 0`, the
isomorphism `ψ_r : grᵖ A^{p+q} ≅ E_r^{p,q}` induced by `g_r : D_r^{p-k,q+k} ⟶ E_r^{p,q}`
through `D_r^{p-k,q+k} ≅ Fᵖ A^{p+q}` and `α_r (D_r^{p-k+1,q+k-1}) ≅ Fᵖ⁺¹ A^{p+q}`
(`thm-sp-half-plane-convergence`, Step 2; the `ψ_r` of `lem-sp-exact-functor-couple`). -/
noncomputable def grIsoIterE (k : ℕ) (p q n : ℤ) (hn : p + q = n) (hp : 0 ≤ p)
    (hk : p + 1 ≤ k) (hk' : q - a ≤ k) :
    (X.abutmentFiltration n).gr p ≅ (X.iter k).E p q :=
  have := h.epi_αgSc_g k p q hk'
  cokernel.mapIso _ _
      (h.abutmentStepIsoIter n (p + 1) k (p - k + 1) (q + k - 1) (by lia) (by lia) (by lia)
        (by lia))
      (h.abutmentStepIsoIter n p k (p - k) (q + k) hp (by lia) (by lia) (by lia))
      (X.abutmentFiltration_incl_stepToIter n p k (p - k) (q + k) hp (by lia) (by lia)
        (by lia)) ≪≫
    IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel _) (h.αgSc_exact k p q).gIsCokernel

@[reassoc]
lemma grπ_grIsoIterE_hom (k : ℕ) (p q n : ℤ) (hn : p + q = n) (hp : 0 ≤ p)
    (hk : p + 1 ≤ k) (hk' : q - a ≤ k) :
    (X.abutmentFiltration n).grπ p ≫ (h.grIsoIterE k p q n hn hp hk hk').hom =
      X.abutmentStepToIter n p k (p - k) (q + k) hp (by lia) (by lia) (by lia) ≫
        (X.iter k).g (p - k) (q + k) p q := by
  have := h.epi_αgSc_g k p q hk'
  simp only [grIsoIterE, Iso.trans_hom, DecreasingFiltration.grπ, cokernel.mapIso_hom,
    cokernel.π_desc_assoc, abutmentStepIsoIter, asIso_hom, assoc]
  exact congrArg (_ ≫ ·)
    (IsColimit.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel _) _ WalkingParallelPair.one)

/-- Convergence of a half-plane exact couple (`thm-sp-half-plane-convergence`): for `p ≥ 0`,
`E_∞^{p,q} ≅ grᵖ A^{p+q}` for the image filtration `Fᵖ Aⁿ = im (αᵖ : D^{p,n-p} ⟶ D^{0,n})` of
the abutment (`CategoryTheory.ExactCouple.abutmentFiltration`, finite by
`CategoryTheory.ExactCouple.IsHalfPlane.abutmentFiltration_isFinite`). -/
noncomputable def grIsoEInfty (p q n : ℤ) (hn : p + q = n) (hp : 0 ≤ p) :
    (X.abutmentFiltration n).gr p ≅ X.EInfty a p q :=
  h.grIsoIterE (stableIndex a p q) p q n hn hp (by simp only [stableIndex]; lia)
    (by simp only [stableIndex]; lia) ≪≫
  h.iterEIsoEInfty p q _ (by simp only [stableIndex]; lia) (by simp only [stableIndex]; lia)

end IsHalfPlane

end ExactCouple

end CategoryTheory
