/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import WeilConjectures.LinearAlgebra.Matrix.RowMinorIdealStableInvariance
import WeilConjectures.LinearAlgebra.Matrix.RowMinorIdealScalarExtension
import WeilConjectures.LinearAlgebra.FreeSurjectionsCommonStabilization

/-!
# Kernel-row Fitting ideals and change of scalars

Source: Stacks Project, More on Algebra, Tags 07Z8 and 07ZA(3)
(blueprint: lem-trf-fitting-ideal-independence-base-change).

## Main definitions

* `LinearMap.presentationFittingIdeal`: the ideal of minors of kernel rows.
* `LinearMap.baseChangePresentation`: the canonical base-changed finite free presentation.
* `LinearMap.localizePresentationAway`: that presentation in the localized module.

## Main statements

* `LinearMap.presentationFittingIdeal_independence_baseChange`: presentation independence,
  arbitrary base change, and localization away from one element.
-/

@[expose] public section

universe u v w

open TensorProduct

namespace LinearMap

/-- The kernel-row ideal `I_k(π)` of Stacks Project, More on Algebra, Tag 07Z8:
span all determinants formed from `n-k` kernel rows and `n-k` distinct columns. When `n ≤ k`
it is the unit ideal. Surjectivity is only needed for the independence theorem, not to form
this ideal. (blueprint: lem-trf-fitting-ideal-independence-base-change) -/
noncomputable def presentationFittingIdeal {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] {n : ℕ}
    (π : (Fin n → R) →ₗ[R] M) (k : ℕ) : Ideal R :=
  if n ≤ k then ⊤ else
    Ideal.span {a | ∃ (A : Matrix (Fin (n - k)) (Fin n) R)
      (c : Fin (n - k) ↪ Fin n),
      (∀ i, π (A i) = 0) ∧ (A.submatrix (fun i ↦ i) c).det = a}

/-- Base change of a finite free presentation, using the canonical identification
`A ⊗[R] (Fin n → R) ≃ₗ[A] (Fin n → A)` of Mathlib's `TensorProduct.piScalarRight`.
It sends the `i`th standard basis vector to `1 ⊗ₜ π(e_i)`. Source: Stacks Project,
More on Algebra, Tag 07ZA(3).
(blueprint: lem-trf-fitting-ideal-independence-base-change) -/
noncomputable def baseChangePresentation {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] (A : Type w)
    [CommRing A] [Algebra R A] {n : ℕ} (π : (Fin n → R) →ₗ[R] M) :
    (Fin n → A) →ₗ[A] A ⊗[R] M :=
  (π.baseChange A).comp (TensorProduct.piScalarRight R A A (Fin n)).symm.toLinearMap

/-- The canonical localized presentation with codomain `M_g`, obtained by transporting
`baseChangePresentation` through Mathlib's canonical localization/tensor equivalence.
Source: Stacks Project, More on Algebra, Tag 07ZA(3), specialized to `R → R_g`.
(blueprint: lem-trf-fitting-ideal-independence-base-change) -/
noncomputable def localizePresentationAway {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] {n : ℕ}
    (π : (Fin n → R) →ₗ[R] M) (g : R) :
    (Fin n → Localization.Away g) →ₗ[Localization.Away g] LocalizedModule.Away g M :=
  (IsLocalizedModule.isBaseChange (Submonoid.powers g) (Localization.Away g)
    (LocalizedModule.mkLinearMap (Submonoid.powers g) M)).equiv.toLinearMap |>.comp
      (π.baseChangePresentation (Localization.Away g))

private theorem univ_orderEmb (r : ℕ) :
    ((Finset.univ : Finset (Fin r)).orderEmbOfFin (by simp) : Fin r → Fin r) = _root_.id := by
  exact (Finset.orderEmbOfFin_unique (by simp) (fun _ ↦ Finset.mem_univ _)
    (fun _ _ h ↦ h)).symm

private theorem presentation_eq_row {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] {n : ℕ}
    (π : (Fin n → R) →ₗ[R] M) (k : ℕ) :
    π.presentationFittingIdeal k = Matrix.rowMinorIdeal n k (ker π) := by
  classical
  by_cases hk : n ≤ k
  · simp [presentationFittingIdeal, Matrix.rowMinorIdeal, hk]
  rw [presentationFittingIdeal, Matrix.rowMinorIdeal, if_neg hk, if_neg hk]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨A, c, hA, rfl⟩
    let T := Finset.univ.image c
    have hT : T.card = n - k := by
      simp [T, Finset.card_image_of_injective, c.injective]
    let e : Fin (n - k) → Fin (n - k) := fun i ↦
      (T.orderIsoOfFin hT).symm ⟨c i, by simp [T]⟩
    have he : Function.Injective e := by
      intro i j hij
      apply c.injective
      have h := congrArg (fun z ↦ ((T.orderIsoOfFin hT) z).val) hij
      simpa [e] using h
    let σ : Equiv.Perm (Fin (n - k)) :=
      Equiv.ofBijective e ⟨he, Finite.surjective_of_injective he⟩
    have hc : ∀ i, T.orderEmbOfFin hT (σ i) = c i := by
      intro i
      exact congrArg Subtype.val ((T.orderIsoOfFin hT).apply_symm_apply _)
    have hm : (A.submatrix _root_.id (T.orderEmbOfFin hT)).det ∈
        Matrix.minorIdeal (n - k) n (n - k) A := by
      apply Ideal.subset_span
      refine ⟨(⟨Finset.univ, by simp⟩, ⟨T, hT⟩), ?_⟩
      simp [univ_orderEmb]
    have hm' : (A.submatrix _root_.id c).det ∈ Matrix.minorIdeal (n - k) n (n - k) A := by
      have hd : A.submatrix _root_.id c =
          (A.submatrix _root_.id (T.orderEmbOfFin hT)).submatrix _root_.id σ := by
        ext i j
        simp [Matrix.submatrix, hc]
      rw [hd, Matrix.det_permute']
      exact Ideal.mul_mem_left _ _ hm
    have hle : Matrix.minorIdeal (n - k) n (n - k) A ≤
        ⨆ (B : Matrix (Fin (n - k)) (Fin n) R) (_ : ∀ i, B i ∈ ker π),
          Matrix.minorIdeal (n - k) n (n - k) B :=
      le_iSup_of_le A (le_iSup_of_le hA le_rfl)
    exact hle hm'
  · refine iSup_le fun A ↦ iSup_le fun hA ↦ Ideal.span_le.mpr ?_
    rintro _ ⟨⟨S, T⟩, rfl⟩
    apply Ideal.subset_span
    refine ⟨A.submatrix (S.val.orderEmbOfFin S.property) _root_.id,
      (T.val.orderEmbOfFin T.property).toEmbedding, fun i ↦ hA _, ?_⟩
    rfl

private def splitCoordinates (R : Type u) [CommRing R] (n m : ℕ) :
    (Fin (n + m) → R) ≃ₗ[R] ((Fin n → R) × (Fin m → R)) where
  toFun x := (fun j ↦ x (Fin.castAdd m j), fun j ↦ x (Fin.natAdd n j))
  invFun x := Fin.append x.1 x.2
  left_inv x := by
    funext i
    cases i using Fin.addCases <;> simp
  right_inv x := by
    ext i <;> simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem row_equiv {R : Type u} [CommRing R] {n m : ℕ} (hnm : n = m)
    (k : ℕ) (K : Submodule R (Fin n → R))
    (e : (Fin n → R) ≃ₗ[R] (Fin m → R)) :
    Matrix.rowMinorIdeal n k K = Matrix.rowMinorIdeal m k (K.map e.toLinearMap) := by
  subst m
  exact ((Matrix.rowMinorIdeal_stable_invariance n k K).2.2 e).symm

private theorem presentation_independent {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] {n m : ℕ}
    (π : (Fin n → R) →ₗ[R] M) (π' : (Fin m → R) →ₗ[R] M)
    (hπ : Function.Surjective π) (hπ' : Function.Surjective π') (k : ℕ) :
    π.presentationFittingIdeal k = π'.presentationFittingIdeal k := by
  obtain ⟨⟨f, g, hf, hg⟩, hs⟩ :=
    Module.free_surjections_common_stabilization R M n m π π' hπ hπ'
  obtain ⟨U, _, _, hU, _⟩ := hs f g hf hg
  let E := splitCoordinates R n m
  let E' := splitCoordinates R m n
  let V := E.trans (U.trans E'.symm)
  let p : (Fin (n + m) → R) →ₗ[R] (Fin n → R) :=
    LinearMap.pi fun j ↦ LinearMap.proj (Fin.castAdd m j)
  let q : (Fin (m + n) → R) →ₗ[R] (Fin m → R) :=
    LinearMap.pi fun j ↦ LinearMap.proj (Fin.castAdd n j)
  have hcomm : ∀ x, π' (q (V x)) = π (p x) := by
    intro x
    have h := congrArg (fun t ↦ t (E x)) hU
    change π' ((E' (V x)).1) = π (E x).1
    simpa only [V, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
      LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.fst_apply] using h
  have hmap : ((ker π).comap p).map V.toLinearMap = (ker π').comap q := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change π' (q (V x)) = 0
      rw [hcomm]
      exact hx
    · intro hy
      refine ⟨V.symm y, ?_, V.apply_symm_apply y⟩
      change π (p (V.symm y)) = 0
      rw [← hcomm, V.apply_symm_apply]
      exact hy
  rw [presentation_eq_row, presentation_eq_row]
  calc
    Matrix.rowMinorIdeal n k (ker π) =
        Matrix.rowMinorIdeal (n + m) k ((ker π).comap p) :=
      ((Matrix.rowMinorIdeal_stable_invariance n k (ker π)).2.1 m).symm
    _ = Matrix.rowMinorIdeal (m + n) k (((ker π).comap p).map V.toLinearMap) :=
      row_equiv (Nat.add_comm n m) k _ V
    _ = Matrix.rowMinorIdeal (m + n) k ((ker π').comap q) := by rw [hmap]
    _ = Matrix.rowMinorIdeal m k (ker π') :=
      (Matrix.rowMinorIdeal_stable_invariance m k (ker π')).2.1 n

private theorem presentation_baseChange {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] {n : ℕ}
    (π : (Fin n → R) →ₗ[R] M) (hπ : Function.Surjective π) (k : ℕ)
    (A : Type w) [CommRing A] [Algebra R A] :
    Function.Surjective (π.baseChangePresentation A) ∧
      (π.baseChangePresentation A).presentationFittingIdeal k =
        Ideal.map (algebraMap R A) (π.presentationFittingIdeal k) := by
  classical
  refine ⟨(π.baseChange_surjective A hπ).comp
    (TensorProduct.piScalarRight R A A (Fin n)).symm.surjective, ?_⟩
  by_cases hnk : n ≤ k
  · simp [presentationFittingIdeal, hnk, Ideal.map_top]
  obtain ⟨θ, hθ, _, hspan, hideal⟩ :=
    Matrix.rowMinorIdeal_scalar_extension (A := A) n (n - k) (ker π)
  have hθeq : θ = TensorProduct.piScalarRight R A A (Fin n) := by
    apply LinearEquiv.toLinearMap_injective
    apply AlgebraTensorModule.ext
    intro a x
    simpa [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
      Algebra.smul_def, mul_comm] using hθ x a
  have hex : Function.Exact ((ker π).subtype.baseChange A) (π.baseChange A) :=
    lTensor_exact A π.exact_subtype_ker_map hπ
  have hk : ker (π.baseChange A) = range ((ker π).subtype.baseChange A) :=
    hex.linearMap_ker_eq
  have hker : ker (π.baseChangePresentation A) =
      Submodule.span A (Set.range (fun z : ker π ↦
        fun j : Fin n ↦ algebraMap R A (z.val j))) := by
    rw [baseChangePresentation, ker_comp, hk,
      ← Submodule.map_equiv_eq_comap_symm, ← hθeq]
    exact hspan
  have hr : ¬n < n - k := by omega
  have hnk' : n - (n - k) = k := by omega
  simpa only [if_neg hr, hnk', ← hker, ← presentation_eq_row] using hideal

private theorem presentation_postcomp_equiv {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N] {n : ℕ}
    (π : (Fin n → R) →ₗ[R] M) (e : M ≃ₗ[R] N) (k : ℕ) :
    (e.toLinearMap.comp π).presentationFittingIdeal k = π.presentationFittingIdeal k := by
  have hk : ker (e.toLinearMap.comp π) = ker π := by
    ext x
    change e (π x) = 0 ↔ π x = 0
    exact e.map_eq_zero_iff
  rw [presentation_eq_row, presentation_eq_row, hk]

/-- The kernel-row ideal is independent of the finite generating surjection and commutes
with arbitrary base change, including localization. Source: Stacks Project, More on Algebra,
Tag 07Z8 and Tag 07ZA(3).
(blueprint: lem-trf-fitting-ideal-independence-base-change)

Proof plan:
1. For `n > k`, the kernel-row definition is the ideal generated by all `(n-k)`-minors
of arbitrary finite matrices with rows in the kernel: a minor only uses `n-k` rows.
This uses `lem-trf-fitting-ideal-minor-inclusions`.
2. Adjoin `d` zero generators. Pad kernel rows by zeros and append the `d` new standard
basis vectors. The block diagonal minor has the old determinant, giving one inclusion.
3. For the converse, project kernel rows onto the first `n` columns and apply the
column-extension inclusion of `lem-trf-fitting-ideal-minor-inclusions`. If `n ≤ k`, either
both ideals are unit ideals by convention, or enough added basis vectors give a unit minor.
4. An invertible coordinate change preserves the ideal, by the matrix-product minor
inclusion of that same node applied to its matrix and inverse. The case `n ≤ k` is immediate.
5. For two surjections `π : F → M`, `π' : G → M`, lift their standard basis images to maps
`f : G → F`, `g : F → G` with `π f = π'` and `π' g = π`. The invertible shear
`(x,y) ↦ (y + g(x-f(y)), x-f(y))`, with inverse
`(a,b) ↦ (b + f(a-g(b)), a-g(b))`, commutes with the zero-stabilized surjections.
Use steps 2–4 to compare the two ideals. The free-module dependency supplies the lifts.
6. Tensor the kernel sequence with `A`. Tensor right exactness
(`lem-weil-pbc-tensor-right-exact`) says the new surjection is surjective and its kernel is
the image of `A ⊗[R] ker π`, without claiming injectivity. The tensor universal property
(`def-weil-pbc-module-tensor-product`) and the canonical finite-free tensor identification
express every new kernel row as a finite `A`-linear combination of old kernel rows.
7. If `n ≤ k`, both ideals are unit ideals. Otherwise expand determinants multilinearly
using `def-weil-pbc-matrix-determinant`: each new minor is a finite linear combination of
images of old minors, and each old minor maps to the corresponding new minor. This gives
the asserted equality with `Ideal.map`, without flatness or finite presentation.
8. Specialize to `A = Localization.Away g`. The canonical equivalence
`lem-weil-pbc-localization-module-tensor` identifies this presentation with the localized
one; step 5 identifies its ideal with the presentation-independent ideal of `M_g`.
-/
theorem presentationFittingIdeal_independence_baseChange
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M] (k : ℕ) {n : ℕ} (π : (Fin n → R) →ₗ[R] M)
    (hπ : Function.Surjective π) :
    (∀ (n' : ℕ) (π' : (Fin n' → R) →ₗ[R] M), Function.Surjective π' →
      π.presentationFittingIdeal k = π'.presentationFittingIdeal k) ∧
    (∀ (A : Type w) [CommRing A] [Algebra R A],
      Function.Surjective (π.baseChangePresentation A) ∧
        (π.baseChangePresentation A).presentationFittingIdeal k =
          Ideal.map (algebraMap R A) (π.presentationFittingIdeal k)) ∧
    (∀ g : R, Function.Surjective (π.localizePresentationAway g) ∧
      (π.localizePresentationAway g).presentationFittingIdeal k =
        Ideal.map (algebraMap R (Localization.Away g)) (π.presentationFittingIdeal k)) := by
  refine ⟨fun n' π' hπ' ↦ presentation_independent π π' hπ hπ' k,
    fun A _ _ ↦ presentation_baseChange π hπ k A, ?_⟩
  intro g
  let e := (IsLocalizedModule.isBaseChange (Submonoid.powers g) (Localization.Away g)
    (LocalizedModule.mkLinearMap (Submonoid.powers g) M)).equiv
  obtain ⟨hsurj, hideal⟩ := presentation_baseChange π hπ k (Localization.Away g)
  refine ⟨e.surjective.comp hsurj, ?_⟩
  exact (presentation_postcomp_equiv (π.baseChangePresentation (Localization.Away g)) e k).trans
    hideal

end LinearMap
