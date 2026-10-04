/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.DirectSum.Finite
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Instances.Matrix
public import WeilConjectures.AlgebraicGeometry.LinearAlgebraicGroup.Weights
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Weights
public import WeilConjectures.Mathlib.LinearAlgebra.Charpoly.Basic
public import WeilConjectures.Mathlib.RepresentationTheory.Basic
public import WeilConjectures.Mathlib.RepresentationTheory.Irreducible

/-!
# Linear-algebra operations on lisse Weil sheaves

The operations of `sk-d-real-operations` and `sk-r-real-linear` on lisse Weil representations:
subquotients, finite direct sums, exterior powers and the determinant line of a lisse Weil
representation are again lisse, and an exterior power of a Weil representation whose local
characteristic polynomials are those of an `ι`-real one is again `ι`-real.

Lisseness is checked on the coefficients `g ↦ φ (ρ g v)` of the geometric part
(`AlgebraicGeometry.WeilGroup.IsLisse.continuous_apply` and
`AlgebraicGeometry.WeilGroup.IsLisse.of_continuous_apply`); reality is checked on the local
eigenvalues (`AlgebraicGeometry.WeilGroup.IsReal.map_conj_localEigenvalues` and
`AlgebraicGeometry.WeilGroup.isReal_of_map_conj_localEigenvalues`): `ι P_x` has real
coefficients exactly when the multiset of complex local eigenvalues is stable under complex
conjugation.

## Main statements

- `AlgebraicGeometry.WeilGroup.IsLisse.subquotient`, `IsLisse.directSum`,
  `IsLisse.exteriorPower`, `IsLisse.ofCharacter_detCharacter`, `IsLisse.of_equiv`.
- `AlgebraicGeometry.WeilGroup.IsReal.exteriorPower_of_charpoly_eq`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace WeilGroup

section FrobeniusWeight

variable {E : Type*} [Field E] (ι : E →+* ℂ)

/-- The `ι`-weight of a product of nonzero elements is the sum of the weights. -/
theorem frobeniusWeight_mul (qx : ℕ) {a b : E} (ha : a ≠ 0) (hb : b ≠ 0) :
    frobeniusWeight ι qx (a * b) = frobeniusWeight ι qx a + frobeniusWeight ι qx b := by
  have ha' : ‖ι a‖ ≠ 0 := by simpa using ha
  have hb' : ‖ι b‖ ≠ 0 := by simpa using hb
  simp only [frobeniusWeight, map_mul, norm_mul, Real.log_mul ha' hb']
  ring

/-- The `ι`-weight of a product of nonzero elements is the sum of the weights. -/
theorem frobeniusWeight_multiset_prod (qx : ℕ) {s : Multiset E} (hs : (0 : E) ∉ s) :
    frobeniusWeight ι qx s.prod = (s.map (frobeniusWeight ι qx)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp [frobeniusWeight]
  | cons a s ih =>
    rw [Multiset.mem_cons, not_or] at hs
    rw [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons,
      frobeniusWeight_mul ι qx (Ne.symm hs.1) (Multiset.prod_ne_zero hs.2), ih hs.2]

/-- The `ι`-weight of a finite product of nonzero elements is the sum of the weights. -/
theorem frobeniusWeight_prod (qx : ℕ) {ι' : Type*} (s : Finset ι') {f : ι' → E}
    (hf : ∀ i ∈ s, f i ≠ 0) :
    frobeniusWeight ι qx (∏ i ∈ s, f i) = ∑ i ∈ s, frobeniusWeight ι qx (f i) := by
  rw [Finset.prod_eq_multiset_prod, frobeniusWeight_multiset_prod, Multiset.map_map]
  · rfl
  · simp only [Multiset.mem_map, not_exists, not_and]
    exact fun i hi h ↦ hf i hi h

/-- Blueprint `sk-d-real-detweights`: the real weight character `a ↦ wt_{ι, q}(a)` of
`sk-d-weights`, whose determinant weights (`Representation.detWeight`) are the determinant
weights `dw_ι` of `sk-d-real-detweights`. -/
noncomputable def weightCharacter (q : ℕ) : Representation.RealWeightCharacter E where
  toFun a := Multiplicative.ofAdd (frobeniusWeight ι q (a : E))
  map_one' := by simp [frobeniusWeight]
  map_mul' a b := by
    rw [Units.val_mul, frobeniusWeight_mul ι q a.ne_zero b.ne_zero, ofAdd_add]

/-- The determinant weight for `AlgebraicGeometry.WeilGroup.weightCharacter` is
`wt_{ι, q}(det ρ(g)) / rank ρ`. -/
theorem detWeight_weightCharacter {G V : Type*} [Group G] [AddCommGroup V] [Module E V]
    (ρ : Representation E G V) (q : ℕ) (g : G) :
    ρ.detWeight (weightCharacter ι q) g =
      frobeniusWeight ι q (LinearMap.det (ρ g)) / Module.finrank E V := by
  simp [Representation.detWeight, weightCharacter, Representation.coe_detCharacter_apply]

/-- The `ι`-weight relative to `q ^ e` is the weight relative to `q`, divided by `e`. -/
theorem frobeniusWeight_pow (q e : ℕ) (a : E) :
    frobeniusWeight ι (q ^ e) a = frobeniusWeight ι q a / e := by
  simp only [frobeniusWeight, Nat.cast_pow, Real.log_pow]
  rcases eq_or_ne (e : ℝ) 0 with he | he
  · simp [he]
  · field_simp

end FrobeniusWeight

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} {p : C ⟶ Spec (.of K)} [IsCurve p]
  {W : WeilGroup p} {l : ℕ} [Fact l.Prime]

section Lisse

variable {V V' : Type u} [AddCommGroup V] [Module (PadicAlgCl l) V] [AddCommGroup V']
  [Module (PadicAlgCl l) V'] {ρ : Representation (PadicAlgCl l) W.carrier V}

/-- A representation equivalent to a lisse one is lisse. -/
theorem IsLisse.of_equiv [FiniteDimensional (PadicAlgCl l) V]
    {σ : Representation (PadicAlgCl l) W.carrier V'} (e : ρ.Equiv σ) (hρ : W.IsLisse l ρ) :
    W.IsLisse l σ :=
  IsLisse.of_continuous_apply fun φ v ↦ by
    have h := hρ.continuous_apply (φ ∘ₗ e.toLinearEquiv.toLinearMap) (e.symm v)
    refine h.congr fun g ↦ ?_
    simp only [LinearMap.comp_apply]
    congr 1
    have h₁ := LinearMap.congr_fun (e.isIntertwining' (g : W.carrier)) (e.symm v)
    simp only [LinearMap.comp_apply] at h₁
    rw [h₁]
    exact congrArg _ (e.apply_symm_apply v)

/-- A subquotient of a lisse representation is lisse. -/
theorem IsLisse.subquotient [FiniteDimensional (PadicAlgCl l) V] (hρ : W.IsLisse l ρ)
    (M N : Subrepresentation ρ) : W.IsLisse l (M.subquotient N) :=
  IsLisse.of_continuous_apply fun φ v ↦ by
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective _ v
    obtain ⟨ψ, hψ⟩ := LinearMap.exists_extend
      (φ ∘ₗ (N.toSubmodule.comap M.toSubmodule.subtype).mkQ) (p := M.toSubmodule)
    refine (hρ.continuous_apply ψ v).congr fun g ↦ ?_
    rw [show ψ (ρ g v) = (ψ ∘ₗ M.toSubmodule.subtype) ((ρ g).restrict
      (M.apply_mem_toSubmodule g) v) from rfl, hψ]
    rfl

/-- A finite direct sum of lisse representations is lisse. -/
theorem IsLisse.directSum {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module (PadicAlgCl l) (V i)]
    [∀ i, FiniteDimensional (PadicAlgCl l) (V i)]
    {ρ : ∀ i, Representation (PadicAlgCl l) W.carrier (V i)} (hρ : ∀ i, W.IsLisse l (ρ i)) :
    W.IsLisse l (Representation.directSum ρ) :=
  IsLisse.of_continuous_apply fun φ v ↦ by
    have hv (g : W.geometric) : φ (Representation.directSum ρ g v) =
        ∑ i, (φ ∘ₗ DirectSum.lof (PadicAlgCl l) ι V i) (ρ i g (v i)) := by
      conv_lhs => rw [← DirectSum.sum_univ_of v]
      simp [map_sum, DirectSum.lof_eq_of]
    simp_rw [hv]
    exact continuous_finsetSum _ fun i _ ↦ (hρ i).continuous_apply _ _

/-- An exterior power of a lisse representation is lisse. -/
theorem IsLisse.exteriorPower [FiniteDimensional (PadicAlgCl l) V] (hρ : W.IsLisse l ρ)
    (s : ℕ) : W.IsLisse l (ρ.exteriorPower s) :=
  IsLisse.of_continuous_apply fun φ x ↦ by
    have hx : x ∈ Submodule.span (PadicAlgCl l)
        (Set.range (exteriorPower.ιMulti (PadicAlgCl l) s (M := V))) := by
      rw [exteriorPower.ιMulti_span]
      trivial
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨m, rfl⟩ := hx
      let b := Module.finBasis (PadicAlgCl l) V
      have key (g : W.geometric) : φ (ρ.exteriorPower s g (exteriorPower.ιMulti _ s m)) =
          ∑ r : Fin s → Fin (Module.finrank (PadicAlgCl l) V),
            (∏ i, b.coord (r i) (ρ g (m i))) *
              φ (exteriorPower.ιMulti _ s fun i ↦ b (r i)) := by
        change φ (_root_.exteriorPower.map s (ρ g) (exteriorPower.ιMulti _ s m)) = _
        rw [exteriorPower.map_apply_ιMulti]
        have hm : (fun i ↦ ρ g (m i)) = fun i ↦ ∑ j, b.coord j (ρ g (m i)) • b j :=
          funext fun i ↦ (b.sum_repr (ρ g (m i))).symm
        rw [Function.comp_def, hm]
        let A := (φ.compAlternatingMap (exteriorPower.ιMulti (PadicAlgCl l) s (M := V)))
        change A.toMultilinearMap _ = _
        rw [MultilinearMap.map_sum]
        refine Finset.sum_congr rfl fun r _ ↦ ?_
        rw [MultilinearMap.map_smul_univ, smul_eq_mul]
        rfl
      simp_rw [key]
      exact continuous_finsetSum _ fun r _ ↦ (continuous_finsetProd _ fun i _ ↦
        hρ.continuous_apply _ _).mul continuous_const
    | zero => simpa using continuous_const
    | add x y _ _ hx hy => exact (hx.add hy).congr fun g ↦ by simp
    | smul a x _ hx =>
      exact ((continuous_const : Continuous fun _ : W.geometric ↦ a).mul hx).congr fun g ↦ by
        simp

/-- The determinant line `g ↦ det ρ(g)` of a lisse representation, realised on any module, is
lisse. -/
theorem IsLisse.ofCharacter_detCharacter [FiniteDimensional (PadicAlgCl l) V]
    (hρ : W.IsLisse l ρ) (M : Type u) [AddCommGroup M] [Module (PadicAlgCl l) M] :
    W.IsLisse l (Representation.ofCharacter ρ.detCharacter M) := by
  have hdet : Continuous fun g : W.geometric ↦ LinearMap.det (ρ g) := by
    let b := Module.finBasis (PadicAlgCl l) V
    have h : Continuous fun g : W.geometric ↦ LinearMap.toMatrix b b (ρ g) :=
      continuous_pi fun i ↦ continuous_pi fun j ↦ hρ.continuous_toMatrix b i j
    simpa only [LinearMap.det_toMatrix] using h.matrix_det
  refine IsLisse.of_continuous_apply fun φ v ↦ ?_
  simp only [Representation.ofCharacter_apply, Representation.coe_detCharacter_apply, map_smul,
    smul_eq_mul]
  exact hdet.mul continuous_const

end Lisse

section Real

/-- The roots of `∏_{β ∈ M} (1 - β T)` are the inverses of the elements of `M`, if these are
nonzero. -/
theorem roots_prod_one_sub_C_mul_X {F : Type*} [Field F] {M : Multiset F} (hM : (0 : F) ∉ M) :
    ((M.map fun β ↦ 1 - Polynomial.C β * Polynomial.X).prod).roots = M.map (·⁻¹) := by
  have hfac (β : F) (hβ : β ≠ 0) : (1 - Polynomial.C β * Polynomial.X : Polynomial F) =
      Polynomial.C (-β) * (Polynomial.X - Polynomial.C β⁻¹) := by
    rw [mul_sub, ← Polynomial.C_mul, neg_mul, mul_inv_cancel₀ hβ]
    simp only [map_neg, map_one]
    ring
  rw [Polynomial.roots_multiset_prod]
  · rw [Multiset.bind_map]
    conv_rhs => rw [← Multiset.bind_singleton M (·⁻¹)]
    refine Multiset.bind_congr fun β hβ ↦ ?_
    have hβ : β ≠ 0 := fun h ↦ hM (h ▸ hβ)
    rw [hfac β hβ, Polynomial.roots_C_mul _ (neg_ne_zero.mpr hβ), Polynomial.roots_X_sub_C]
  · simp only [Multiset.mem_map, not_exists, not_and]
    intro β _ h
    simpa using congrArg (Polynomial.coeff · 0) h

/-- Mapping `∏_{β ∈ M} (1 - β T)` along a ring homomorphism `f` gives
`∏_{β ∈ M} (1 - f(β) T)`. -/
theorem map_prod_one_sub_C_mul_X {F F' : Type*} [Field F] [Field F'] (f : F →+* F')
    (M : Multiset F) :
    ((M.map fun β ↦ 1 - Polynomial.C β * Polynomial.X).prod).map f =
      ((M.map f).map fun β ↦ 1 - Polynomial.C β * Polynomial.X).prod := by
  rw [Polynomial.map_multiset_prod, Multiset.map_map, Multiset.map_map]
  congr 1
  exact Multiset.map_congr rfl fun β _ ↦ by simp

variable {V V' : Type u} [AddCommGroup V] [Module (PadicAlgCl l) V]
  [FiniteDimensional (PadicAlgCl l) V] [AddCommGroup V'] [Module (PadicAlgCl l) V']
  [FiniteDimensional (PadicAlgCl l) V'] {ρ : Representation (PadicAlgCl l) W.carrier V}
  (ι : PadicAlgCl l →+* ℂ)

/-- The local eigenvalues are nonzero, since the local Frobenius acts invertibly. -/
theorem zero_notMem_localEigenvalues (x : C.finitePoints) :
    (0 : PadicAlgCl l) ∉ W.localEigenvalues l ρ x := by
  intro h
  rw [localEigenvalues, Polynomial.mem_roots (LinearMap.charpoly_monic _).ne_zero,
    ← Module.End.hasEigenvalue_iff_isRoot_charpoly] at h
  obtain ⟨v, hv⟩ := h.exists_hasEigenvector
  have h0 : ρ (W.frobenius x) v = 0 := by rw [hv.apply_eq_smul, zero_smul]
  have : v = 0 := by
    have hv' : v = ρ (W.frobenius x)⁻¹ (ρ (W.frobenius x) v) := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [hv', h0, map_zero]
  exact hv.2 this

/-- The complex local polynomial `ι P_x(ρ, T)` is `∏ (1 - (ι α) T)` over the local eigenvalues
`α`. -/
theorem map_localPolynomial (x : C.finitePoints) :
    (W.localPolynomial l ρ x).map ι =
      (((W.localEigenvalues l ρ x).map ι).map
        fun β ↦ 1 - Polynomial.C β * Polynomial.X).prod := by
  rw [localPolynomial_eq_prod_localEigenvalues, map_prod_one_sub_C_mul_X]

/-- The complex local eigenvalues are nonzero. -/
theorem zero_notMem_map_localEigenvalues (x : C.finitePoints) :
    (0 : ℂ) ∉ (W.localEigenvalues l ρ x).map ι := by
  simp only [Multiset.mem_map, map_eq_zero, not_exists, not_and]
  rintro α hα rfl
  exact zero_notMem_localEigenvalues x hα

/-- Blueprint `sk-d-real-weights`: an `ι`-real representation has a conjugation-stable
multiset of complex local eigenvalues at every closed point. -/
theorem IsReal.map_conj_localEigenvalues (h : W.IsReal l ρ ι) (x : C.finitePoints) :
    ((W.localEigenvalues l ρ x).map ι).map (starRingEnd ℂ) =
      (W.localEigenvalues l ρ x).map ι := by
  set M := (W.localEigenvalues l ρ x).map ι
  have hM : (0 : ℂ) ∉ M := zero_notMem_map_localEigenvalues ι x
  have hM' : (0 : ℂ) ∉ M.map (starRingEnd ℂ) := by simpa using hM
  have h₁ : ((W.localPolynomial l ρ x).map ι).map (starRingEnd ℂ) =
      (W.localPolynomial l ρ x).map ι := by
    ext n
    simpa [Polynomial.coeff_map] using h x n
  rw [map_localPolynomial, map_prod_one_sub_C_mul_X] at h₁
  have := congrArg Polynomial.roots h₁
  rw [roots_prod_one_sub_C_mul_X hM', roots_prod_one_sub_C_mul_X hM] at this
  exact Multiset.map_injective inv_injective this

/-- Blueprint `sk-d-real-weights`: a representation whose multisets of complex local
eigenvalues are stable under complex conjugation is `ι`-real. -/
theorem isReal_of_map_conj_localEigenvalues
    (h : ∀ x, ((W.localEigenvalues l ρ x).map ι).map (starRingEnd ℂ) =
      (W.localEigenvalues l ρ x).map ι) :
    W.IsReal l ρ ι := by
  intro x n
  have h₁ : ((W.localPolynomial l ρ x).map ι).map (starRingEnd ℂ) =
      (W.localPolynomial l ρ x).map ι := by
    rw [map_localPolynomial, map_prod_one_sub_C_mul_X, h x]
  simpa [Polynomial.coeff_map] using congrArg (Polynomial.coeff · n) h₁

/-- Blueprint `sk-r-real-linear`: if the local characteristic polynomials of `σ` are those of an
`ι`-real representation `ρ`, then every exterior power of `σ` is `ι`-real: its local
eigenvalues are the products of the `s`-element sub-multisets of those of `ρ`, by
`LinearMap.charpoly_roots_exteriorPower`. -/
theorem IsReal.exteriorPower_of_charpoly_eq {σ : Representation (PadicAlgCl l) W.carrier V'}
    (hreal : W.IsReal l ρ ι)
    (h : ∀ x, (σ (W.frobenius x)).charpoly = (ρ (W.frobenius x)).charpoly) (s : ℕ) :
    W.IsReal l (σ.exteriorPower s) ι := by
  refine isReal_of_map_conj_localEigenvalues ι fun x ↦ ?_
  have hE : W.localEigenvalues l (σ.exteriorPower s) x =
      ((W.localEigenvalues l ρ x).powersetCard s).map Multiset.prod := by
    change (_root_.exteriorPower.map s (σ (W.frobenius x))).charpoly.roots = _
    rw [LinearMap.charpoly_roots_exteriorPower, h x]
    rfl
  have hmap (f : PadicAlgCl l →+* ℂ) (M : Multiset (PadicAlgCl l)) :
      ((M.powersetCard s).map Multiset.prod).map f =
        ((M.map f).powersetCard s).map Multiset.prod := by
    rw [Multiset.powersetCard_map, Multiset.map_map, Multiset.map_map]
    exact Multiset.map_congr rfl fun t _ ↦ map_multiset_prod f t
  have hconj (M : Multiset ℂ) :
      ((M.powersetCard s).map Multiset.prod).map (starRingEnd ℂ) =
        ((M.map (starRingEnd ℂ)).powersetCard s).map Multiset.prod := by
    rw [Multiset.powersetCard_map, Multiset.map_map, Multiset.map_map]
    exact Multiset.map_congr rfl fun t _ ↦ map_multiset_prod (starRingEnd ℂ) t
  rw [hE, hmap, hconj, hreal.map_conj_localEigenvalues ι x]

end Real

end WeilGroup

end AlgebraicGeometry
