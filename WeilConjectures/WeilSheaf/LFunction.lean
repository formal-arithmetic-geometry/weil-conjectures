/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EulerProductAux
public import WeilConjectures.WeilSheaf.Cohomology
public import WeilConjectures.WeilSheaf.LocalFrobenius
public import WeilConjectures.WeilSheaf.StalkFunctor
public import WeilConjectures.ZetaFunction.TraceFormula
public import WeilConjectures.ZetaLinearAlgebra.CharpolyRevExpand
public import WeilConjectures.ZetaLinearAlgebra.DetTrace
public import WeilConjectures.ZetaLinearAlgebra.TraceDatum

/-!
# The Euler-product form of the trace formula for Weil complexes

Let `X₀` be a separated scheme of finite type over the finite field `k₀`, `X = X₀ ⊗ k̄` and `K`
a Weil complex on `X₀`. For a closed point `x` of degree `e_x` the local factor of the
`L`-function of `K` at `x` is the inverse of the alternating determinant

`det (1 - T ^ {e_x} F_x ∣ K_x̄) = ∏_j det (1 - T ^ {e_x} F_x ∣ 𝓗ʲ(K)_x̄) ^ ((-1) ^ j)`

(`LinearMap.alternatingCharpolyRevProd`), and the Euler-product form of the
Grothendieck–Lefschetz trace formula says

`L (X₀, K, T) = ∏_x det (1 - T ^ {e_x} F_x ∣ K_x̄)⁻¹`
`  = ∏_i det (1 - T F ∣ H_cⁱ(X, K)) ^ ((-1) ^ (i + 1))`

in `1 + T ℚ̄_ℓ⟦T⟧`, the product over the closed points being locally finite for the `T`-adic
topology (`AlgebraicGeometry.WeilComplex.coeff_prod_inv_alternatingCharpolyRevProd_stalk`).
For a Weil sheaf placed in degree zero, the stalk cohomology is the stalk itself
(`AlgebraicGeometry.WeilSheaf.coeff_prod_inv_localPolynomial_stalk`).

## Main statements

- `AlgebraicGeometry.WeilComplex.coeff_prod_inv_alternatingCharpolyRevProd_stalk`
  (`thm-trf-l-function-euler-product`): the Euler-product form of the trace formula.
- `AlgebraicGeometry.WeilSheaf.coeff_prod_inv_localPolynomial_stalk`: its form for a Weil
  sheaf.

## Implementation notes

*Local finiteness.* The `L`-function is an infinite product over the closed points. Instead of
choosing a topology on `ℚ̄_ℓ⟦T⟧` in which it converges, the statement is coefficientwise: the
coefficient of `T ^ n` of the finite product over any finite set of closed points containing
all points of degree at most `n` is the coefficient of `T ^ n` of the cohomological side. This
is the `T`-adic local finiteness of item (1) of the blueprint theorem, together with item (2).
Item (3), the curve case, is obtained from it with the vanishing of `H_cⁱ` outside `[0, 2]`,
and item (4), the transport along `ι : ℚ̄_ℓ → ℂ`, by applying `ι` coefficientwise.

*Degrees.* The finite products over the cohomological degrees run over finite sets `S` and `T`
of integers outside of which the compactly supported cohomology, respectively the cohomology
sheaves, vanish; such sets exist by finiteness
(`AlgebraicGeometry.WeilComplex.exists_subsingleton_compactlySupportedCohomology` and
`AlgebraicGeometry.WeilComplex.exists_finset_isZero_homologySheaf`), and enlarging them does
not change the alternating determinants, the added factors being `1`.

*Hypotheses.* The blueprint theorem is stated for a Weil complex satisfying the finite-level
hypotheses of `thm-trf-trace-formula-e` (étale-origin witnesses and compactification
admissibility for the reductions of a lattice of a representative). The Weil complexes of this
repository are constructible `ℚ̄_ℓ`-complexes on the pro-étale site of `X`, built directly from
pro-étale sheaves with no chosen lattice; those hypotheses are properties of the integral
models used in the proof, and are not part of the statement.
-/

@[expose] public section

universe u

open CategoryTheory Limits PowerSeries

namespace PowerSeries

/-- The logarithmic derivative of the inverse: if `X f' = a f` and `f` is invertible, then
`X (f⁻¹)' = -a f⁻¹`. -/
theorem X_mul_derivative_inv {K : Type*} [Field K] {f a : K⟦X⟧} (hf : constantCoeff f ≠ 0)
    (h : X * derivative K f = a * f) : X * derivative K f⁻¹ = -a * f⁻¹ := by
  rw [derivative_inv']
  linear_combination (-(f⁻¹ ^ 2)) * h - (a * f⁻¹) * PowerSeries.mul_inv_cancel f hf

end PowerSeries

namespace LinearMap

variable {K : Type*} [Field K]

/-- The expansion `det (1 - Tᵉ F)`, `e ≠ 0`, has constant coefficient `1`. -/
theorem constantCoeff_charpolyRev_comp_X_pow {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (F : Module.End K V) {e : ℕ} (he : e ≠ 0) :
    constantCoeff ((F.charpolyRev.comp (Polynomial.X ^ e) : Polynomial K) : K⟦X⟧) = 1 := by
  rw [Polynomial.constantCoeff_coe, Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_comp,
    Polynomial.eval_pow, Polynomial.eval_X, zero_pow he, eval_charpolyRev]

variable {W : ℤ → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
  [∀ i, FiniteDimensional K (W i)]

/-- The alternating determinant `∏ᵢ det (1 - Tᵉ uᵢ)^{(-1)^i}`, `e ≠ 0`, has constant
coefficient `1`. -/
theorem constantCoeff_alternatingCharpolyRevProd (s : Finset ℤ) (u : ∀ i, Module.End K (W i))
    {e : ℕ} (he : e ≠ 0) : constantCoeff (alternatingCharpolyRevProd s u e) = 1 := by
  rw [alternatingCharpolyRevProd, map_prod]
  refine Finset.prod_eq_one fun i _ ↦ ?_
  split_ifs
  · exact constantCoeff_charpolyRev_comp_X_pow (u i) he
  · rw [PowerSeries.constantCoeff_inv, constantCoeff_charpolyRev_comp_X_pow (u i) he, inv_one]

/-- The logarithmic derivative of the alternating determinant `∏ᵢ det (1 - Tᵉ uᵢ)^{(-1)^i}`,
`e ≠ 0`: it is minus the generating series of `e ∑ᵢ (-1)ⁱ tr (uᵢ^{m / e})`, `e ∣ m`, `m ≥ 1`. -/
theorem X_mul_derivative_alternatingCharpolyRevProd (s : Finset ℤ)
    (u : ∀ i, Module.End K (W i)) {e : ℕ} (he : e ≠ 0) :
    X * derivative K (alternatingCharpolyRevProd s u e) =
      (-PowerSeries.mk fun m ↦ if m ≠ 0 ∧ e ∣ m then
        (e : K) * ∑ i ∈ s, (i.negOnePow : ℤ) • trace K (W i) (u i ^ (m / e)) else 0) *
        alternatingCharpolyRevProd s u e := by
  set H : ℤ → K⟦X⟧ := fun i ↦ PowerSeries.mk fun m ↦
    if m ≠ 0 ∧ e ∣ m then (e : K) * trace K (W i) (u i ^ (m / e)) else 0 with hH
  have hP (i : ℤ) : (((u i).charpolyRev.comp (Polynomial.X ^ e) : Polynomial K) : K⟦X⟧) =
      PowerSeries.expand e he ((u i).charpolyRev : K⟦X⟧) := by
    rw [← Polynomial.expand_eq_comp_X_pow, coe_expand]
  have hf : ∀ i ∈ s, X * derivative K
      (if Even i then (((u i).charpolyRev.comp (Polynomial.X ^ e) : Polynomial K) : K⟦X⟧)
      else (((u i).charpolyRev.comp (Polynomial.X ^ e) : Polynomial K) : K⟦X⟧)⁻¹) =
      (-((i.negOnePow : ℤ) • H i)) *
      (if Even i then (((u i).charpolyRev.comp (Polynomial.X ^ e) : Polynomial K) : K⟦X⟧)
      else (((u i).charpolyRev.comp (Polynomial.X ^ e) : Polynomial K) : K⟦X⟧)⁻¹) := by
    intro i _
    have h1 := constantCoeff_charpolyRev_comp_X_pow (u i) he
    rw [hP] at h1 ⊢
    split_ifs with h
    · rw [Int.negOnePow_even _ h, Units.val_one, one_smul]
      exact X_mul_derivative_expand_charpolyRev (u i) e he
    · rw [Int.negOnePow_odd _ (Int.not_even_iff_odd.1 h), Units.val_neg, Units.val_one,
        neg_smul, one_smul]
      exact PowerSeries.X_mul_derivative_inv (ne_of_eq_of_ne h1 one_ne_zero)
        (X_mul_derivative_expand_charpolyRev (u i) e he)
  rw [alternatingCharpolyRevProd, PowerSeries.X_mul_derivative_prod s hf, Finset.sum_neg_distrib]
  congr 2
  ext m
  rw [map_sum, PowerSeries.coeff_mk]
  split_ifs with hm
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [hH, map_zsmul, PowerSeries.coeff_mk, if_pos hm, mul_smul_comm]
  · refine Finset.sum_eq_zero fun i _ ↦ ?_
    simp only [hH, map_zsmul, PowerSeries.coeff_mk, if_neg hm, smul_zero]

end LinearMap

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

namespace WeilSheaf

/-- The linear isomorphism induced by an isomorphism of Weil sheaves on the stalks at a geometric
point. -/
noncomputable def stalkAtLinEquivOfIso {F G : WeilSheaf k₀ l X} (e : F ≅ G)
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (m : ℕ) (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).hom =
      (specGeometricFrobenius k₀ ^ m).hom ≫ s) :
    (F.stalkAt s m hs).carrier ≃ₗ[PadicAlgCl l] (G.stalkAt s m hs).carrier :=
  LinearEquiv.ofLinearMap (stalkAtMap s m hs e.hom) (stalkAtMap s m hs e.inv)
    (LinearMap.ext fun y ↦ (stalkAtMap_comp s m hs e.inv e.hom y).symm.trans <| by
      rw [e.inv_hom_id]
      exact stalkAtMap_id s m hs G y)
    (LinearMap.ext fun y ↦ (stalkAtMap_comp s m hs e.hom e.inv y).symm.trans <| by
      rw [e.hom_inv_id]
      exact stalkAtMap_id s m hs F y)

theorem stalkAtLinEquivOfIso_apply {F G : WeilSheaf k₀ l X} (e : F ≅ G)
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (m : ℕ) (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).hom =
      (specGeometricFrobenius k₀ ^ m).hom ≫ s) (v) :
    stalkAtLinEquivOfIso e s m hs v = stalkAtMap s m hs e.hom v :=
  rfl

/-- The linear isomorphism `AlgebraicGeometry.WeilSheaf.stalkAtLinEquivOfIso` commutes with the
Frobenius. -/
theorem stalkAtLinEquivOfIso_frobenius {F G : WeilSheaf k₀ l X} (e : F ≅ G)
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (m : ℕ) (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).hom =
      (specGeometricFrobenius k₀ ^ m).hom ≫ s) (v : (F.stalkAt s m hs).carrier) :
    stalkAtLinEquivOfIso e s m hs ((F.stalkAt s m hs).frobenius v) =
      (G.stalkAt s m hs).frobenius (stalkAtLinEquivOfIso e s m hs v) := by
  rw [stalkAtLinEquivOfIso_apply, stalkAtLinEquivOfIso_apply]
  exact stalkAtMap_frobenius s m hs e.hom v

/-- An isomorphism of Weil sheaves induces an isomorphism of the stalks at a geometric point,
compatible with the Frobenius. -/
noncomputable def stalkAtEquivOfIso {F G : WeilSheaf k₀ l X} (e : F ≅ G)
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (m : ℕ) (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).hom =
      (specGeometricFrobenius k₀ ^ m).hom ≫ s) :
    (F.stalkAt s m hs).Equiv (G.stalkAt s m hs) :=
  ⟨stalkAtLinEquivOfIso e s m hs, stalkAtLinEquivOfIso_frobenius e s m hs⟩

/-- An isomorphism of Weil sheaves induces an isomorphism of the geometric stalks at a closed
point, compatible with the local Frobenius. -/
noncomputable def stalkEquivOfIso {F G : WeilSheaf k₀ l X} (e : F ≅ G) (x : X.finitePoints) :
    (F.stalk x).Equiv (G.stalk x) :=
  stalkAtEquivOfIso e _ _ _

/-- Isomorphic Weil sheaves have the same characteristic polynomial of the local Frobenius at a
closed point. -/
theorem charpoly_frobeniusEnd_stalk_of_iso {F G : WeilSheaf k₀ l X} (e : F ≅ G)
    (x : X.finitePoints) :
    (F.stalk x).frobeniusEnd.charpoly = (G.stalk x).frobeniusEnd.charpoly :=
  ((stalkEquivOfIso e x).charpoly_frobeniusEnd).symm

/-- The stalks of a zero Weil sheaf are zero. -/
theorem subsingleton_stalk_of_isZero {F : WeilSheaf k₀ l X} (hF : IsZero F)
    (x : X.finitePoints) : Subsingleton (F.stalk x).carrier :=
  ModuleCat.subsingleton_of_isZero ((WeilCoefficients.toModuleCat l).map_isZero
    ((stalkFunctor k₀ l (Scheme.Hom.geometricFiberPointOfFinitePoint _ x)).map_isZero hF))

end WeilSheaf

variable [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

namespace WeilComplex

/-- Blueprint `thm-trf-l-function-euler-product`: Euler-product form of the trace formula.

Let `X₀` be a separated scheme of finite type over `k₀ = 𝔽_q` and `K` a Weil complex on `X₀`
with coefficients in `ℚ̄_ℓ`, `ℓ ≠ p`. Write `F` for the global geometric Frobenius on
`H_cⁱ(X, K)` and, for a closed point `x` of degree `e_x`, `F_x` for the local Frobenius on the
stalks `𝓗ʲ(K)_x̄`. Then

`L (X₀, K, T) = ∏_x det (1 - T ^ {e_x} F_x ∣ K_x̄)⁻¹`
`  = ∏_i det (1 - T F ∣ H_cⁱ(X, K)) ^ ((-1) ^ (i + 1))`

as formal power series over `ℚ̄_ℓ`, the product over the closed points being locally finite:
for every `n`, the coefficient of `T ^ n` of the finite product over any finite set `s` of
closed points containing those of degree at most `n` is the coefficient of `T ^ n` of the
right-hand side. Here `S` and `T` are finite sets of degrees outside of which `H_cⁱ(X, K)`,
respectively the cohomology sheaves `𝓗ʲ(K)`, vanish. This is assertion (2) of the blueprint
node, for `Λ = ℚ̄_ℓ`, with the local finiteness of assertion (1). -/
theorem coeff_prod_inv_alternatingCharpolyRevProd_stalk (K : WeilComplex k₀ l X)
    {S T : Finset ℤ}
    (hS : ∀ i ∉ S, Subsingleton (WeilComplex.compactlySupportedCohomology K i).carrier)
    (hT : ∀ j ∉ T, IsZero ((homologySheaf j).obj K)) (n : ℕ) (s : Finset X.finitePoints)
    (hs : ∀ x : X.finitePoints, (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1 ≤ n → x ∈ s) :
    coeff n (∏ x ∈ s, (LinearMap.alternatingCharpolyRevProd T
        (fun j ↦ (WeilComplex.stalk K j x).frobeniusEnd)
          ((X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1))⁻¹) =
      coeff n (LinearMap.alternatingCharpolyRevProd S
        (fun i ↦ (WeilComplex.compactlySupportedCohomology K i).frobeniusEnd) 1)⁻¹ := by
  classical
  have hd (x : X.finitePoints) : (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1 ≠ 0 :=
    (X ↘ Spec (CommRingCat.of k₀)).degreeOver_ne_zero x.2
  have hL := PowerSeries.X_mul_derivative_prod s fun x _ ↦ PowerSeries.X_mul_derivative_inv
    (ne_of_eq_of_ne (LinearMap.constantCoeff_alternatingCharpolyRevProd _ _ (hd x)) one_ne_zero)
    (LinearMap.X_mul_derivative_alternatingCharpolyRevProd T
      (fun j ↦ (WeilComplex.stalk K j x).frobeniusEnd) (hd x))
  have hR := PowerSeries.X_mul_derivative_inv
    (ne_of_eq_of_ne (LinearMap.constantCoeff_alternatingCharpolyRevProd _ _ one_ne_zero)
      one_ne_zero)
    (LinearMap.X_mul_derivative_alternatingCharpolyRevProd S
      (fun i ↦ (WeilComplex.compactlySupportedCohomology K i).frobeniusEnd) one_ne_zero)
  refine PowerSeries.coeff_eq_of_X_mul_derivative_eq hL hR ?_ ?_ (m := n) ?_ n le_rfl
  · rw [map_prod, PowerSeries.constantCoeff_inv,
      LinearMap.constantCoeff_alternatingCharpolyRevProd _ _ one_ne_zero, inv_one]
    refine Finset.prod_eq_one fun x _ ↦ ?_
    rw [PowerSeries.constantCoeff_inv,
      LinearMap.constantCoeff_alternatingCharpolyRevProd _ _ (hd x), inv_one]
  · simp
  · intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simp
    have hsupp : (Function.support fun j : ℤ ↦ (j.negOnePow : ℤ) •
        LinearMap.trace (PadicAlgCl l) _
          ((WeilComplex.compactlySupportedCohomology K j).frobeniusEnd ^ i)) ⊆ S := by
      intro j hj
      by_contra h
      have := hS j h
      have h0 : (WeilComplex.compactlySupportedCohomology K j).frobeniusEnd ^ i = 0 :=
        LinearMap.ext fun _ ↦ Subsingleton.elim _ _
      rw [Function.mem_support, h0, map_zero, smul_zero] at hj
      exact hj rfl
    have htr := K.finsum_trace_compactlySupportedCohomology_eq hi0
    rw [finsum_eq_sum_of_support_subset _ hsupp,
      (X ↘ Spec (CommRingCat.of k₀)).finsum_fieldPoints_eq_sum hi0.ne' _
        (fun x ↦ ∑ j ∈ T, (j.negOnePow : ℤ) • LinearMap.trace (PadicAlgCl l) _
          ((WeilComplex.stalk K j x).frobeniusEnd ^
            (i / (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1)))
        (fun y x hx ↦ by
          rw [K.traceFunction_eq_sum T hT]
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          rw [WeilSheaf.traceFunction_eq_trace_frobeniusEnd_stalk_pow _ i y x hx]
          rfl)
        (fun x hx ↦ hs x ((Nat.le_of_dvd hi0 hx).trans hi))] at htr
    simp only [neg_neg, map_sum, PowerSeries.coeff_mk]
    rw [if_pos ⟨hi0.ne', one_dvd i⟩, Nat.cast_one, one_mul, Nat.div_one, htr, Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    simp [hi0.ne', nsmul_eq_mul]

end WeilComplex

namespace WeilSheaf

/-- The Euler-product form of the trace formula for a Weil sheaf `F` placed in degree zero:
for every `n` and every finite set `s` of closed points containing those of degree at most `n`,

`coeff_n ∏_{x ∈ s} det (1 - T ^ {e_x} F_x ∣ F_x̄)⁻¹`
`  = coeff_n ∏_i det (1 - T F ∣ H_cⁱ(X, F)) ^ ((-1) ^ (i + 1))`,

for a finite set `S` of degrees outside of which `H_cⁱ(X, F)` vanishes. This is
`AlgebraicGeometry.WeilComplex.coeff_prod_inv_alternatingCharpolyRevProd_stalk` for the Weil
complex `F[0]`, whose only cohomology sheaf is `𝓗⁰ = F`. -/
theorem coeff_prod_inv_localPolynomial_stalk (F : WeilSheaf k₀ l X) {S : Finset ℤ}
    (hS : ∀ i ∉ S, Subsingleton (F.compactlySupportedCohomology i).carrier) (n : ℕ)
    (s : Finset X.finitePoints)
    (hs : ∀ x : X.finitePoints, (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1 ≤ n → x ∈ s) :
    coeff n (∏ x ∈ s, (((F.stalk x).localPolynomial.comp
        (Polynomial.X ^ (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1) : Polynomial _) :
          (PadicAlgCl l)⟦X⟧)⁻¹) =
      coeff n (LinearMap.alternatingCharpolyRevProd S
        (fun i ↦ (F.compactlySupportedCohomology i).frobeniusEnd) 1)⁻¹ := by
  have h := WeilComplex.coeff_prod_inv_alternatingCharpolyRevProd_stalk (toComplex.obj F)
    (T := {0}) hS
    (fun j hj ↦ WeilComplex.isZero_homologySheaf_singleComplex (Finset.notMem_singleton.1 hj) F)
    n s hs
  refine Eq.trans (congrArg (coeff n) (Finset.prod_congr rfl fun x _ ↦ ?_)) h
  refine congrArg Inv.inv ?_
  rw [LinearMap.alternatingCharpolyRevProd, Finset.prod_singleton, if_pos Even.zero,
    FrobeniusModule.localPolynomial, LinearMap.charpolyRev, LinearMap.charpolyRev]
  have h2 : (WeilComplex.stalk (toComplex.obj F) 0 x).frobeniusEnd.charpoly =
      (F.stalk x).frobeniusEnd.charpoly :=
    charpoly_frobeniusEnd_stalk_of_iso
      ((toComplexCompHomologySheafIso (k₀ := k₀) (l := l) (X := X)).app F) x
  rw [h2]

end WeilSheaf

end AlgebraicGeometry
