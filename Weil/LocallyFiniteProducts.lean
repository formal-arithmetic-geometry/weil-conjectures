/-
Formalization of Chapter 3, Section 2 of `weil_conjectures_chapter3.tex`:
"Locally finite sums and products"
(`sec:weil-locally-finite-products`).

Every declaration below is annotated with the LaTeX label it formalizes.
Design notes:

* `Weil.PowerSeries.AgreeThrough N A B` is the relation `A ≡_N B` of the
  text (agreement of all coefficients through degree `N`).  Besides the
  declarations named in the text, small helper lemmas (`refl`, `symm`,
  `trans`, `mono`, `one_add`) are provided; the text uses these facts
  inline in its proofs.
* `Weil.TAdicallyLocallyFiniteFamily R I` is the record of the text: a
  component map `toFun : I → R⟦X⟧` with a positive-order certificate and an
  active-set finiteness certificate; the index type `I` is an explicit
  parameter.  The bundled two-part lemma
  `lemma:weil-series-agree-through-operations` is provided as the components
  `AgreeThrough.add` / `AgreeThrough.mul` plus the bundled conjunction
  `AgreeThrough.add_mul` under the name of the text.
* Scopes follow the text: the truncation/product layer needs only
  `[CommRing R]`; the logarithmic subchain uses
  `[CommRing R] [Algebra ℚ R] [IsAddTorsionFree R]`; the coefficient-subring
  layer is again generic.
-/
import Weil.FormalExpLog

open PowerSeries Nat

namespace Weil

noncomputable section

variable {R : Type*} [CommRing R] {I : Type*}

/-! ### Agreement through a degree (generic coefficient-ring scope) -/

/-- `def:weil-series-agree-through`.  `A ≡_N B`: the coefficients of `A` and
`B` agree in every degree `j ≤ N`. -/
def PowerSeries.AgreeThrough (N : ℕ) (A B : R⟦X⟧) : Prop :=
  ∀ j ≤ N, coeff j A = coeff j B

namespace PowerSeries.AgreeThrough

theorem refl (N : ℕ) (A : R⟦X⟧) : PowerSeries.AgreeThrough N A A :=
  fun _ _ => rfl

theorem symm {N : ℕ} {A B : R⟦X⟧} (h : PowerSeries.AgreeThrough N A B) :
    PowerSeries.AgreeThrough N B A :=
  fun j hj => (h j hj).symm

theorem trans {N : ℕ} {A B C : R⟦X⟧} (hAB : PowerSeries.AgreeThrough N A B)
    (hBC : PowerSeries.AgreeThrough N B C) : PowerSeries.AgreeThrough N A C :=
  fun j hj => (hAB j hj).trans (hBC j hj)

/-- Agreement through `N` restricts to agreement through any `M ≤ N`. -/
theorem mono {M N : ℕ} (hMN : M ≤ N) {A B : R⟦X⟧}
    (h : PowerSeries.AgreeThrough N A B) : PowerSeries.AgreeThrough M A B :=
  fun j hj => h j (hj.trans hMN)

/-- Additive half of `lemma:weil-series-agree-through-operations`. -/
theorem add {N : ℕ} {A A' B B' : R⟦X⟧}
    (hA : PowerSeries.AgreeThrough N A A') (hB : PowerSeries.AgreeThrough N B B') :
    PowerSeries.AgreeThrough N (A + B) (A' + B') := fun j hj => by
  rw [map_add, map_add, hA j hj, hB j hj]

/-- Multiplicative half of `lemma:weil-series-agree-through-operations`:
every pair in the antidiagonal of `j ≤ N` has both entries `≤ N`. -/
theorem mul {N : ℕ} {A A' B B' : R⟦X⟧}
    (hA : PowerSeries.AgreeThrough N A A') (hB : PowerSeries.AgreeThrough N B B') :
    PowerSeries.AgreeThrough N (A * B) (A' * B') := fun j hj => by
  rw [coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mem_antidiagonal] at hp
  rw [hA p.1 (by omega), hB p.2 (by omega)]

/-- `lemma:weil-series-agree-through-operations`, bundled as in the text. -/
theorem add_mul {N : ℕ} {A A' B B' : R⟦X⟧}
    (hA : PowerSeries.AgreeThrough N A A') (hB : PowerSeries.AgreeThrough N B B') :
    PowerSeries.AgreeThrough N (A + B) (A' + B') ∧
      PowerSeries.AgreeThrough N (A * B) (A' * B') :=
  ⟨hA.add hB, hA.mul hB⟩

/-- `lemma:weil-series-agree-through-sub`.  Agreement is preserved by
subtraction. -/
theorem sub {N : ℕ} {A A' B B' : R⟦X⟧}
    (hA : PowerSeries.AgreeThrough N A A') (hB : PowerSeries.AgreeThrough N B B') :
    PowerSeries.AgreeThrough N (A - B) (A' - B') := fun j hj => by
  rw [map_sub, map_sub, hA j hj, hB j hj]

/-- `lemma:weil-series-agree-through-pow`.  Agreement is preserved by natural
powers. -/
theorem pow {N : ℕ} {A B : R⟦X⟧} (h : PowerSeries.AgreeThrough N A B) (r : ℕ) :
    PowerSeries.AgreeThrough N (A ^ r) (B ^ r) := by
  induction r with
  | zero => simpa using refl N 1
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact ih.mul h

/-- `lemma:weil-series-agree-through-finset-product`.  Agreement is preserved
by finite products. -/
theorem finsetProd {N : ℕ} (S : Finset I) (A B : I → R⟦X⟧)
    (h : ∀ i ∈ S, PowerSeries.AgreeThrough N (A i) (B i)) :
    PowerSeries.AgreeThrough N (∏ i ∈ S, A i) (∏ i ∈ S, B i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using refl N 1
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- If `u ≡_N 0`, then `1 + u ≡_N 1`; the inline step used repeatedly in the
truncation-compatibility proofs of the text. -/
theorem one_add {N : ℕ} {u : R⟦X⟧} (h : PowerSeries.AgreeThrough N u 0) :
    PowerSeries.AgreeThrough N (1 + u) 1 := by
  simpa using (refl N (1 : R⟦X⟧)).add h

end PowerSeries.AgreeThrough

/-! ### `T`-adically locally finite families and their products -/

/-- `def:weil-t-adic-locally-finite-family`.  A family of positive-order
series indexed by `I`, finitely many of which are active (`≢_N 0`) at each
degree `N`.  The index type is an explicit parameter; both certificates are
structure fields. -/
structure TAdicallyLocallyFiniteFamily (R : Type*) [CommRing R] (I : Type*) where
  /-- The component map `u : I → R[[T]]`. -/
  toFun : I → R⟦X⟧
  /-- The positive-order certificate `h_pos`. -/
  constantCoeff_eq_zero : ∀ i, constantCoeff (toFun i) = 0
  /-- The active-set certificate `h_fin`: for each `N` the set
  `Act_N(u) = {i | u_i ≢_N 0}` is finite. -/
  finite_active : ∀ N : ℕ, {i : I | ¬ PowerSeries.AgreeThrough N (toFun i) 0}.Finite

namespace TAdicallyLocallyFiniteFamily

variable (u : TAdicallyLocallyFiniteFamily R I)

/-- `def:weil-active-index-finset`.  The active-index finset `A_N(u)`,
obtained from the finite set `Act_N(u)` by `Set.Finite.toFinset`. -/
def activeFinset (N : ℕ) : Finset I :=
  (u.finite_active N).toFinset

/-- `lemma:weil-active-index-finset-mem`.  Membership in the active-index
finset. -/
theorem mem_activeFinset {N : ℕ} {i : I} :
    i ∈ u.activeFinset N ↔ ¬ PowerSeries.AgreeThrough N (u.toFun i) 0 :=
  Set.Finite.mem_toFinset _

/-- `lemma:weil-active-index-finset-mono`.  Monotonicity of active-index
finsets. -/
theorem activeFinset_mono {M N : ℕ} (hMN : M ≤ N) :
    u.activeFinset M ⊆ u.activeFinset N := by
  intro i hi
  rw [mem_activeFinset] at hi ⊢
  exact fun h => hi (h.mono hMN)

/-- `def:weil-truncated-product`.  The finite product
`Π_N(u) = ∏_{i ∈ A_N(u)} (1 + u_i)` at truncation level `N`. -/
def truncatedProduct (N : ℕ) : R⟦X⟧ :=
  ∏ i ∈ u.activeFinset N, (1 + u.toFun i)

/-- Every truncated product is a finite product of factors with constant
coefficient one (inline step of the text's proofs). -/
theorem truncatedProduct_constantCoeff (N : ℕ) :
    constantCoeff (u.truncatedProduct N) = 1 := by
  rw [truncatedProduct, map_prod]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [map_add, map_one, u.constantCoeff_eq_zero, add_zero]

/-- `lemma:weil-truncated-products-compatible`.  Compatibility of finite
truncated products: if `M ≤ N`, then `Π_N(u) ≡_M Π_M(u)`. -/
theorem truncatedProduct_agree {M N : ℕ} (hMN : M ≤ N) :
    PowerSeries.AgreeThrough M (u.truncatedProduct N) (u.truncatedProduct M) := by
  classical
  have hsub := u.activeFinset_mono hMN
  have hsplit : u.truncatedProduct N =
      (∏ i ∈ u.activeFinset N \ u.activeFinset M, (1 + u.toFun i)) *
        u.truncatedProduct M := by
    rw [truncatedProduct, truncatedProduct, Finset.prod_sdiff hsub]
  rw [hsplit]
  have hdiff : PowerSeries.AgreeThrough M
      (∏ i ∈ u.activeFinset N \ u.activeFinset M, (1 + u.toFun i))
      (∏ _i ∈ u.activeFinset N \ u.activeFinset M, (1 : R⟦X⟧)) := by
    refine PowerSeries.AgreeThrough.finsetProd _ _ _ fun i hi => ?_
    rw [Finset.mem_sdiff] at hi
    refine PowerSeries.AgreeThrough.one_add ?_
    by_contra h
    exact hi.2 (u.mem_activeFinset.mpr h)
  simpa using hdiff.mul (PowerSeries.AgreeThrough.refl M (u.truncatedProduct M))

/-- `def:weil-locally-finite-product`.  The coefficientwise locally finite
product `∏^lf (1 + u_i)`, defined degreewise from the truncated products;
no inverse-limit object occurs. -/
def product : R⟦X⟧ :=
  PowerSeries.mk fun N => coeff N (u.truncatedProduct N)

/-- `lemma:weil-locally-finite-product-coeff`.  Coefficient formula for the
locally finite product. -/
theorem coeff_product (N : ℕ) :
    coeff N u.product = coeff N (u.truncatedProduct N) :=
  coeff_mk _ _

/-- `lemma:weil-locally-finite-product-constant`.  Constant coefficient of a
locally finite product. -/
theorem product_constantCoeff : constantCoeff u.product = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_product,
    coeff_zero_eq_constantCoeff_apply, truncatedProduct_constantCoeff]

/-- `lemma:weil-locally-finite-product-agree`.  The locally finite product
has the prescribed truncations. -/
theorem product_agree (N : ℕ) :
    PowerSeries.AgreeThrough N u.product (u.truncatedProduct N) := by
  intro j hj
  rw [coeff_product]
  exact ((u.truncatedProduct_agree hj) j le_rfl).symm

/-- `lemma:weil-truncated-product-agree-prescribed-finset`.  A prescribed
finite superset of the active finset gives the same truncation. -/
theorem truncatedProduct_agree_finset {N : ℕ} {S : Finset I}
    (hS : u.activeFinset N ⊆ S) :
    PowerSeries.AgreeThrough N (u.truncatedProduct N)
      (∏ i ∈ S, (1 + u.toFun i)) := by
  classical
  have hsplit : (∏ i ∈ S, (1 + u.toFun i)) =
      (∏ i ∈ S \ u.activeFinset N, (1 + u.toFun i)) * u.truncatedProduct N := by
    rw [truncatedProduct, Finset.prod_sdiff hS]
  rw [hsplit]
  have hdiff : PowerSeries.AgreeThrough N
      (∏ i ∈ S \ u.activeFinset N, (1 + u.toFun i))
      (∏ _i ∈ S \ u.activeFinset N, (1 : R⟦X⟧)) := by
    refine PowerSeries.AgreeThrough.finsetProd _ _ _ fun i hi => ?_
    rw [Finset.mem_sdiff] at hi
    refine PowerSeries.AgreeThrough.one_add ?_
    by_contra h
    exact hi.2 (u.mem_activeFinset.mpr h)
  have := hdiff.mul (PowerSeries.AgreeThrough.refl N (u.truncatedProduct N))
  refine PowerSeries.AgreeThrough.symm ?_
  simpa using this

/-- `lemma:weil-locally-finite-product-agree-prescribed-finset`.  A locally
finite product agrees with the finite product over any prescribed finite
superset of the active finset. -/
theorem product_agree_finset {N : ℕ} {S : Finset I}
    (hS : u.activeFinset N ⊆ S) :
    PowerSeries.AgreeThrough N u.product (∏ i ∈ S, (1 + u.toFun i)) :=
  (u.product_agree N).trans (u.truncatedProduct_agree_finset hS)

end TAdicallyLocallyFiniteFamily

/-! ### Rational logarithm scope

For the logarithmic subchain the parameters are
`[CommRing R] [Algebra ℚ R] [IsAddTorsionFree R]`, as prescribed by the
scope paragraph of the text; the linter for unused section variables is
silenced accordingly. -/

section RationalLogarithmScope

variable [Algebra ℚ R] [IsAddTorsionFree R]

set_option linter.unusedSectionVars false

/-- `lemma:weil-inactive-logarithm`.  An inactive factor has inactive
logarithm: if `u ≡_N 0` and `c(u) = 0`, then `Log(1 + u) ≡_N 0`. -/
theorem formalLog_agree_zero {u : R⟦X⟧} (hc : constantCoeff u = 0) {N : ℕ}
    (h : PowerSeries.AgreeThrough N u 0) :
    PowerSeries.AgreeThrough N (formalLog (1 + u)) 0 := by
  have hc1 : constantCoeff (1 + u) = 1 := by rw [map_add, map_one, hc, add_zero]
  intro j hj
  rcases Nat.eq_zero_or_pos j with rfl | hjpos
  · rw [coeff_zero_eq_constantCoeff_apply, formalLog_constantCoeff hc1, map_zero]
  · rw [formalLog_coeff hc1 (by omega), map_zero]
    refine Finset.sum_eq_zero fun r hr => ?_
    rw [Finset.mem_Icc] at hr
    have hzero : coeff j ((1 + u - 1) ^ r) = 0 := by
      rw [add_sub_cancel_left]
      have hcoeff := (h.pow r) j hj
      rwa [zero_pow (by omega : r ≠ 0), map_zero] at hcoeff
    rw [hzero, mul_zero]

/-- `lemma:weil-formal-log-agree-through`.  The formal logarithm respects
finite-degree agreement. -/
theorem formalLog_agreeThrough {A B : R⟦X⟧} (hA : constantCoeff A = 1)
    (hB : constantCoeff B = 1) {N : ℕ} (h : PowerSeries.AgreeThrough N A B) :
    PowerSeries.AgreeThrough N (formalLog A) (formalLog B) := by
  have hsub : PowerSeries.AgreeThrough N (A - 1) (B - 1) :=
    h.sub (PowerSeries.AgreeThrough.refl N 1)
  intro j hj
  rcases Nat.eq_zero_or_pos j with rfl | hjpos
  · rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply,
      formalLog_constantCoeff hA, formalLog_constantCoeff hB]
  · rw [formalLog_coeff hA (by omega), formalLog_coeff hB (by omega)]
    exact Finset.sum_congr rfl fun r _ => by rw [(hsub.pow r) j hj]

/-- `lemma:weil-formal-log-one`.  The formal logarithm of one is zero. -/
theorem formalLog_one : formalLog (1 : R⟦X⟧) = 0 := by
  ext N
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [coeff_zero_eq_constantCoeff_apply, formalLog_constantCoeff (map_one _), map_zero]
  · rw [formalLog_coeff (map_one _) (by omega), map_zero]
    refine Finset.sum_eq_zero fun r hr => ?_
    rw [Finset.mem_Icc] at hr
    rw [sub_self, zero_pow (by omega : r ≠ 0), map_zero, mul_zero]

/-- `lemma:weil-formal-log-finset-product`.  A finite product of normalized
one-series turns into a finite logarithm sum. -/
theorem formalLog_finsetProd (S : Finset I) (A : I → R⟦X⟧)
    (hA : ∀ i ∈ S, constantCoeff (A i) = 1) :
    formalLog (∏ i ∈ S, A i) = ∑ i ∈ S, formalLog (A i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [formalLog_one]
  | @insert a s ha ih =>
    have hprod : constantCoeff (∏ i ∈ s, A i) = 1 := by
      rw [map_prod]
      exact Finset.prod_eq_one fun i hi => hA i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      formalLog_mul (hA a (Finset.mem_insert_self a s)) hprod,
      ih fun i hi => hA i (Finset.mem_insert_of_mem hi)]

namespace TAdicallyLocallyFiniteFamily

variable (u : TAdicallyLocallyFiniteFamily R I)

/-- `def:weil-locally-finite-log-sum`.  The locally finite logarithm sum
`∑^lf Log(1 + u_i)`, defined degreewise over the active finsets. -/
def logSum : R⟦X⟧ :=
  PowerSeries.mk fun N => ∑ i ∈ u.activeFinset N, coeff N (formalLog (1 + u.toFun i))

/-- `lemma:weil-locally-finite-log-agree-truncation`.  The logarithm of the
locally finite product agrees with the logarithm of the active finite
truncation. -/
theorem log_agree_truncatedProduct (N : ℕ) :
    PowerSeries.AgreeThrough N (formalLog u.product)
      (formalLog (u.truncatedProduct N)) :=
  formalLog_agreeThrough u.product_constantCoeff
    (u.truncatedProduct_constantCoeff N) (u.product_agree N)

/-- `lemma:weil-truncated-log-coeff`.  The truncated logarithm has the
prescribed coefficient. -/
theorem coeff_log_truncatedProduct (N : ℕ) :
    coeff N (formalLog (u.truncatedProduct N)) = coeff N u.logSum := by
  rw [truncatedProduct,
    formalLog_finsetProd _ _ fun i _ => by
      rw [map_add, map_one, u.constantCoeff_eq_zero, add_zero],
    map_sum, logSum, coeff_mk]

/-- `lemma:weil-locally-finite-log-coeff`.  Coefficient formula for the
logarithm of a locally finite product. -/
theorem coeff_log_product (N : ℕ) :
    coeff N (formalLog u.product) = coeff N u.logSum := by
  rw [← u.coeff_log_truncatedProduct N]
  exact (u.log_agree_truncatedProduct N) N le_rfl

/-- `prop:weil-log-locally-finite-product`.  Logarithm of a locally finite
product: `Log(∏^lf (1 + u_i)) = ∑^lf Log(1 + u_i)`. -/
theorem log_product : formalLog u.product = u.logSum := by
  ext N
  exact u.coeff_log_product N

end TAdicallyLocallyFiniteFamily

end RationalLogarithmScope

/-! ### Coefficient subrings (generic coefficient-ring reset) -/

/-- `def:weil-power-series-over-subring`.  `A` has coefficients in the
subring `R₀` if every coefficient of `A` lies in `R₀`. -/
def PowerSeries.HasCoefficientsIn (A : R⟦X⟧) (R₀ : Subring R) : Prop :=
  ∀ n : ℕ, coeff n A ∈ R₀

namespace PowerSeries.HasCoefficientsIn

/-- The constant series one has coefficients in every subring (inline step
of the text's proofs). -/
theorem one {R₀ : Subring R} : PowerSeries.HasCoefficientsIn (1 : R⟦X⟧) R₀ := by
  intro n
  rw [coeff_one]
  split_ifs
  · exact R₀.one_mem
  · exact R₀.zero_mem

/-- `lemma:weil-power-series-over-subring-finset-product`.
Coefficient-subring membership is closed under finite products. -/
theorem finsetProd {R₀ : Subring R} (S : Finset I) (A : I → R⟦X⟧)
    (h : ∀ i ∈ S, PowerSeries.HasCoefficientsIn (A i) R₀) :
    PowerSeries.HasCoefficientsIn (∏ i ∈ S, A i) R₀ := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using one
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    intro n
    rw [coeff_mul]
    refine Subring.sum_mem _ fun p _ => Subring.mul_mem _
      (h a (Finset.mem_insert_self a s) p.1)
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)) p.2)

end PowerSeries.HasCoefficientsIn

/-- `lemma:weil-locally-finite-product-subring`.  A locally finite product
preserves a coefficient subring. -/
theorem TAdicallyLocallyFiniteFamily.product_mem_subring
    (u : TAdicallyLocallyFiniteFamily R I) {R₀ : Subring R}
    (h : ∀ i, PowerSeries.HasCoefficientsIn (u.toFun i) R₀) :
    PowerSeries.HasCoefficientsIn u.product R₀ := by
  intro N
  rw [u.coeff_product, truncatedProduct]
  refine PowerSeries.HasCoefficientsIn.finsetProd _ _ (fun i _ => ?_) N
  intro n
  rw [map_add]
  exact R₀.add_mem (PowerSeries.HasCoefficientsIn.one n) (h i n)

end

end Weil
