module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.Filtration

/-!
# Comparison with the formal graph of an étale closed subscheme

Source: Stacks Project, More on Morphisms, Tags 04FF and 02HG; coefficientwise
assembly in the owning node (blueprint: lem-trf-etale-graph-taylor-comparison).
-/

@[expose] public section

set_option autoImplicit false

universe u v w x

open AlgebraicGeometry

namespace MvPowerSeries

/-- The formal graph vector is the expansion of the transverse coordinates minus
its constant value. This is actual power-series data, with no choice of a lift.
Source: Stacks Project, Tags 04FF and 02HG, graph comparison construction in the node
(blueprint: lem-trf-etale-graph-taylor-comparison). -/
noncomputable def etaleGraphVector {k : Type u} {D : Type v} {L : Type w}
    [Field k] [CommRing D] [Field L] [Algebra k D] [Algebra k L]
    {m r : ℕ} (ε : D →ₐ[k] L) (σ : D →ₐ[k] MvPowerSeries (Fin m) L)
    (y : Fin r → D) : Fin r → MvPowerSeries (Fin m) L :=
  fun j ↦ σ (y j) - C (ε (y j))

/-- Localization at the prime defined by a field-valued evaluation. The prime proof is
Mathlib's `RingHom.ker_isPrime`, so this imposes no extra hypothesis on the evaluation.
Source: Stacks Project, Tags 04FF and 02HG, localization clause of the graph comparison
(blueprint: lem-trf-etale-graph-taylor-comparison). -/
abbrev evaluationLocalization {A : Type v} {L : Type w} [CommRing A] [Field L]
    (ev : A →+* L) :=
  @Localization.AtPrime A _ (RingHom.ker ev) (RingHom.ker_isPrime ev)

-- Mathlib packages the unique-lifting induction; Krull intersection supplies separation.
private theorem unramified_powerSeries_ext {P : Type*} {B : Type*} {F : Type*}
    [CommRing P] [CommRing B] [Field F] {n : ℕ} (e : P →+* B)
    (he : e.FormallyUnramified) (f g : B →+* MvPowerSeries (Fin n) F)
    (hb : f.comp e = g.comp e) (h₀ : ∀ b, constantCoeff (f b) = constantCoeff (g b)) :
    f = g := by
  let := e.toAlgebra
  let := (f.comp e).toAlgebra
  let : Algebra.FormallyUnramified P B := he
  let f' : B →ₐ[P] MvPowerSeries (Fin n) F :=
    { f with commutes' := fun _ ↦ rfl }
  let g' : B →ₐ[P] MvPowerSeries (Fin n) F :=
    { g with commutes' := fun a ↦ (RingHom.congr_fun hb a).symm }
  have hsep : ⨅ i : ℕ, (RingHom.ker (constantCoeff (σ := Fin n) (R := F))) ^ i = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing _ (RingHom.ker_isPrime _).ne_top
  have hh : f' = g' := Algebra.FormallyUnramified.ext_of_iInf _ hsep (fun b ↦ by
    rw [Ideal.Quotient.eq, RingHom.mem_ker, map_sub, sub_eq_zero]
    exact h₀ b)
  exact congrArg AlgHom.toRingHom hh

private theorem coordinate_powerSeries_ext {k : Type*} {B : Type*} {F : Type*}
    {ι : Type*} [Field k] [CommRing B] [Field F] [Algebra k B] [Algebra k F]
    {n : ℕ} (z : ι → B)
    (he : (MvPolynomial.aeval z : MvPolynomial ι k →ₐ[k] B).toRingHom.Etale)
    (f g : B →ₐ[k] MvPowerSeries (Fin n) F)
    (hz : ∀ i, f (z i) = g (z i))
    (h₀ : ∀ b, constantCoeff (f b) = constantCoeff (g b)) : f = g := by
  apply AlgHom.coe_ringHom_injective
  apply unramified_powerSeries_ext _ he.formallyUnramified _ _ _ h₀
  have hh : f.comp (MvPolynomial.aeval z) = g.comp (MvPolynomial.aeval z) := by
    apply MvPolynomial.algHom_ext
    intro i
    simpa using hz i
  exact congrArg AlgHom.toRingHom hh

private theorem graph_hasSubst {F : Type*} [CommRing F] {m r : ℕ}
    {ψ : Fin r → MvPowerSeries (Fin m) F} (hψ : ∀ j, constantCoeff (ψ j) = 0) :
    HasSubst (Fin.addCases X ψ) := by
  apply hasSubst_of_constantCoeff_zero
  intro i
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
  · simp
  · simpa using hψ j

private theorem graph_constantCoeff {F : Type*} [CommRing F] {m r : ℕ}
    {ψ : Fin r → MvPowerSeries (Fin m) F} (hψ : ∀ j, constantCoeff (ψ j) = 0)
    (f : MvPowerSeries (Fin (m + r)) F) :
    constantCoeff (subst (Fin.addCases X ψ) f) = constantCoeff f := by
  have hs := graph_hasSubst hψ
  have hz : ∀ i, constantCoeff (Fin.addCases X ψ i) = 0 := by
    intro i
    exact Fin.addCases (fun j ↦ by simp) (fun j ↦ by simpa using hψ j) i
  have hh := constantCoeff_subst_eq_zero hs hz
    (f := f - C (constantCoeff f)) (by simp)
  simpa [subst_sub hs, subst_C, sub_eq_zero] using hh

private theorem graph_core {k : Type u} {A : Type v} {L : Type w}
    [Field k] [CommRing A] [Field L] [Algebra k A] [Algebra k L]
    {m r s : ℕ} (w : Fin m → A) (y : Fin r → A) (h : Fin s → A)
    (hA : (MvPolynomial.aeval (Fin.addCases w y) :
      MvPolynomial (Fin (m + r)) k →ₐ[k] A).toRingHom.Etale)
    (hD : (MvPolynomial.aeval
      (fun i ↦ (Ideal.Quotient.mkₐ k (Ideal.span (Set.range h))) (w i)) :
      MvPolynomial (Fin m) k →ₐ[k] (A ⧸ Ideal.span (Set.range h))).toRingHom.Etale)
    (ε : (A ⧸ Ideal.span (Set.range h)) →ₐ[k] L)
    (τ : A →ₐ[k] MvPowerSeries (Fin (m + r)) L)
    (σ : (A ⧸ Ideal.span (Set.range h)) →ₐ[k] MvPowerSeries (Fin m) L)
    (hτ₀ : ∀ a, constantCoeff (τ a) = ε ((Ideal.Quotient.mkₐ k (Ideal.span (Set.range h))) a))
    (hσ₀ : ∀ d, constantCoeff (σ d) = ε d)
    (hτw : ∀ i, τ (w i) = C (ε ((Ideal.Quotient.mkₐ k (Ideal.span (Set.range h))) (w i))) + X
      (Fin.castAdd r i))
    (hτy : ∀ j, τ (y j) = C (ε ((Ideal.Quotient.mkₐ k (Ideal.span (Set.range h))) (y j))) + X
      (Fin.natAdd m j))
    (hσw : ∀ i, σ ((Ideal.Quotient.mkₐ k (Ideal.span (Set.range h))) (w i)) = C (ε
      ((Ideal.Quotient.mkₐ k (Ideal.span (Set.range h))) (w i))) + X i) :
    let q := Ideal.Quotient.mkₐ k (Ideal.span (Set.range h))
    let φ := etaleGraphVector ε σ (fun j ↦ q (y j))
    (∀ j, constantCoeff (φ j) = 0) ∧
    (∀ a, subst (Fin.addCases X φ) (τ a) = σ (q a)) ∧
    (∀ i, subst (Fin.addCases X φ) (τ (h i)) = 0) ∧
    (∀ ψ : Fin r → MvPowerSeries (Fin m) L,
      (∀ j, constantCoeff (ψ j) = 0) →
      (∀ i, subst (Fin.addCases X ψ) (τ (h i)) = 0) → ψ = φ) := by
  let q := Ideal.Quotient.mkₐ k (Ideal.span (Set.range h))
  let φ := etaleGraphVector ε σ (fun j ↦ q (y j))
  have hφ₀ : ∀ j, constantCoeff (φ j) = 0 := by
    intro j
    simp [φ, etaleGraphVector, hσ₀]
  have hs := graph_hasSubst hφ₀
  let S : MvPowerSeries (Fin (m + r)) L →ₐ[k] MvPowerSeries (Fin m) L :=
    (substAlgHom (R := L) hs).restrictScalars k
  have hS (f : MvPowerSeries (Fin (m + r)) L) :
      S f = subst (Fin.addCases X φ) f := substAlgHom_apply hs f
  have hcomp : S.comp τ = σ.comp q := by
    refine coordinate_powerSeries_ext (k := k) (B := A) (F := L) (n := m)
      (ι := Fin (m + r)) (Fin.addCases w y) (by exact hA) (S.comp τ) (σ.comp q) ?_ ?_
    · simp only [AlgHom.comp_apply, hS]
      intro i
      refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
      · simp only [Fin.addCases_left]
        rw [hτw, subst_add hs, subst_C, subst_X hs]
        simpa only [q, Fin.addCases_left] using (hσw j).symm
      · simp only [Fin.addCases_right]
        rw [hτy, subst_add hs, subst_C, subst_X hs]
        simp [φ, etaleGraphVector, q]
    · simp only [AlgHom.comp_apply, hS]
      intro a
      rw [graph_constantCoeff hφ₀, hτ₀, hσ₀]
  have hq : ∀ i, q (h i) = 0 := by
    intro i
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
  have hc (a : A) : subst (Fin.addCases X φ) (τ a) = σ (q a) := by
    simpa only [AlgHom.comp_apply, hS] using AlgHom.congr_fun hcomp a
  refine ⟨hφ₀, hc, ?_, ?_⟩
  · intro i
    rw [hc, hq, map_zero]
  · intro ψ hψ₀ hψ
    have hsψ := graph_hasSubst hψ₀
    let T : A →ₐ[k] MvPowerSeries (Fin m) L :=
      ((substAlgHom (R := L) hsψ).restrictScalars k).comp τ
    have hT (a : A) : T a = subst (Fin.addCases X ψ) (τ a) :=
      substAlgHom_apply hsψ (τ a)
    have hI : Ideal.span (Set.range h) ≤ RingHom.ker T.toRingHom := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      change T (h i) = 0
      rw [hT]
      exact hψ i
    let ρ := Ideal.Quotient.liftₐ (Ideal.span (Set.range h)) T (fun a ha ↦ hI ha)
    have hρ (a : A) : ρ (q a) = subst (Fin.addCases X ψ) (τ a) := by
      simpa only [AlgHom.comp_apply, hT] using
        AlgHom.congr_fun (Ideal.Quotient.liftₐ_comp _ T (fun a ha ↦ hI ha)) a
    have hρσ : ρ = σ := by
      refine coordinate_powerSeries_ext (k := k) (F := L) (n := m)
        (fun i ↦ q (w i)) hD ρ σ ?_ ?_
      · intro i
        rw [hρ, hτw, subst_add hsψ, subst_C, subst_X hsψ]
        simpa only [q, Fin.addCases_left] using (hσw i).symm
      · intro d
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mkₐ_surjective k (Ideal.span (Set.range h)) d
        rw [hρ, graph_constantCoeff hψ₀, hτ₀, hσ₀]
    funext j
    have hh := hρ (y j)
    rw [hρσ, hτy, subst_add hsψ, subst_C, subst_X hsψ] at hh
    change ψ j = σ (q (y j)) - C (ε (q (y j)))
    exact eq_sub_iff_add_eq.mpr (by
      simpa only [q, Fin.addCases_right, add_comm] using hh.symm)

private theorem graph_map_subst {F K : Type*} [CommRing F] [CommRing K] {m r : ℕ}
    {ψ : Fin r → MvPowerSeries (Fin m) F} (hψ : ∀ j, constantCoeff (ψ j) = 0)
    (ι : F →+* K) (f : MvPowerSeries (Fin (m + r)) F) :
    subst (Fin.addCases X (fun j ↦ map ι (ψ j))) (map ι f) =
      map ι (subst (Fin.addCases X ψ) f) := by
  rw [map_subst (graph_hasSubst hψ)]
  congr 1
  funext i
  exact Fin.addCases (fun j ↦ by simp) (fun j ↦ by simp) i

private theorem evaluation_lift {B F : Type*} [CommRing B] [Field F] {ι : Type*}
    (ev : B →+* F) (f : B →+* MvPowerSeries ι F)
    (h₀ : ∀ b, constantCoeff (f b) = ev b) :
    ∃ fₚ : evaluationLocalization ev →+* MvPowerSeries ι F,
      ∀ b, fₚ (algebraMap B _ b) = f b := by
  let : (RingHom.ker ev).IsPrime := RingHom.ker_isPrime ev
  have hu : ∀ s : (RingHom.ker ev).primeCompl, IsUnit (f s) := by
    intro s
    rw [isUnit_iff_constantCoeff, h₀, isUnit_iff_ne_zero]
    exact s.property
  exact ⟨IsLocalization.lift (S := evaluationLocalization ev) hu,
    fun b ↦ IsLocalization.lift_eq hu b⟩

/-- Ambient expansion restricts by substitution into the uniquely determined formal graph.
The comparison extends to evaluation-prime localizations and every coefficient-field extension.
Source: Stacks Project, More on Morphisms, Tags 04FF and 02HG; agent coefficientwise assembly
(blueprint: lem-trf-etale-graph-taylor-comparison).

Proof plan, following the six steps of the node:
1. Put $R=L[[W]]$. For $n\ge1$, let $R_n$ be the ring of polynomials in $W$ of total degree $<n$,
with multiplication followed by deletion of terms of degree $\ge n$. Coefficient truncation $R\to
R_n$ is a ring map. The kernel of $R_{n+1}\to R_n$ consists of homogeneous terms of degree $n$ and
has square zero, since $2n\ge n+1$. Equality in all $R_n$ implies equality in $R$, by checking
each coefficient. For any $\eta\in(W)R^r$, define $S_\eta:L[[W,Y]]\to R$ by substitution
$Y=\eta(W)$. Modulo degree $n$, this is ordinary polynomial substitution using only monomials of
total degree $<n$: all substituted variables have zero constant term, so terms of degree $\ge n$
contribute nothing. These finite substitutions are compatible as $n$ varies and preserve sums and
products. Taking their coefficients defines the asserted $L$-algebra map. In particular it
preserves constant terms. This is a direct calculation with the coefficient-family definition of
power series; it uses no convergence theorem.
2. The two $k$-algebra maps $f=S_\phi\tau$ and $g=\sigma q$ from $A$ to $R$ have the same constant
term $\epsilon q$. They agree on every coordinate: $f(w_i)=g(w_i)=\epsilon q(w_i)+W_i$ and
$f(y_j)=g(y_j)=\epsilon q(y_j)+\phi_j$. Compare their reductions $f_n,g_n:A\to R_n$ by induction
on $n\ge1$. The base $n=1$ is the asserted equality of constant terms. If $f_n=g_n$, then
$f_{n+1},g_{n+1}$ are two lifts of the same map to $R_n$, over $\mathbf A_k^{m+r}$ with coordinate
values just displayed in $R_{n+1}$. The morphism $\operatorname{Spec}A\to\mathbf A_k^{m+r}$ is
flat and unramified by its etaleness. Apply [lem-weil-pbc-flat-unramified-formally-etale] to the
affine first order thickening $\operatorname{Spec}R_n\subset\operatorname{Spec}R_{n+1}$: its
uniqueness clause gives $f_{n+1}=g_{n+1}$. The contravariant affine-spectrum correspondence
identifies these scheme lifts with the ring maps in question. Thus the reductions agree for all
$n$, and coefficientwise separation from step 1 proves $S_\phi\tau=\sigma q$.
3. For each $i$, the comparison gives $S_\phi\tau(h_i)=\sigma(q(h_i))=0$, so $\phi$ is a solution.
Let $\psi\in(W)R^r$ be another solution. Since $S_\psi\tau$ is a homomorphism annihilating each
generator $h_i$, it annihilates their ideal and factors through the quotient as $\rho:D\to R$,
with $\rho q=S_\psi\tau$. Concretely $\rho(q(a))=S_\psi\tau(a)$; if $q(a)=q(a')$, their difference
is a finite sum $\sum_i b_i h_i$ and maps to zero. The maps $\rho$ and $\sigma$ have constant term
$\epsilon$ and send $q(w_i)$ to $\epsilon q(w_i)+W_i$. Induct on their reductions to $R_n$,
starting at $R_1=L$. At the induction step apply the uniqueness clause of
[lem-weil-pbc-flat-unramified-formally-etale], this time to the flat unramified morphism
$\operatorname{Spec}D\to\mathbf A_k^m$ and the same affine square-zero thickening. This gives
equality at $n+1$, hence $\rho=\sigma$ coefficientwise. Evaluating at $q(y_j)$ yields $\epsilon
q(y_j)+\psi_j=\rho(q(y_j))=\sigma(q(y_j))=\epsilon q(y_j)+\phi_j$, and cancellation proves
$\psi_j=\phi_j$ for every $j$.
4. Let $\mathfrak p=\ker(\epsilon q)\subset A$ and $\mathfrak d=\ker\epsilon\subset D$; these are
prime because their target $L$ is a field. A power series with constant term $a\ne0$ has inverse
$a^{-1}\sum_{v\ge0}(-u)^v$, where the series is written $a(1+u)$ and $u$ has zero constant term.
Every coefficient in this geometric sum is finite, and multiplying finite truncations gives $1$ in
every degree. Thus $\tau(s)$ is a unit for $s\notin\mathfrak p$, and $\sigma(t)$ is a unit for
$t\notin\mathfrak d$. Extend the maps to $A_{\mathfrak p}$ and $D_{\mathfrak d}$ by
$a/s\mapsto\tau(a)\tau(s)^{-1}$ and $b/t\mapsto\sigma(b)\sigma(t)^{-1}$; the fraction equivalence
relation makes these well defined. Since $q(s)\notin\mathfrak d$, $q$ also extends. Step 2,
applied to numerator and denominator, gives
$$S_\phi(\tau(a)\tau(s)^{-1})=\sigma(q(a))\sigma(q(s))^{-1}.$$ Substitution preserves inverses
because it is a unital ring map. This is the localized comparison. A zero-constant candidate
solving the localized equations also solves the original equations $h_i$, and so is $\phi$ by step
3. Conversely $\phi$ annihilates the whole localized defining ideal.
5. For $\iota:L\hookrightarrow K$, define $\iota_*\sum_E a_EX^E=\sum_E\iota(a_E)X^E$. The finite
coefficient sums for multiplication show that this is a ring map. The finite substitutions modulo
each degree in step 1 also give $$\iota_*S_\eta(f)=S_{\iota_*\eta}(\iota_*f).$$ Apply this to
$S_\phi\tau=\sigma q$; the maps $\tau_K=\iota_*\tau$, $\sigma_K=\iota_*\sigma$ and
$\epsilon_K=\iota\epsilon$ have exactly the required constant terms and coordinate values, and
$\phi_K=\iota_*\phi$ satisfies the comparison and equations over $K$. To verify uniqueness even
for a candidate in $(W)K[[W]]^r$ whose coefficients do not lie in $L$, repeat step 3 with $K$ in
place of $L$: its quotient factorization, square-zero uniqueness argument and coefficientwise
equality use only the field property of the coefficient ring. The etale maps of $k$-schemes remain
the originally given maps, so no etale base-change theorem is needed. This proves the asserted
uniqueness over $K$. The inverse series and fraction formulas of step 4 commute with $\iota_*$ as
well. The kernels of the evaluations are unchanged since $\iota$ is injective, so these formulas
also give the localized compatibility.
6. All degree truncations above allow an empty list of variables: if $m=0$, $R=R_n=L$ and $(W)=0$,
so both graph vectors are the unique zero vector and the comparisons are already the degree-one
comparisons. If $r=0$, the graph vector is empty, substitution fixes $W$, and the induction still
proves the comparison. If $s=0$, the quotient ideal is zero and the quotient factorization in step
3 imposes no equations; etaleness of $D=A$ over $\mathbf A_k^m$ still supplies the required
uniqueness. No step uses that $\epsilon$ is surjective, that its kernel is maximal, or that $L/k$
is algebraic: the only evaluation properties used are the stated constant terms and inverses of
nonzero field elements. Thus the argument covers the stated edge cases and arbitrary evaluation
primes.
-/
theorem etale_graph_taylor_comparison {k : Type u} {A : Type v} {L : Type w}
    [Field k] [CommRing A] [Field L] [Algebra k A] [Algebra k L]
    {m r s : ℕ} (w : Fin m → A) (y : Fin r → A) (h : Fin s → A)
    (hA : (MvPolynomial.aeval (Fin.addCases w y) :
      MvPolynomial (Fin (m + r)) k →ₐ[k] A).toRingHom.Etale)
    (hD : (MvPolynomial.aeval
      (fun i ↦ (Ideal.Quotient.mkₐ k (Ideal.span (Set.range h))) (w i)) :
      MvPolynomial (Fin m) k →ₐ[k] (A ⧸ Ideal.span (Set.range h))).toRingHom.Etale)
    (ε : (A ⧸ Ideal.span (Set.range h)) →ₐ[k] L)
    (τ : A →ₐ[k] MvPowerSeries (Fin (m + r)) L)
    (σ : (A ⧸ Ideal.span (Set.range h)) →ₐ[k] MvPowerSeries (Fin m) L)
    (hτ₀ : ∀ a, constantCoeff (τ a) = ε ((Ideal.Quotient.mkₐ k (Ideal.span (Set.range h))) a))
    (hσ₀ : ∀ d, constantCoeff (σ d) = ε d)
    (hτw : ∀ i, τ (w i) = C (ε ((Ideal.Quotient.mkₐ k (Ideal.span (Set.range h))) (w i))) + X
      (Fin.castAdd r i))
    (hτy : ∀ j, τ (y j) = C (ε ((Ideal.Quotient.mkₐ k (Ideal.span (Set.range h))) (y j))) + X
      (Fin.natAdd m j))
    (hσw : ∀ i, σ ((Ideal.Quotient.mkₐ k (Ideal.span (Set.range h))) (w i)) = C (ε
      ((Ideal.Quotient.mkₐ k (Ideal.span (Set.range h))) (w i))) + X i) :
    (∀ j, constantCoeff ((etaleGraphVector ε σ (fun j ↦ (Ideal.Quotient.mkₐ k (Ideal.span (Set.range
      h))) (y j))) j) = 0) ∧
    (∀ a, subst (Fin.addCases X (etaleGraphVector ε σ (fun j ↦ (Ideal.Quotient.mkₐ k (Ideal.span
      (Set.range h))) (y j)))) (τ a) = σ ((Ideal.Quotient.mkₐ k (Ideal.span (Set.range h))) a)) ∧
    (∀ i, subst (Fin.addCases X (etaleGraphVector ε σ (fun j ↦ (Ideal.Quotient.mkₐ k (Ideal.span
      (Set.range h))) (y j)))) (τ (h i)) = 0) ∧
    (∀ ψ : Fin r → MvPowerSeries (Fin m) L,
      (∀ j, constantCoeff (ψ j) = 0) →
      (∀ i, subst (Fin.addCases X ψ) (τ (h i)) = 0) → ψ = (etaleGraphVector ε σ (fun j ↦
        (Ideal.Quotient.mkₐ k (Ideal.span (Set.range h))) (y j)))) ∧
    (∃ (τₚ : evaluationLocalization (ε.comp (Ideal.Quotient.mkₐ k (Ideal.span (Set.range
      h)))).toRingHom →+*
          MvPowerSeries (Fin (m + r)) L)
        (σₚ : evaluationLocalization ε.toRingHom →+*
          MvPowerSeries (Fin m) L)
        (qₚ : evaluationLocalization (ε.comp (Ideal.Quotient.mkₐ k (Ideal.span (Set.range
          h)))).toRingHom →+*
          evaluationLocalization ε.toRingHom),
      (∀ a, τₚ (algebraMap A _ a) = τ a) ∧
      (∀ d, σₚ (algebraMap (A ⧸ Ideal.span (Set.range h)) _ d) = σ d) ∧
      (∀ a, qₚ (algebraMap A _ a) =
        algebraMap (A ⧸ Ideal.span (Set.range h)) _ ((Ideal.Quotient.mkₐ k (Ideal.span (Set.range
          h))) a)) ∧
      (∀ z, subst (Fin.addCases X (etaleGraphVector ε σ (fun j ↦ (Ideal.Quotient.mkₐ k (Ideal.span
        (Set.range h))) (y j)))) (τₚ z) = σₚ (qₚ z)) ∧
      (∀ i, subst (Fin.addCases X (etaleGraphVector ε σ (fun j ↦ (Ideal.Quotient.mkₐ k (Ideal.span
        (Set.range h))) (y j)))) (τₚ (algebraMap A _ (h i))) = 0) ∧
      (∀ ψ : Fin r → MvPowerSeries (Fin m) L,
        (∀ j, constantCoeff (ψ j) = 0) →
        (∀ i, subst (Fin.addCases X ψ) (τₚ (algebraMap A _ (h i))) = 0) →
        ψ = (etaleGraphVector ε σ (fun j ↦ (Ideal.Quotient.mkₐ k (Ideal.span (Set.range h))) (y
          j)))) ∧
      (∀ (K : Type x) [Field K] [Algebra k K] (ι : L →ₐ[k] K) z,
        subst (Fin.addCases X (fun j ↦ map ι.toRingHom ((etaleGraphVector ε σ (fun j ↦
          (Ideal.Quotient.mkₐ k (Ideal.span (Set.range h))) (y j))) j)))
          (map ι.toRingHom (τₚ z)) = map ι.toRingHom (σₚ (qₚ z)))) ∧
    (∀ (K : Type x) [Field K] [Algebra k K] (ι : L →ₐ[k] K),
      (∀ j, constantCoeff (map ι.toRingHom ((etaleGraphVector ε σ (fun j ↦ (Ideal.Quotient.mkₐ k
        (Ideal.span (Set.range h))) (y j))) j)) = 0) ∧
      (∀ a, subst (Fin.addCases X (fun j ↦ map ι.toRingHom ((etaleGraphVector ε σ (fun j ↦
        (Ideal.Quotient.mkₐ k (Ideal.span (Set.range h))) (y j))) j)))
        (map ι.toRingHom (τ a)) = map ι.toRingHom (σ ((Ideal.Quotient.mkₐ k (Ideal.span (Set.range
          h))) a))) ∧
      (∀ i, subst (Fin.addCases X (fun j ↦ map ι.toRingHom ((etaleGraphVector ε σ (fun j ↦
        (Ideal.Quotient.mkₐ k (Ideal.span (Set.range h))) (y j))) j)))
        (map ι.toRingHom (τ (h i))) = 0) ∧
      (∀ ψ : Fin r → MvPowerSeries (Fin m) K,
        (∀ j, constantCoeff (ψ j) = 0) →
        (∀ i, subst (Fin.addCases X ψ) (map ι.toRingHom (τ (h i))) = 0) →
        ψ = fun j ↦ map ι.toRingHom ((etaleGraphVector ε σ (fun j ↦ (Ideal.Quotient.mkₐ k
          (Ideal.span (Set.range h))) (y j))) j))) := by
  let q := Ideal.Quotient.mkₐ k (Ideal.span (Set.range h))
  let φ := etaleGraphVector ε σ (fun j ↦ q (y j))
  obtain ⟨hφ₀, hc, heq, hu⟩ := graph_core w y h hA hD ε τ σ hτ₀ hσ₀ hτw hτy hσw
  change (∀ j, constantCoeff (φ j) = 0) ∧ _
  refine ⟨hφ₀, hc, heq, hu, ?_, ?_⟩
  · let ev := (ε.comp q).toRingHom
    let : (RingHom.ker ev).IsPrime := RingHom.ker_isPrime ev
    let : (RingHom.ker ε.toRingHom).IsPrime := RingHom.ker_isPrime ε.toRingHom
    obtain ⟨τₚ, hτₚ⟩ := evaluation_lift ev τ.toRingHom hτ₀
    obtain ⟨σₚ, hσₚ⟩ := evaluation_lift ε.toRingHom σ.toRingHom hσ₀
    let qₚ : evaluationLocalization ev →+* evaluationLocalization ε.toRingHom :=
      Localization.localRingHom (RingHom.ker ev) (RingHom.ker ε.toRingHom) q.toRingHom rfl
    have hqₚ (a : A) : qₚ (algebraMap A _ a) =
        algebraMap (A ⧸ Ideal.span (Set.range h)) _ (q a) :=
      Localization.localRingHom_to_map _ _ _ _ a
    have hs := graph_hasSubst hφ₀
    have hloc : ∀ z, subst (Fin.addCases X φ) (τₚ z) = σₚ (qₚ z) := by
      have hh : (substAlgHom hs).toRingHom.comp τₚ = σₚ.comp qₚ := by
        apply IsLocalization.ringHom_ext (RingHom.ker ev).primeCompl
        apply RingHom.ext
        intro a
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
          substAlgHom_apply]
        change subst (Fin.addCases X φ) (τₚ (algebraMap A _ a)) =
          σₚ (qₚ (algebraMap A _ a))
        rw [hτₚ, hqₚ, hσₚ]
        exact hc a
      intro z
      simpa only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        substAlgHom_apply] using
        RingHom.congr_fun hh z
    refine ⟨τₚ, σₚ, qₚ, hτₚ, hσₚ, hqₚ, hloc, ?_, ?_, ?_⟩
    · intro i
      rw [hτₚ]
      exact heq i
    · intro ψ hψ₀ hψ
      apply hu ψ hψ₀
      intro i
      have hh := hψ i
      change subst (Fin.addCases X ψ) (τₚ (algebraMap A (evaluationLocalization ev) (h i))) = 0
        at hh
      rw [hτₚ] at hh
      exact hh
    · intro K _ _ ι z
      rw [graph_map_subst hφ₀, hloc]
  · intro K _ _ ι
    have hK := graph_core w y h hA hD (ι.comp ε) ((mapAlgHom ι).comp τ)
      ((mapAlgHom ι).comp σ)
      (fun a ↦ by
        simp only [AlgHom.comp_apply, mapAlgHom_apply,
          constantCoeff_map, hτ₀, AlgHom.coe_toRingHom])
      (fun d ↦ by
        simp only [AlgHom.comp_apply, mapAlgHom_apply,
          constantCoeff_map, hσ₀, AlgHom.coe_toRingHom])
      (fun i ↦ by
        simp only [AlgHom.comp_apply, mapAlgHom_apply, hτw,
          map_add, map_C, map_X, AlgHom.coe_toRingHom])
      (fun j ↦ by
        simp only [AlgHom.comp_apply, mapAlgHom_apply, hτy,
          map_add, map_C, map_X, AlgHom.coe_toRingHom])
      (fun i ↦ by
        simp only [AlgHom.comp_apply, mapAlgHom_apply, hσw,
          map_add, map_C, map_X, AlgHom.coe_toRingHom])
    have hφK : etaleGraphVector (ι.comp ε) ((mapAlgHom ι).comp σ)
        (fun j ↦ q (y j)) = fun j ↦ map ι.toRingHom (φ j) := by
      funext j
      simp only [etaleGraphVector, AlgHom.comp_apply, mapAlgHom_apply, φ, map_sub, map_C,
        AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
    change (∀ j, constantCoeff ((etaleGraphVector (ι.comp ε) ((mapAlgHom ι).comp σ)
      (fun j ↦ q (y j))) j) = 0) ∧ _ at hK
    rw [hφK] at hK
    exact hK

end MvPowerSeries
