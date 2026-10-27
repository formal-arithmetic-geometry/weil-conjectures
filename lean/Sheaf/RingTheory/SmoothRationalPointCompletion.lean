/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q16
-/
module

public import WeilConjectures.RingTheory.EssentiallySmooth
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import WeilConjectures.RingTheory.AssociatedGradedRing
import Sheaf.RingTheory.PolynomialCombinedIdealCoefficients
import Mathlib.RingTheory.AdicCompletion.Topology
import Sheaf.RingTheory.PolynomialCombinedCompletion
import Sheaf.RingTheory.CompletionEquivPowerQuotients
import Sheaf.RingTheory.PolynomialCombinedAssociatedGraded
import Sheaf.RingTheory.FormallyEtaleAssociatedGraded
import Mathlib.RingTheory.MvPowerSeries.Inverse
import WeilConjectures.RingTheory.PowerSeriesCombinedIdealCoefficients
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.AdicCompletion.Completeness

/-!
# Completion and tangent cone at a rational point of an essentially smooth local map

Source: Stacks Project, Morphisms, Tag 054L, and More on Algebra, Tag 0AGX.
(blueprint: lem-trf-smooth-rational-point-completion)
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open IsLocalRing TensorProduct

namespace Algebra

private theorem essentiallySmooth_polynomial_chart
    (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [IsLocalRing S] [Algebra R S] (h : EssentiallySmooth R S) :
    ∃ (d : ℕ) (f : MvPolynomial (Fin d) R →ₐ[R] S), f.toRingHom.FormallyEtale := by
  obtain ⟨P, hP, hRP, hsm, W, ⟨e⟩⟩ := h
  let := hP
  let := hRP
  let := hsm
  let : Algebra P S :=
    (e.symm.toRingHom.comp (algebraMap P (Localization W))).toAlgebra
  have : IsScalarTower R P S := .of_algebraMap_eq fun r => by
    change algebraMap R S r = e.symm (algebraMap P (Localization W) (algebraMap R P r))
    rw [← IsScalarTower.algebraMap_apply R P (Localization W), e.symm.commutes]
  have : IsLocalization W S :=
    (IsLocalization.isLocalization_iff_of_ringEquiv W e.symm.toRingEquiv).mp inferInstance
  let p := (maximalIdeal S).comap (algebraMap P S)
  have : p.IsPrime := Ideal.comap_isPrime _ _
  have hWp : W ≤ p.primeCompl := by
    intro x hx
    exact fun hn => hn (IsLocalization.map_units S (⟨x, hx⟩ : W))
  have : IsLocalization p.primeCompl S :=
    IsLocalization.of_le W p.primeCompl hWp fun x hx => by
      exact not_not.mp hx
  have : IsSmoothAt R p := inferInstance
  obtain ⟨g, hgp, d, hpoly, htower, het⟩ :=
    IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := R) (p := p)
  let := hpoly
  let := htower
  let := het
  let l : Localization.Away g →ₐ[R] S :=
    IsLocalization.liftAlgHom (M := Submonoid.powers g)
      (f := IsScalarTower.toAlgHom R P S) fun x => by
        apply not_not.mp
        obtain ⟨k, hk⟩ := x.property
        change ¬ (algebraMap P S) (x : P) ∈ maximalIdeal S
        rw [← hk]
        exact p.primeCompl.pow_mem hgp k
  let : Algebra (Localization.Away g) S := l.toRingHom.toAlgebra
  have : IsScalarTower P (Localization.Away g) S := .of_algebraMap_eq fun x => by
    change algebraMap P S x = IsLocalization.lift _ (algebraMap P (Localization.Away g) x)
    simp
  have : IsScalarTower R (Localization.Away g) S := .to₁₃₄ R P _ S
  have : IsLocalization (p.primeCompl.map (algebraMap P (Localization.Away g))) S :=
    IsLocalization.isLocalization_of_submonoid_le (Localization.Away g) S
      (Submonoid.powers g) p.primeCompl (Submonoid.powers_le.mpr hgp)
  have : FormallyEtale (Localization.Away g) S :=
    FormallyEtale.of_isLocalization (p.primeCompl.map (algebraMap P (Localization.Away g)))
  let f := l.comp (IsScalarTower.toAlgHom R (MvPolynomial (Fin d) R) (Localization.Away g))
  refine ⟨d, f, ?_⟩
  have h₁ : (algebraMap (MvPolynomial (Fin d) R) (Localization.Away g)).FormallyEtale :=
    RingHom.formallyEtale_algebraMap.mpr inferInstance
  have h₂ : l.toRingHom.FormallyEtale :=
    (RingHom.formallyEtale_algebraMap (R := Localization.Away g) (S := S)).mpr inferInstance
  exact h₁.comp h₂

private theorem formallyEtale_ringEquiv {A : Type*} {B : Type*}
    [CommRing A] [CommRing B] (e : A ≃+* B) : e.toRingHom.FormallyEtale := by
  let : Algebra A B := e.toRingHom.toAlgebra
  let E : A ≃ₐ[A] B := { e with commutes' _ := rfl }
  exact FormallyEtale.of_equiv E

private theorem polynomial_chart_rank
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [IsLocalRing S]
    [Algebra R S] (d : ℕ) (f : MvPolynomial (Fin d) R →ₐ[R] S)
    (hf : f.toRingHom.FormallyEtale) :
    Module.Finite (ResidueField S) ((ResidueField S) ⊗[S] KaehlerDifferential R S) ∧
      Module.finrank (ResidueField S) ((ResidueField S) ⊗[S] KaehlerDifferential R S) = d := by
  let : Algebra (MvPolynomial (Fin d) R) S := f.toAlgebra
  have : IsScalarTower R (MvPolynomial (Fin d) R) S :=
    .of_algebraMap_eq' f.comp_algebraMap.symm
  have : FormallyEtale (MvPolynomial (Fin d) R) S := hf
  let b := ((KaehlerDifferential.mvPolynomialBasis R (Fin d)).baseChange S).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R (MvPolynomial (Fin d) R) S)
  let b' := b.baseChange (ResidueField S)
  exact ⟨Module.Finite.of_basis b', by simpa using Module.finrank_eq_card_basis b'⟩

private theorem centered_polynomial_chart
    (R : Type u) (S : Type v) (L : Type w)
    [CommRing R] [CommRing S] [Field L] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] (rR : ResidueField R ≃+* L) (rS : ResidueField S ≃+* L)
    (hres : ∀ a : R, rS (residue S (algebraMap R S a)) = rR (residue R a))
    (h : EssentiallySmooth R S) :
    ∃ (d : ℕ) (f : MvPolynomial (Fin d) R →ₐ[R] S),
      f.toRingHom.FormallyEtale ∧
      (∀ i, residue S (f (MvPolynomial.X i)) = 0) := by
  classical
  obtain ⟨d, f, hf⟩ := essentiallySmooth_polynomial_chart R S h
  have hsurj : Function.Surjective (fun a : R => rR (residue R a)) :=
    rR.surjective.comp (residue_surjective)
  choose a ha using fun i : Fin d => hsurj (rS (residue S (f (MvPolynomial.X i))))
  let t : MvPolynomial (Fin d) R →ₐ[R] MvPolynomial (Fin d) R :=
    MvPolynomial.aeval (fun i => MvPolynomial.X i - MvPolynomial.C (a i))
  let t' : MvPolynomial (Fin d) R →ₐ[R] MvPolynomial (Fin d) R :=
    MvPolynomial.aeval (fun i => MvPolynomial.X i + MvPolynomial.C (a i))
  let E : MvPolynomial (Fin d) R ≃ₐ[R] MvPolynomial (Fin d) R :=
    AlgEquiv.ofAlgHom t t' (by ext i; simp [t, t']) (by ext i; simp [t, t'])
  refine ⟨d, f.comp t, (formallyEtale_ringEquiv E.toRingEquiv).comp hf, ?_⟩
  intro i
  apply rS.injective
  simp only [AlgHom.comp_apply, t, MvPolynomial.aeval_X, map_sub, map_zero]
  rw [show f (MvPolynomial.C (a i)) = algebraMap R S (a i) from f.commutes (a i),
    hres]
  exact sub_eq_zero.mpr (ha i).symm

private theorem polynomial_chart_residue
    (R : Type u) (S : Type v) (L : Type w)
    [CommRing R] [CommRing S] [Field L] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] (rR : ResidueField R ≃+* L) (rS : ResidueField S ≃+* L)
    (hres : ∀ a : R, rS (residue S (algebraMap R S a)) = rR (residue R a))
    (d : ℕ) (f : MvPolynomial (Fin d) R →ₐ[R] S)
    (hX : ∀ i, residue S (f (MvPolynomial.X i)) = 0) :
    ∀ p, rS (residue S (f p)) = rR (residue R (MvPolynomial.constantCoeff p)) := by
  have heq : rS.toRingHom.comp ((residue S).comp f.toRingHom) =
      (rR.toRingHom.comp (residue R)).comp MvPolynomial.constantCoeff := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simpa using hres a
    · intro i
      simp [hX]
  exact RingHom.congr_fun heq

private theorem polynomial_chart_contraction
    (R : Type u) (S : Type v) (L : Type w)
    [CommRing R] [CommRing S] [Field L] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] (rR : ResidueField R ≃+* L) (rS : ResidueField S ≃+* L)
    (hres : ∀ a : R, rS (residue S (algebraMap R S a)) = rR (residue R a))
    (d : ℕ) (f : MvPolynomial (Fin d) R →ₐ[R] S)
    (hX : ∀ i, residue S (f (MvPolynomial.X i)) = 0) :
    (maximalIdeal S).comap f.toRingHom =
      (maximalIdeal R).map MvPolynomial.C ⊔ MvPolynomial.idealOfVars (Fin d) R := by
  ext p
  rw [← pow_one ((maximalIdeal R).map MvPolynomial.C ⊔
    MvPolynomial.idealOfVars (Fin d) R), MvPolynomial.mem_combined_ideal_pow_iff]
  have hp : f p ∈ maximalIdeal S ↔ MvPolynomial.constantCoeff p ∈ maximalIdeal R := by
    rw [← residue_eq_zero_iff, ← residue_eq_zero_iff]
    rw [← rS.injective.eq_iff, map_zero,
      polynomial_chart_residue R S L rR rS hres d f hX p]
    exact rR.map_eq_zero_iff
  change f p ∈ maximalIdeal S ↔ _
  rw [hp]
  constructor
  · intro hp E
    by_cases hE : E = 0
    · subst E
      simpa [MvPolynomial.constantCoeff_eq] using hp
    · have hd : 1 ≤ E.degree := by
        have := (Finsupp.degree_eq_zero_iff E).not.mpr hE
        omega
      simp [Nat.sub_eq_zero_of_le hd]
  · intro hp
    simpa [MvPolynomial.constantCoeff_eq] using hp 0

private theorem polynomial_chart_residue_surjective
    (R : Type u) (S : Type v) (L : Type w)
    [CommRing R] [CommRing S] [Field L] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] (rR : ResidueField R ≃+* L) (rS : ResidueField S ≃+* L)
    (hres : ∀ a : R, rS (residue S (algebraMap R S a)) = rR (residue R a))
    (d : ℕ) (f : MvPolynomial (Fin d) R →ₐ[R] S) :
    Function.Surjective ((Ideal.Quotient.mk (maximalIdeal S)).comp f.toRingHom) := by
  intro b
  obtain ⟨a, ha⟩ := (rR.surjective.comp residue_surjective) (rS b)
  refine ⟨MvPolynomial.C a, ?_⟩
  apply rS.injective
  change rS (residue S (f (MvPolynomial.C a))) = rS b
  rw [show f (MvPolynomial.C a) = algebraMap R S a from f.commutes a, hres]
  exact ha

private theorem powerSeries_maximalIdeal
    (A : Type*) [CommRing A] [IsLocalRing A] (d : ℕ) :
    maximalIdeal (MvPowerSeries (Fin d) A) =
      (maximalIdeal A).map MvPowerSeries.C ⊔
        Ideal.span (Set.range (MvPowerSeries.X (σ := Fin d) (R := A))) := by
  ext F
  change (¬ IsUnit F) ↔ _
  rw [MvPowerSeries.isUnit_iff_constantCoeff]
  change MvPowerSeries.constantCoeff F ∈ maximalIdeal A ↔ _
  change MvPowerSeries.constantCoeff F ∈ maximalIdeal A ↔
    F ∈ (maximalIdeal A).map (algebraMap A (MvPowerSeries (Fin d) A)) ⊔
      Ideal.span (Set.range MvPowerSeries.X)
  rw [← pow_one ((maximalIdeal A).map (algebraMap A (MvPowerSeries (Fin d) A)) ⊔
    Ideal.span (Set.range (MvPowerSeries.X (σ := Fin d) (R := A)))),
    power_series_mem_combined_ideal_pow_iff A (maximalIdeal A) d 1 F]
  constructor
  · intro h E hE
    have he : E = 0 := (Finsupp.degree_eq_zero_iff E).mp (by omega)
    subst E
    simpa using h
  · intro h
    simpa using h 0 (by simp)

/-- The maximal-ideal completion of an essentially smooth rational local point is a
power-series algebra over the completed base, and its tangent cone is a graded polynomial
extension. The completion algebra structure is specified on every quotient coordinate.
The graded base compatibility sends the degree `n` class of every `a ∈ m^n` to
the degree `n` class of its image in `S`; the polynomial variables have degree one.
The residue comparison uses the specified identifications with `L`, rather than an abstract
residue-field isomorphism.

Source: Stacks Project, Tag 054L followed by Tag 0AGX.
(blueprint: lem-trf-smooth-rational-point-completion)

Proof:
1. Choose a smooth $R$-algebra $A$ and a localization $S=W^{-1}A$. If $\mathfrak p\subset A$ is
   the inverse image of $\mathfrak n$, every element of $A\setminus\mathfrak p$ maps to a unit of
   the local ring $S$. The two localization maps give mutually inverse $R$-algebra maps
   $A_{\mathfrak p}\leftrightarrows S$. Apply the smooth-ring/affine-scheme equivalence and the
   etale local normal form at $\mathfrak p$. The base affine neighbourhood contains the closed
   point of $\operatorname{Spec}R$, hence is all of $\operatorname{Spec}R$: every open of a local
   spectrum containing its closed point is the whole spectrum. We obtain a finite integer
   $d\geq0$, an etale map $C=R[X_1,\ldots,X_d]\to B$, and a prime $\mathfrak b$ of $B$ with
   $S=B_{\mathfrak b}$ as $R$-algebras. Restricting the affine neighbourhood does not change this
   local ring.
   Uses: def-weil-pbc-essentially-smooth-ring-map, lem-weil-pbc-smooth-ring-map-iff-smooth-affine,
   sbc-thm-etale-local-normal-form.
2. Let $\overline a_i\in L$ be the image of $X_i$ under $C\to S\to L$, choose lifts $a_i\in R$,
   and put $Z_i=X_i-a_i$. This translation identifies $C$ with $R[Z_1,\ldots,Z_d]$. The map $C\to
   L$ sends the $Z_i$ to zero and has kernel $Q=(\mathfrak m,Z_1,\ldots,Z_d)$, since its reduction
   modulo this ideal is the specified isomorphism $R/\mathfrak m\to L$. Thus $\mathfrak b\cap
   C=Q$, $T=C_Q$ is local with residue field $L$, and $T\to S$ is a local map inducing the
   specified identity on $L$. All maps still restrict to the original map from $R$.
   Uses: def-weil-pbc-mv-polynomial-ring.
3. By the affine etaleness equivalence the etale chart $C\to B$ has $H_1(L_{B/C})=0$ and
   $\Omega_{B/C}=0$. Apply the formally etale differential base-change statement to $R\to C\to B$,
   and then localize at $\mathfrak b$. The polynomial differential basis and localization of
   differentials identify $\Omega_{S/R}$ with $\bigoplus_{i=1}^d S\,\mathrm dZ_i$. Tensoring this
   displayed free basis with $L$ gives $\Omega_{S/R}\otimes_S L\cong L^d$. Hence the integer $s$
   in the statement is finite and equals $d$.
   Uses: lem-weil-pbc-etale-ring-map-iff-etale-affine,
   lem-trf-formally-etale-differentials-base-change, lem-weil-pbc-polynomial-ring-kahler-basis,
   lem-weil-pbc-kahler-differentials-localization.
4. The finite type morphism $\operatorname{Spec}C\to\operatorname{Spec}R$ has locally Noetherian
   source by the locally-Noetherian finite-type theorem. On a Noetherian affine neighbourhood of
   $Q$, the local ring $T$ is a localization of its Noetherian coordinate ring, so $T$ is
   Noetherian. The map $C\to B$ is flat and $B\to B_{\mathfrak b}=S$ is flat. Their composite is
   flat: tensoring an injection first with $B$ and then with $S$ preserves injectivity, and
   associativity identifies the result with tensoring with $S$ over $C$. As $S$ is a
   $T=C_Q$-algebra, the flat-over-localization equivalence makes $T\to S$ flat. The etale
   prime/maximal-ideal statement gives $QS=\mathfrak n$, so the maximal ideal $QT$ of $T$ extends
   to $\mathfrak n$.
   Uses: pqf-lem-locnoeth-lft, pqf-def-locnoeth, lem-weil-pbc-localization-noetherian,
   lem-weil-pbc-etale-algebra-flat, lem-weil-pbc-localization-flat,
   lem-weil-pbc-flat-over-localization, lem-weil-pbc-etale-prime-generates-maximal.
5. Apply the flat-local completion isomorphism to $T\to S$. Both rings are Noetherian and local,
   the extended maximal ideal is $\mathfrak n$ by Step 4, and the induced residue map is the
   identity of $L$ by Step 2. We obtain the actual induced isomorphism $\widehat
   T\xrightarrow{\sim}\widehat S$. It commutes with the maps from $R$, and its reduction on $L$ is
   the identity. By its coordinatewise construction it also commutes with the maps from $\widehat
   R$.
   Uses: lem-weil-pbc-flat-local-completion-iso, def-weil-pbc-adic-completion.
6. For $N\geq1$, expand $Q^N=\sum_{|\beta|\leq N}\mathfrak m^{N-|\beta|}Z^\beta C$. Comparing
   monomial coefficients gives $$C/Q^N=\bigoplus_{|\alpha|<N}(R/\mathfrak
   m^{N-|\alpha|})Z^\alpha$$ as additive groups, with multiplication given by polynomial
   convolution and the indicated coefficient reductions. Indeed the coefficient ideal of
   $Z^\alpha$ in $Q^N$ is $\mathfrak m^{\max(N-|\alpha|,0)}$: each generating summand is contained
   in this ideal, and conversely choose $\beta\leq\alpha$ of degree $\min(|\alpha|,N)$. Every
   $g\notin Q$ has unit constant coefficient $r\in R$ and $g=r+h$, $h\in Q$; its inverse modulo
   $Q^N$ is $r^{-1}\sum_{j=0}^{N-1}(-h/r)^j$. Thus localization changes none of these quotients,
   giving compatible ring isomorphisms $C/Q^N\cong T/(QT)^N$.
   Uses: def-weil-pbc-mv-polynomial-ring.
7. Take inverse limits of the explicit quotients in Step 6, using the compatible-sequence
   definition of completion. For each fixed multi-index $\alpha$, the coefficients form a
   compatible sequence modulo $\mathfrak m^{N-|\alpha|}$ for $N>|\alpha|$, hence a unique element
   $c_\alpha\in\widehat R$. Conversely any family $(c_\alpha)_{\alpha\in\mathbf N^d}$ defines the
   $N$th quotient coordinate by retaining only $|\alpha|<N$ and reducing its coefficient modulo
   $\mathfrak m^{N-|\alpha|}$. These two constructions are inverse. They preserve products because
   the coefficient of each monomial is the same finite convolution in both rings. Hence $\widehat
   T\cong\widehat R[[Z_1,\ldots,Z_d]]$ as $\widehat R$-algebras, with the constants giving the
   original base map. Composing its inverse with Step 5 and using $d=s$ proves the requested
   algebra isomorphism and its compatibility on $L$.
   Uses: def-weil-pbc-adic-completion, def-weil-pbc-multivariate-power-series.
8. The maximal ideal $\mathfrak m$ is finitely generated, so the completion-mod-power statement
   gives $\widehat R/\mathfrak m\widehat R=R/\mathfrak m=L$. Every element of $\widehat R$ whose
   residue is nonzero is a unit: its coordinates in each local ring $R/\mathfrak m^N$ are units
   and their inverses are compatible. Thus $\widehat R$ is local with maximal ideal $\mathfrak
   m\widehat R$. A formal series is a unit exactly when its constant coefficient is a unit: solve
   the coefficients of its inverse recursively by total degree (necessity follows by evaluating at
   zero). Every series with zero constant coefficient is a sum $\sum_{i=1}^d Z_i f_i$, assigning
   each positive-degree monomial to its first variable with positive exponent. Consequently the
   maximal ideal of the power series ring is precisely $(\mathfrak m\widehat R,Z_1,\ldots,Z_d)$.
   The isomorphism of Step 7 respects this maximal ideal and its powers, so it is an isomorphism
   of complete local algebras. When $d=0$ the same argument has an empty sum and the power series
   ring is $\widehat R$.
   Uses: lem-weil-pbc-adic-completion-mod-power, def-weil-pbc-multivariate-power-series.
9. For every $N\geq1$ the ideals $QT$ and $\mathfrak n$ are finitely generated, since $T$ and $S$
   are Noetherian. Apply the completion-mod-power statement to both and use the local isomorphism
   of Step 5: the actual map $T/(QT)^N\to S/\mathfrak n^N$ is an isomorphism. Together with Step 6
   this identifies the compatible quotient towers of $(C,Q)$ and $(S,\mathfrak n)$. Kernels of the
   reductions from level $r+1$ to level $r$ identify their graded pieces for $r\geq1$; degree zero
   is their common residue field $L$. Step 6 computes the $r$th piece as
   $$Q^r/Q^{r+1}\cong\bigoplus_{|\alpha|\leq r}(\mathfrak m^{r-|\alpha|}/\mathfrak
   m^{r-|\alpha|+1})Z^\alpha.$$ On these summands multiplication is exactly
   $[a]Z^\alpha\,[b]Z^\beta=[ab]Z^{\alpha+\beta}$. This proves the graded algebra isomorphism
   $\operatorname{gr}_{\mathfrak n}S\cong(\operatorname{gr}_{\mathfrak m}R)[Z_1,\ldots,Z_d]$, with
   each $Z_i$ in degree one. The constants throughout are the given maps from $R$, so the
   isomorphism respects the base graded map and the specified $L$-algebra structures.
   Uses: lem-weil-pbc-adic-completion-mod-power, def-weil-pbc-associated-graded-ring.
-/
theorem essentiallySmooth_rationalPoint_completion
    (R : Type u) (S : Type v) (L : Type w)
    [CommRing R] [CommRing S] [Field L]
    [IsLocalRing R] [IsLocalRing S] [IsNoetherianRing R] [IsNoetherianRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    (rR : ResidueField R ≃+* L) (rS : ResidueField S ≃+* L)
    (hres : ∀ a : R, rS (residue S (algebraMap R S a)) = rR (residue R a))
    (hsmooth : EssentiallySmooth R S) :
    Module.Finite (ResidueField S) ((ResidueField S) ⊗[S] KaehlerDifferential R S) ∧
    ∃ s : ℕ,
      Module.finrank (ResidueField S)
        ((ResidueField S) ⊗[S] KaehlerDifferential R S) = s ∧
      ∃ e : AdicCompletion (maximalIdeal S) S ≃+*
          MvPowerSeries (Fin s) (AdicCompletion (maximalIdeal R) R),
        (∀ (n : ℕ) (x : AdicCompletion (maximalIdeal R) R) (a : R),
          AdicCompletion.evalₐ (maximalIdeal R) n x =
              Ideal.Quotient.mk (maximalIdeal R ^ n) a →
            AdicCompletion.evalₐ (maximalIdeal S) n (e.symm (MvPowerSeries.C x)) =
              Ideal.Quotient.mk (maximalIdeal S ^ n) (algebraMap R S a)) ∧
        (∀ x : AdicCompletion (maximalIdeal S) S,
          rR (AdicCompletion.evalOneₐ (maximalIdeal R) (MvPowerSeries.constantCoeff (e x))) =
            rS (AdicCompletion.evalOneₐ (maximalIdeal S) x)) ∧
        IsLocalRing (AdicCompletion (maximalIdeal S) S) ∧
        IsLocalRing (MvPowerSeries (Fin s) (AdicCompletion (maximalIdeal R) R)) ∧
        IsAdicComplete
          ((maximalIdeal S).map (algebraMap S (AdicCompletion (maximalIdeal S) S)))
          (AdicCompletion (maximalIdeal S) S) ∧
        IsAdicComplete
          ((maximalIdeal R).map
              ((MvPowerSeries.C (σ := Fin s)).comp
                (algebraMap R (AdicCompletion (maximalIdeal R) R))) ⊔
            Ideal.span (Set.range (MvPowerSeries.X (σ := Fin s)
              (R := AdicCompletion (maximalIdeal R) R))))
          (MvPowerSeries (Fin s) (AdicCompletion (maximalIdeal R) R)) ∧
        ((maximalIdeal R).map
            ((MvPowerSeries.C (σ := Fin s)).comp
              (algebraMap R (AdicCompletion (maximalIdeal R) R))) ⊔
          Ideal.span (Set.range (MvPowerSeries.X (σ := Fin s)
            (R := AdicCompletion (maximalIdeal R) R)))).IsMaximal ∧
        Ideal.map e.toRingHom
            ((maximalIdeal S).map (algebraMap S (AdicCompletion (maximalIdeal S) S))) =
          (maximalIdeal R).map
              ((MvPowerSeries.C (σ := Fin s)).comp
                (algebraMap R (AdicCompletion (maximalIdeal R) R))) ⊔
            Ideal.span (Set.range (MvPowerSeries.X (σ := Fin s)
              (R := AdicCompletion (maximalIdeal R) R))) ∧
        ∃ g : MvPolynomial (Fin s) (Ideal.associatedGraded (maximalIdeal R)) ≃+*
            Ideal.associatedGraded (maximalIdeal S),
          (∀ (n : ℕ) (a : R) (ha : a ∈ maximalIdeal R ^ n)
              (hb : algebraMap R S a ∈ maximalIdeal S ^ n),
            g (MvPolynomial.C
                (DirectSum.of (Ideal.associatedGradedPiece (maximalIdeal R)) n
                  (Submodule.Quotient.mk (⟨a, ha⟩ : (maximalIdeal R ^ n : Ideal R))))) =
              DirectSum.of (Ideal.associatedGradedPiece (maximalIdeal S)) n
                (Submodule.Quotient.mk
                  (⟨algebraMap R S a, hb⟩ : (maximalIdeal S ^ n : Ideal S)))) ∧
          ∀ i : Fin s, ∃ z : Ideal.associatedGradedPiece (maximalIdeal S) 1,
            g (MvPolynomial.X i) =
              DirectSum.of (Ideal.associatedGradedPiece (maximalIdeal S)) 1 z := by
  classical
  obtain ⟨d, f, hf, hX⟩ := centered_polynomial_chart R S L rR rS hres hsmooth
  obtain ⟨hfinite, hrank⟩ := polynomial_chart_rank R S d f hf
  refine ⟨hfinite, d, hrank, ?_⟩
  let I := maximalIdeal R
  let J := maximalIdeal S
  let Q := J.comap f.toRingHom
  have hQ : Q = I.map (MvPolynomial.C (σ := Fin d)) ⊔
      MvPolynomial.idealOfVars (Fin d) R :=
    polynomial_chart_contraction R S L rR rS hres d f hX
  have hle : Q ≤ J.comap f.toRingHom := le_rfl
  obtain ⟨hbij, gS, hgS, _⟩ := Ideal.formallyEtale_powerQuotient_associatedGraded
    f.toRingHom J hf (polynomial_chart_residue_surjective R S L rR rS hres d f)
  have hbijQ : ∀ n : ℕ,
      Function.Bijective (Ideal.powerQuotientMap f.toRingHom Q J hle n) := by
    intro n
    by_cases hn : 1 ≤ n
    · exact hbij n hn
    · have hn0 : n = 0 := by omega
      subst n
      have : Subsingleton (MvPolynomial (Fin d) R ⧸ Q ^ 0) := by
        apply Ideal.Quotient.subsingleton_iff.mpr
        simp
      have : Subsingleton (S ⧸ J ^ 0) := by
        apply Ideal.Quotient.subsingleton_iff.mpr
        simp
      exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun b =>
        ⟨0, Subsingleton.elim _ _⟩⟩
  obtain ⟨eS, heS⟩ :=
    AdicCompletion.equiv_of_powerQuotient_bijective f.toRingHom Q J hle hbijQ
  have hP := MvPolynomial.combinedIdeal_completion R d
  dsimp only at hP
  rw [← hQ] at hP
  obtain ⟨eP, heP, hresP⟩ := hP
  let e := eS.symm.trans eP
  have hQhat : maximalIdeal (MvPowerSeries (Fin d) (AdicCompletion I R)) =
      I.map ((MvPowerSeries.C (σ := Fin d)).comp
        (algebraMap R (AdicCompletion I R))) ⊔
        Ideal.span (Set.range (MvPowerSeries.X (σ := Fin d)
          (R := AdicCompletion I R))) := by
    rw [powerSeries_maximalIdeal, AdicCompletion.maximalIdeal_eq_map, Ideal.map_map]
  refine ⟨e, ?_, ?_, inferInstance, inferInstance,
    AdicCompletion.isAdicComplete_self J J.fg_of_isNoetherianRing, ?_, ?_, ?_, ?_⟩
  · intro n x a ha
    change AdicCompletion.evalₐ J n (eS (eP.symm (MvPowerSeries.C x))) = _
    rw [heS, heP n x a ha]
    change Ideal.Quotient.mk (J ^ n) (f (MvPolynomial.C a)) = _
    rw [show f (MvPolynomial.C a) = algebraMap R S a from f.commutes a]
  · intro x
    obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ Q 1 (eS.symm x))
    have hpx : AdicCompletion.evalₐ J 1 x = Ideal.Quotient.mk (J ^ 1) (f p) := by
      have := heS 1 (eS.symm x)
      rw [eS.apply_symm_apply, ← hp] at this
      exact this
    have hSres : AdicCompletion.evalOneₐ J x = residue S (f p) := by
      rw [← AdicCompletion.factorₐ_evalₐ_one, hpx]
      rfl
    change rR (AdicCompletion.evalOneₐ I
      (MvPowerSeries.constantCoeff (eP (eS.symm x)))) = _
    rw [hresP _ p hp.symm, hSres]
    exact (polynomial_chart_residue R S L rR rS hres d f hX p).symm
  · rw [← hQhat]
    rw [← IsLocalRing.map_ringEquiv_maximalIdeal e]
    exact (IsAdicComplete.congr_ringEquiv (maximalIdeal (AdicCompletion J S)) e).mpr
      (by infer_instance)
  · rw [← hQhat]
    infer_instance
  · rw [← AdicCompletion.maximalIdeal_eq_map, ← hQhat]
    exact IsLocalRing.map_ringEquiv_maximalIdeal e
  · have hP := MvPolynomial.combinedIdeal_associatedGraded R I d
    dsimp only at hP
    rw [← hQ] at hP
    obtain ⟨gP, hgP, hgPX⟩ := hP
    refine ⟨gP.trans gS, ?_, ?_⟩
    · intro n a ha hb
      have hca : MvPolynomial.C (σ := Fin d) a ∈ Q ^ n := by
        rw [hQ]
        exact Ideal.pow_right_mono le_sup_left n (by
          rw [← Ideal.map_pow]
          exact Ideal.mem_map_of_mem _ ha)
      change gS (gP (MvPolynomial.C _)) = _
      rw [hgP n a ha hca]
      change gS (DirectSum.of _ n (Submodule.Quotient.mk _)) = _
      change gS.toAddMonoidHom _ = _
      rw [hgS, Ideal.associatedGradedMap, DirectSum.map_of]
      apply congrArg (DirectSum.of _ n)
      change Submodule.Quotient.mk
        (⟨f (MvPolynomial.C a), _⟩ : (J ^ n : Ideal S)) = _
      congr 1
      exact Subtype.ext (f.commutes a)
    · intro i
      obtain ⟨z, hz⟩ := hgPX i
      refine ⟨Ideal.associatedGradedPieceMap f.toRingHom Q J hle 1 z, ?_⟩
      change gS (gP (MvPolynomial.X i)) = _
      rw [hz]
      change gS.toAddMonoidHom _ = _
      rw [hgS, Ideal.associatedGradedMap, DirectSum.map_of]
      rfl


end Algebra
