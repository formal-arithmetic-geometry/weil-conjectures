/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q18
-/
module

public import WeilConjectures.RingTheory.AssociatedGradedRing
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.LocalRing.Module
import WeilConjectures.RingTheory.AdicCompletionNoetherianOfQuotient
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.Completeness
import WeilConjectures.RingTheory.CompletionRegularLocal
import WeilConjectures.RingTheory.CompletionDimensionEquality
import WeilConjectures.RingTheory.LocalCompletionQuotient
import Mathlib.RingTheory.AdicCompletion.Exactness
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import WeilConjectures.RingTheory.ExistsCoefficientSubring
import Sheaf.RingTheory.RegularCompleteCoefficientCoordinates
import WeilConjectures.RingTheory.PowerSeriesAdicEvaluation

/-! # Bennett's numerical criterion for normal flatness

Source: Cossart--Jannsen--Saito, March 12, 2009 preprint, Theorem 2.3(1) iff (2),
printed p.29, citing Bennett, Theorem (3). ILO VIII 2.3.13, printed p.94, supplies
motivation (blueprint: lem-trf-bennett-normal-flat-numerical-criterion).

The displayed summation operator acts on extended-natural-valued sequences so that
`Module.length` is used without truncation. All the lengths here are finite. The
natural number `d`, identified with the Krull dimension by `hd`, names the finite
dimension of the regular local quotient. The source's degree-wise Hilbert functions
become these quotient lengths after one inclusive summation.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Ideal

/-- The associated graded ring along a regular prime is flat precisely when the
Hilbert--Samuel quotient-length sequence is the dimension-fold inclusive summation
of the corresponding sequence at the prime localization.
Source: Cossart--Jannsen--Saito, March 12, 2009 preprint, Theorem 2.3(1) iff (2),
printed p.29; Bennett, Theorem (3)
(blueprint: lem-trf-bennett-normal-flat-numerical-criterion).

Proof: the DAG supplies the following equicharacteristic argument. Its supporting
lemmas are imported above as proof dependencies.
1. Put $k=R/\mathfrak m$, $\mathfrak a=\mathfrak m/I$, $K=\operatorname{Frac}(A)$, and
   $G_j=I^j/I^{j+1}$. The ring $A$ is a domain by [lem-sc-regular-local-domain]. Each $I^j$ is
   finite over $R$ by [lem-weil-pbc-noetherian-submodule-finite], so $G_j$ is finite over $A$,
   since $I$ annihilates it. Define $r_j=\dim_K(K\otimes_A G_j)$ and $\mu_j=\dim_k(G_j/\mathfrak
   aG_j)$. Localize $0\to I^{j+1}\to I^j\to G_j\to0$ at $R\setminus I$ using
   [lem-weil-pbc-localization-module-exact]. The localized quotient of $R/I$ is $K$, so
   $$K\otimes_A G_j\simeq (IR_I)^j/(IR_I)^{j+1}.$$ Thus $r_j=g_{R_I}(j)$, where
   $g_T(j)=\dim_{T/\mathfrak m_T}\mathfrak m_T^j/\mathfrak m_T^{j+1}$. All these dimensions are
   finite. Uses: lem-sc-regular-local-domain, lem-weil-pbc-noetherian-submodule-finite,
   lem-weil-pbc-localization-module-exact.

2. For later use, a finite $A$-module $M$ with $r=\dim_K(K\otimes_A M)$ and
   $\mu=\dim_k(M/\mathfrak aM)$ is free if $\mu=r$. Indeed, lifts of a residue basis give a
   surjection $A^\mu\to M$ by [lem-weil-pbc-nakayama-local-generators]. If $L$ is its kernel,
   [lem-weil-pbc-localization-module-exact] makes $K\otimes_A L$ the kernel of a surjection
   between $K$-spaces of the same dimension, hence zero. An element of $L\subseteq A^\mu$ which
   vanishes after localization is killed by a nonzero element of the domain $A$, and therefore is
   zero coordinate by coordinate. Thus $L=0$. Conversely $M\simeq A^r$ has $\mu=r$, directly from
   the standard basis. This includes rank zero. Uses: lem-weil-pbc-nakayama-local-generators,
   lem-weil-pbc-localization-module-exact.

3. For $T=R$ or $R_I$, the filtration of $T/\mathfrak m_T^{n+1}$ by its maximal-ideal powers has
   successive factors $\mathfrak m_T^j/\mathfrak m_T^{j+1}$ for $0\le j\le n$. A basis of each
   such residue-field vector space gives a composition series with that many one-dimensional
   simple factors. Repeated use of [lem-weil-pbc-length-additive-short-exact] therefore gives
   $h_T=\Lambda g_T$. On integer sequences set $\Delta f(0)=f(0)$ and $\Delta f(n)=f(n)-f(n-1)$
   for $n>0$. Telescoping gives $\Delta\Lambda f=f=\Lambda\Delta f$. Consequently the desired
   numerical equality is equivalent to $$g_R=\Lambda^d r,\qquad r(j)=r_j.$$ This equivalence
   concerns all entries, not just eventual Hilbert polynomials. Uses:
   lem-weil-pbc-length-additive-short-exact.

4. Write $C=\widehat R$ for maximal-ideal completion, $J=IC$, $D=\widehat A$, $\mathfrak
   n=\mathfrak mC$, and $\mathfrak p=\mathfrak aD$. By
   [lem-weil-pbc-completion-noetherian-quotient-noetherian] both completions are Noetherian and
   complete. By [lem-weil-pbc-local-completion-local-ring] they are local with maximal ideals
   $\mathfrak n,\mathfrak p$ and common residue field $k$. By
   [lem-weil-pbc-adic-completion-mod-power], $C/\mathfrak n^q\simeq R/\mathfrak m^q$ for all
   $q\ge1$. Taking kernels of successive quotient maps gives $g_C=g_R$. The ring $D$ is regular by
   [lem-weil-pbc-completion-regular-local] and has dimension $d$ by
   [lem-weil-pbc-completion-dimension-eq]. No completion of $R_I$ is used. Uses:
   lem-weil-pbc-completion-noetherian-quotient-noetherian,
   lem-weil-pbc-local-completion-local-ring, lem-weil-pbc-adic-completion-mod-power,
   lem-weil-pbc-completion-regular-local, lem-weil-pbc-completion-dimension-eq.

5. The quotient-completion map of [lem-weil-pbc-local-completion-quotient] identifies $C/J=D$, and
   identifies the image of the completion of $I^j\hookrightarrow R$ with $I^jC=J^j$. Exact
   completion [lem-weil-pbc-completion-exact-finite-modules] applied to $0\to I^{j+1}\to I^j\to
   G_j\to0$ therefore identifies $$H_j:=J^j/J^{j+1}\simeq\widehat{G_j}\simeq D\otimes_A G_j.$$ For
   the last isomorphism use [lem-weil-pbc-completion-finite-module-tensor] over $A$: the
   $\mathfrak m$-adic filtration on $G_j$ equals its $\mathfrak a$-adic filtration since $IG_j=0$.
   The reduction statement of [lem-weil-pbc-module-completion-complete] gives $H_j/\mathfrak
   pH_j\simeq G_j/\mathfrak aG_j$. In particular, if $G_j\simeq A^{r_j}$ then $H_j\simeq D^{r_j}$,
   while $\dim_k H_j/\mathfrak pH_j=\mu_j$ without any freeness assumption. Uses:
   lem-weil-pbc-local-completion-quotient, lem-weil-pbc-completion-exact-finite-modules,
   lem-weil-pbc-completion-finite-module-tensor, lem-weil-pbc-module-completion-complete.

6. Choose a coefficient ring $k_0\subset C$ by [lem-weil-pbc-cohen-coefficient-ring-exists].
   Because $C$ contains the field $F$, its characteristic equals the characteristic of its residue
   field. The coefficient ring's maximal ideal $p k_0$ is consequently zero, so $k_0$ is a field
   and $k_0\simeq k$. Its image in $D$ is again a coefficient field. Choose $d$ generators $\bar
   t_1,\ldots,\bar t_d$ of $\mathfrak p$. By [lem-trf-regular-complete-coefficient-coordinates],
   $\theta:k_0[[T_1,\ldots,T_d]]\to D$, $T_i\mapsto\bar t_i$, is an isomorphism. Lift them to
   $t_i\in\mathfrak n$ and use [lem-weil-pbc-power-series-adic-evaluation] to obtain
   $E:k_0[[T]]\to C$. The composite of $E$ with $C\to D$ is $\theta$ by the explicit evaluation
   formula. Thus $s=E\theta^{-1}:D\to C$ is a section. Regard $D$ as a subring by $s$; then
   $\mathfrak n=J+\mathfrak pC$. No $F$-linearity of this section, and no separability of $k/F$,
   is asserted or needed. Uses: lem-weil-pbc-cohen-coefficient-ring-exists,
   lem-trf-regular-complete-coefficient-coordinates, lem-weil-pbc-power-series-adic-evaluation.

7. Fix $N\ge1$ and suppose that $G_j$ is free over $A$ for all $j<N$. We calculate degree $N$
   without assuming $G_N$ free. Put $B=C/J^{N+1}$ and $Q=JB$. The section in step 6 makes $B$ a
   $D$-algebra with $B/Q=D$ and $Q^{N+1}=0$. Its successive quotients $Q^j/Q^{j+1}=H_j$ are
   $D$-free for $j<N$, by step 5. For each such $j$, lift a $D$-basis of $H_j$ into $Q^j$, and let
   $E_j$ be its $D$-span. The projection $E_j\to H_j$ is an isomorphism: projecting any relation
   proves all coefficients zero. Subtracting the lifted basis expansion from an element of $Q^j$
   then gives $$Q^j=E_j\oplus Q^{j+1}.$$ Iterating this finite decomposition, with $M=Q^N=H_N$,
   gives, for $0\le a\le N$, $$Q^a=M\oplus\bigoplus_{a\le j<N}E_j,\qquad E_j\simeq D^{r_j}.$$
   Every splitting here is a splitting of modules by explicit basis lifts; it need not respect
   multiplication.

8. Let $\mathfrak b=\mathfrak nB=Q+\mathfrak pB$. Expanding a power of the sum of two ideals
   gives, for every $q\ge0$, $$\mathfrak b^q=\sum_{a=0}^{\min(q,N)}\mathfrak p^{q-a}Q^a.$$ Insert
   the direct decompositions of step 7. On the summand $E_j$ the smallest exponent of $\mathfrak
   p$ occurs at $a=\min(q,j)$; on $M$ it occurs at $a=\min(q,N)$. The powers of $\mathfrak p$ are
   nested, so the sum on each summand equals the term with that smallest exponent. Thus, inside
   the fixed direct sum for $B$, $$\mathfrak b^q=\mathfrak p^{\max(q-N,0)}M\ \oplus\
   \bigoplus_{j<N}\mathfrak p^{\max(q-j,0)}E_j.$$ In particular, at $q=N$ and $q=N+1$ this gives
   $$\mathfrak b^N/\mathfrak b^{N+1}\simeq M/\mathfrak pM\ \oplus\ \bigoplus_{j<N}(\mathfrak
   p^{N-j}/\mathfrak p^{N-j+1})^{r_j}.$$ Only the modules $E_j$, not the final module $M$, were
   assumed free.

9. Define $c_d(q)$ to be the number of monomials of total degree $q$ in $d$ variables. Thus
   $c_0(0)=1$ and $c_0(q)=0$ for $q>0$. Under $D\simeq k_0[[T_1,\ldots,T_d]]$, $\mathfrak p^q$
   consists precisely of series with no term below degree $q$: for the reverse inclusion assign
   each exponent of degree at least $q$ to one of its degree-$q$ divisors and factor out that
   monomial, using only finitely many degree-$q$ divisors. Coefficient extraction therefore
   identifies $\mathfrak p^q/\mathfrak p^{q+1}$ with the vector space on the degree-$q$ monomials,
   of dimension $c_d(q)$. Since $J^{N+1}\subset\mathfrak n^{N+1}$, passage from $C$ to $B$ does
   not change degree $N$ of the maximal-ideal graded ring. Steps 4, 5 and 8 now give the finite
   formula $$g_R(N)=\mu_N+\sum_{j<N}r_jc_d(N-j)\quad\text{whenever every }G_j\text{ with
   }j<N\text{ is free}.$$ This is the calculation needed for the induction, not an appeal to the
   numerical normal-flatness criterion.

10. For any sequence $r$, define its convolution with $c_d$ in degree $n$ by $\sum_{j=0}^n
   r_jc_d(n-j)$. A monomial in $d+1$ variables is uniquely a monomial in $d$ variables times a
   power of the last variable, whence $c_{d+1}(q)=\sum_{i=0}^q c_d(i)$. Interchanging two finite
   sums shows that replacing $c_d$ by $c_{d+1}$ replaces the convolution by its partial sums.
   Starting with $c_0$ therefore gives $$(\Lambda^d r)(n)=\sum_{j=0}^n r_jc_d(n-j).$$ In
   particular, $c_d(0)=1$ for every $d\ge0$, so the coefficient of $r_n$ is always one. This
   includes $d=0$.

11. Assume $G=\operatorname{gr}_I R$ is flat over $A$. Each $G_j$ is a direct summand of $G$. It
   is flat: for an injection $U\hookrightarrow V$, a kernel element in $U\otimes_A G_j$ embeds by
   the split inclusion in $U\otimes_A G$, where it is zero by flatness, and the split projection
   gives its original value zero. Each $G_j$ is finite by step 1, so
   [lem-weil-pbc-finite-flat-local-free] makes it free over the local ring $A$. Its rank is $r_j$
   after tensoring with $K$, and hence $\mu_j=r_j$. Apply the formula of step 9 for every $N\ge1$
   and step 10 to obtain $g_R(N)=(\Lambda^d r)(N)$. Degree zero also agrees: $g_R(0)=1=r_0$. Thus
   $g_R=\Lambda^d r$, and step 3 yields $h_R=\Lambda^d h_{R_I}$. Uses:
   lem-weil-pbc-finite-flat-local-free.

12. Conversely, assume $h_R=\Lambda^d h_{R_I}$, so $g_R=\Lambda^d r$ by step 3. We prove by
   induction on $N$ that $G_N$ is free of rank $r_N$. At $N=0$, $G_0=A$ and $r_0=1$. If all
   degrees below $N\ge1$ are free, steps 9 and 10 give
   $$\mu_N+\sum_{j<N}r_jc_d(N-j)=g_R(N)=(\Lambda^d r)(N)=r_N+\sum_{j<N}r_jc_d(N-j).$$ Cancel the
   finite sum to get $\mu_N=r_N$. The explicit kernel argument in step 2 makes $G_N$ free of rank
   $r_N$, completing the induction. The induction uses no assumed freeness in degree $N$; that
   degree was the unrestricted summand $M$ in steps 7--9.

13. Choose the bases just obtained for all $G_j$. Their disjoint union, with each vector labelled
   by its degree, is an $A$-basis of $G=\bigoplus_jG_j$, since every element of a direct sum has
   finite support and relations separate degree by degree. For an injection $U\hookrightarrow V$,
   the basis identifies tensoring with $G$ with a direct sum of copies of that injection. A
   finite-support tuple which maps to zero has every coordinate zero; hence this direct sum map is
   injective. This is exactly the flatness required in the statement. Both implications are now
   established. No nontrivial-centre hypothesis occurred, so the proof also applies to $I=0$; if
   $I=\mathfrak m$, then $d=0$ and the numerical assertion is the identity $h_R=h_R$.
-/
theorem bennett_normal_flat_numerical_criterion
    {F : Type u} [Field F] {R : Type v} [CommRing R] [Algebra F R]
    [Algebra.EssFiniteType F R] [IsReduced R] [IsNoetherianRing R] [IsLocalRing R]
    (I : Ideal R) [I.IsPrime] (hI : I ≤ IsLocalRing.maximalIdeal R)
    [IsRegularLocalRing (R ⧸ I)] (d : ℕ)
    (hd : ringKrullDim (R ⧸ I) = (d : WithBot ℕ∞)) :
    Module.Flat (R ⧸ I) (associatedGraded I) ↔
      (fun n : ℕ ↦ Module.length R (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1))) =
        ((fun (f : ℕ → ℕ∞) (n : ℕ) ↦ ∑ j ∈ Finset.range (n + 1), f j)^[d])
          (fun n : ℕ ↦ Module.length (Localization.AtPrime I)
            (Localization.AtPrime I ⧸
              IsLocalRing.maximalIdeal (Localization.AtPrime I) ^ (n + 1))) := by
  sorry

end Ideal
