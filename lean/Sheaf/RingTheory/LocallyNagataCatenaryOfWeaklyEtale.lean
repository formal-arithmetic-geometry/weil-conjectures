/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Sheaf.RingTheory.ExcellentRing
public import Sheaf.RingTheory.IndPrincipalZariski
public import Sheaf.RingTheory.NagataRing
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Localization.Basic
import Sheaf.RingTheory.JapaneseDomain
import Sheaf.RingTheory.FiniteOverNagata
import Sheaf.RingTheory.LocalizationPrimeResidueFieldIso
import WeilConjectures.Mathlib.RingTheory.Etale.Weakly
import Sheaf.RingTheory.NagataLocalization
import Sheaf.RingTheory.PolynomialNagata
import Sheaf.RingTheory.WeaklyEtaleField
import Sheaf.RingTheory.NagataOfWeaklyEtale
import Sheaf.RingTheory.WeaklyEtaleLocalComponentDimension

/-!
# Local Nagata properties and universal catenarity under weakly etale maps

Source: Silvio Greco, Two theorems on excellent rings, Nagoya Mathematical Journal 60
(1976), Theorem 5.3(iii), pp. 146–147, with Remark 5.2 and the Foreword on p. 139
(blueprint: lem-exc-weakly-etale-locally-nagata-catenary).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace RingHom

/-- Universal catenarity and the Nagata property of every prime localization ascend
along a weakly etale homomorphism of commutative Noetherian rings.

Source: Greco, Two theorems on excellent rings, Theorem 5.3(iii), pp. 146–147;
Remark 5.2 identifies absolute flatness with weak etaleness for Noetherian rings
(blueprint: lem-exc-weakly-etale-locally-nagata-catenary).

Proof (the nine steps of the recorded DAG proof):
1. For $\mathfrak q\in\operatorname{Spec}B$, put $\mathfrak p=f^{-1}(\mathfrak q)$. Base change
   $A\to B$ to $A_{\mathfrak p}$ and then localize the target at the prime induced by $\mathfrak
   q$. The stability lemma and the weak etaleness of localization show that the resulting local
   map $A_{\mathfrak p}\to B_{\mathfrak q}$ is weakly etale. Explicitly $(B\otimes_A A_{\mathfrak
   p})_{\mathfrak q^{\prime}}\cong B_{\mathfrak q}$ by $b\otimes(a/s)\mapsto f(a)b/f(s)$; every
   denominator outside $\mathfrak p$ maps outside $\mathfrak q$. These localizations are
   Noetherian: every ideal is the extension of its contraction and fractions of finitely many
   generators of that contraction generate it.

2. The hypothesis supplies that $A_{\mathfrak p}$ is Nagata. Apply Nagata ascent to the Noetherian
   weakly etale map $A_{\mathfrak p}\to B_{\mathfrak q}$ from step 1. Thus $B_{\mathfrak q}$ is
   Nagata for each $\mathfrak q$, proving the local Nagata assertion without assuming that $A$
   itself is Nagata.

3. Fix $n\geq0$ and write $R=A[X_1,\ldots,X_n]$, $S=B[X_1,\ldots,X_n]=R\otimes_A B$. Both are
   Noetherian by finite-type Noetherianity, and $R\to S$ is weakly etale by base change. Here the
   tensor identification sends $h(X)\otimes b$ to $f(h)(X)b$; its inverse sends $\sum b_\alpha
   X^\alpha$ to $\sum X^\alpha\otimes b_\alpha$, so both composites fix coefficients and
   variables. Every finite type $R$-algebra is finite type over $A$ (adjoin its generators
   together with the $X_i$), so $R$ is universally catenary. It is also locally Nagata: for a
   prime $\mathfrak r\subset R$ with contraction $\mathfrak a\subset A$, $R_{\mathfrak r}$ is a
   localization of $A_{\mathfrak a}[X_1,\ldots,X_n]$. Its coefficient ring is Nagata by
   hypothesis, the polynomial ring is Nagata by $n$ applications of polynomial Nagata permanence,
   and the localization is Nagata. The fraction identification sends $a/s$ to the same fraction
   and fixes each $X_i$.

4. For any weakly etale map $R\to S$, distinct comparable primes of $S$ have distinct contractions
   to $R$. Indeed, base change to the residue field $k=\kappa(\mathfrak
   p)=\operatorname{Frac}(R/\mathfrak p)$ identifies primes over $\mathfrak p$ with primes of
   $F=S\otimes_R k$ (first quotient by $\mathfrak pS$, then invert $R\setminus\mathfrak p$). The
   weakly etale field lemma says that every singly generated $k$-subalgebra of $F$ is finite
   etale, hence finite dimensional: linear dependence of $1,x,x^2,\ldots$ makes each $x$ algebraic
   over $k$. Each prime quotient of $F$ is therefore an algebraic domain over $k$, hence a field:
   for a nonzero $x$, an algebraic equation of least degree has nonzero constant coefficient, and
   solving it expresses $x^{-1}$ as a polynomial in $x$. Thus all primes of $F$ are maximal, so
   comparable primes in a fibre coincide.

5. We will use the following elementary consequence of universal catenarity. If $H$ is universally
   catenary and $T\subset H$ is multiplicative, every polynomial ring $(T^{-1}H)[Y_1,\ldots,Y_m]$
   is $T^{-1}(H[Y_1,\ldots,Y_m])$, by sending each coefficient fraction $a/t$ to the same fraction
   and fixing the variables; a common denominator for the finitely many coefficients gives the
   inverse. The cited localization prime correspondence preserves every interval between its
   endpoint primes: every intervening prime is disjoint from $T$ because it is contained in the
   upper endpoint. Thus these polynomial localizations are catenary, since $H[Y_1,\ldots,Y_m]$ is
   catenary. Quotient prime intervals are also unchanged, since every prime between two primes
   containing an ideal $J$ contains $J$; every finite type algebra over $T^{-1}H$ is such a
   polynomial quotient. Consequently $T^{-1}H$ is universally catenary. The same finite type
   argument shows that every quotient of a universally catenary ring is universally catenary;
   Noetherianity of these rings follows by contracting ideals and extending their finite
   generators, and by lifting quotient ideals.

6. Let $\mathfrak Q\subsetneq\mathfrak Q^{\prime}$ be consecutive primes in a saturated chain of
   $S$, and put $\mathfrak p=\mathfrak Q\cap R$, $\mathfrak p^{\prime}=\mathfrak Q^{\prime}\cap
   R$. Step 4 gives $\mathfrak p\subsetneq\mathfrak p^{\prime}$. Set $C=R_{\mathfrak
   p^{\prime}}/\mathfrak pR_{\mathfrak p^{\prime}}\cong(R/\mathfrak p)_{\mathfrak
   p^{\prime}/\mathfrak p}$ and $D=S_{\mathfrak Q^{\prime}}/\mathfrak pS_{\mathfrak Q^{\prime}}$.
   By step 3, $R_{\mathfrak p^{\prime}}$ is Nagata; its quotient $C$ is Nagata by finite-over-
   Nagata permanence. It is a local domain by the displayed quotient-localization isomorphism. It
   is universally catenary by the quotient and localization arguments of step 5 applied to $R$.
   Its normalization in its fraction field is finite by the Nagata and Japanese definitions,
   taking the trivial finite field extension. Base change $R\to S$ along $R\to C$ to get $C\to
   C\otimes_R S=(S\otimes_R R_{\mathfrak p^{\prime}})/\mathfrak p(S\otimes_R R_{\mathfrak
   p^{\prime}})$; send $(r/s)\otimes b$ to $f(r)b/f(s)$ and then localize at the prime induced by
   $\mathfrak Q^{\prime}$. This gives exactly $D$, since all $s\in R\setminus\mathfrak p^{\prime}$
   have image outside $\mathfrak Q^{\prime}$ and the final denominators are precisely those
   outside that prime. Base-change stability and weak etaleness of localization therefore give a
   local weakly etale map $C\to D$: the maximal ideals are the images of $\mathfrak p^{\prime}$
   and $\mathfrak Q^{\prime}$, and their contraction equality is exactly $\mathfrak Q^{\prime}\cap
   R=\mathfrak p^{\prime}$. The target is Noetherian local: localizing preserves finite generation
   of ideals as in step 1, and taking a quotient preserves it by lifting an ideal.

7. The prime $P=\mathfrak QS_{\mathfrak Q^{\prime}}/\mathfrak pS_{\mathfrak Q^{\prime}}$ is
   minimal in $D$. A prime of $D$ contained in $P$ corresponds to a prime $\mathfrak
   T\subseteq\mathfrak Q$ of $S$ containing $\mathfrak pS$; its contraction is both contained in
   and contains $\mathfrak p$, hence equals $\mathfrak p$. Step 4 forces $\mathfrak T=\mathfrak
   Q$. Prime correspondence also identifies $D/P$ with $S_{\mathfrak Q^{\prime}}/\mathfrak
   QS_{\mathfrak Q^{\prime}}$: it has exactly the two primes coming from $\mathfrak Q$ and
   $\mathfrak Q^{\prime}$, so its Krull dimension is $1$. Apply the local component dimension
   lemma to the map $C\to D$ prepared in step 6 and the minimal prime $P$. It gives $\dim C=1$.
   Primes of $C$ correspond to primes of $R$ between $\mathfrak p$ and $\mathfrak p^{\prime}$; an
   intermediate prime would give a chain of length $2$, contradicting $\dim C=1$. Thus the
   contracted adjacent primes are consecutive.

8. For fixed endpoints $\mathfrak Q_0\subseteq\mathfrak Q_1$ in $S$, contraction sends every
   finite strict chain between them to a strict chain of the same length in $R$ by step 4.
   Catenarity of $R$ therefore bounds all these lengths. A finite chain can be refined to a
   saturated chain by inserting primes; the bound makes this process terminate. Steps 6–7 show
   that every saturated chain contracts to a saturated chain with the same fixed contracted
   endpoints. All those chains have the same length because $R$ is catenary. Hence $S$ is
   catenary. Equal endpoints have only the length-zero chain. If $S$ has no primes the assertion
   is vacuous.

9. Every finite type $B$-algebra is a quotient of some $B[X_1,\ldots,X_n]$, which is catenary by
   steps 3–8. Such a quotient is catenary: primes of $S/J$ correspond by inverse image to primes
   of $S$ containing $J$; every prime between two such primes also contains $J$, so the
   corresponding intervals and their saturated chains agree exactly. The same chain bounds and
   lengths apply. Thus all finite type $B$-algebras are catenary, which is universal catenarity of
   $B$. Together with step 2 this proves both assertions. -/
theorem isUniversallyCatenary_and_locallyNagata_of_weaklyEtale
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] (f : A →+* B) (hf : f.WeaklyEtale)
    (hA : ∀ (p : Ideal A) [p.IsPrime], IsNagataRing (Localization.AtPrime p))
    (hcat : IsUniversallyCatenary A) :
    IsUniversallyCatenary B ∧
      ∀ (q : Ideal B) [q.IsPrime], IsNagataRing (Localization.AtPrime q) := by
  sorry

end RingHom
