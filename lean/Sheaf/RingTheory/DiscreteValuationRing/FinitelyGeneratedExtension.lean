module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.RingTheory.LocalRing.LocalSubring
public import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.FieldTheory.FinTrdeg
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.AlgebraicIndependent.Defs
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import WeilConjectures.AlgebraicGeometry.IntegralClosureDedekindSurjectiveFibres
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.Defs
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.DedekindDomain.Dvr

/-!
# A dominating DVR in a finitely generated field extension

Source: Stacks Project, Algebra, Tag 00PH, `lemma-exists-dvr`
(blueprint: lem-sfb-local-domain-fg-field-dvr).
-/

@[expose] public section

universe u v w

/-- A nonfield Noetherian local domain is dominated by a DVR inside any prescribed
finitely generated extension of its fraction field, with that extension as fraction field.
The equation of ring maps fixes the inclusion of the original domain into that same field.

Source: Stacks Project, Algebra, Tag 00PH, `lemma-exists-dvr`.
(blueprint: lem-sfb-local-domain-fg-field-dvr).

Proof (the eight steps of the node, following all three paragraphs of Tag 00PH):
1. Write $L=K(a_1,\ldots,a_n)$. By
   [lem-weil-pbc-finitely-generated-field-finite-transcendence-basis], choose a finite
   transcendence basis $x_1,\ldots,x_r$ and put $K_0=K(x_1,\ldots,x_r)\subseteq L$. Thus the $x_i$
   are algebraically independent over $K$ and $L/K_0$ is algebraic. Also $L=K_0(a_1,\ldots,a_n)$:
   the right side contains $K$ and all the original generators, and is contained in $L$. Each
   $a_i$ is algebraic over $K_0$, so [lem-weil-pbc-algebraic-generators-finite-extension] gives
   $[L:K_0]<\infty$. This includes $r=0$, when $K_0=K$.

2. Let $P=R[x_1,\ldots,x_r]\subseteq K_0$. The polynomial-ring evaluation map
   [def-weil-pbc-mv-polynomial-ring] is injective: by algebraic independence
   [def-weil-pbc-transcendence-basis], a polynomial over $K$ vanishing at the $x_i$ has every
   coefficient zero, and $R\subseteq K$ is injective. Hence $P$ is a polynomial ring over $R$, and
   [lem-weil-pbc-finite-type-algebra-noetherian] makes it Noetherian. The map $P\to R/\mathfrak
   m_R$ sending every $x_i$ to zero and each coefficient to its residue is surjective. Its kernel
   is $\mathfrak n=(\mathfrak m_R,x_1,\ldots,x_r)$: a polynomial lies in the kernel exactly when
   its constant coefficient is in $\mathfrak m_R$, and its remaining monomials are multiples of
   the $x_i$. As the quotient is a field, $\mathfrak n$ is maximal and $\mathfrak n\cap
   R=\mathfrak m_R$.

3. Set $B=P_{\mathfrak n}$ [def-weil-pbc-localization-at-prime]. Concretely regard it as the
   subring $\{p/s:p,s\in P,\ s\notin\mathfrak n\}$ of $K_0$: all such denominators are nonzero,
   and equality of fractions is checked by cross multiplication in the domain $P$. It is local
   with maximal ideal $\mathfrak nB$, and [lem-weil-pbc-localization-noetherian] makes it
   Noetherian. For $p\notin\mathfrak n$, $p/1$ is a unit with inverse $1/p$; for $p\in\mathfrak
   n$, $p/1\in\mathfrak nB$. Thus $\mathfrak m_B\cap P=\mathfrak n$ and $\mathfrak m_B\cap
   R=\mathfrak m_R$. Fix $0\ne t\in\mathfrak m_R$; it remains nonzero in $B$ and belongs to
   $\mathfrak m_B$, so $B$ is not a field. The fraction field of $P$, hence of $B$, is exactly
   $K_0$: the field of ratios of $P$ contains all ratios from $R$, hence $K$, and the $x_i$, hence
   $K_0$; conversely all these ratios lie in $K_0$. For $r=0$ this construction gives $B=R$.

4. Apply [lem-sfb-local-domain-birational-dimension-one] to $B\subseteq K_0$. Its hypotheses hold
   by step 3. Obtain $B\subseteq D\subseteq K_0$ with $D$ a Noetherian local integral domain of
   dimension $1$, fraction field $K_0$, and $\mathfrak m_D\cap B=\mathfrak m_B$. In particular
   $t\ne0$ belongs to $\mathfrak m_D$, and contracting once more gives $\mathfrak m_D\cap
   R=\mathfrak m_R$. The finite extension $L/K_0$ from step 1 is unchanged by this replacement of
   the local ring.

5. Let $C\subseteq L$ be the integral closure of $D$ in $L$ [def-weil-pbc-integral-closure]. Apply
   [lem-sc-integral-closure-dedekind-surjective-fibres] to the Noetherian domain $D$ of dimension
   $1$, with fraction field $K_0$ and finite extension $L/K_0$. It gives that $C$ is a Noetherian
   integrally closed domain of dimension $1$, and that
   $\operatorname{Spec}C\to\operatorname{Spec}D$ is surjective. Choose a prime $\mathfrak q\subset
   C$ contracting to $\mathfrak m_D$. Independently
   [lem-weil-pbc-integral-closure-finite-extension-normal], under the same finite-extension
   hypotheses, gives that the given field $L$ is the fraction field of $C$. Thus the required
   field is retained, even when $L/K_0$ is inseparable.

6. The prime $\mathfrak q$ is nonzero because it contains the nonzero element $t\in\mathfrak m_D$.
   It is maximal: if a proper prime strictly containing it existed, the chain
   $(0)\subsetneq\mathfrak q\subsetneq\mathfrak p$ in the domain $C$ would contradict $\dim C=1$.
   Equivalently, taking a maximal ideal containing $\mathfrak q$ forces equality by this chain
   argument. Thus $\mathfrak q$ is a nonzero maximal ideal of the Dedekind domain $C$.

7. Set $A=C_{\mathfrak q}$ [def-weil-pbc-localization-at-prime]. Since $C$ is a normal domain with
   fraction field $L$ and $0\notin C\setminus\mathfrak q$,
   [lem-weil-pbc-localization-normal-domain] embeds $A$ into $L$ by $c/s\mapsto c/s$ and states
   that its fraction field is $L$. Since $C$ is a Noetherian integrally closed domain of dimension
   $1$ and $\mathfrak q$ is maximal, [lem-sc-dedekind-localization-dvr] gives that $A$ is a
   discrete valuation ring. We have the inclusions $R\subseteq B\subseteq D\subseteq C\subseteq
   A\subseteq L$.

8. By [def-weil-pbc-localization-at-prime], $\mathfrak m_A=\mathfrak qC_{\mathfrak q}$. If
   $c\in\mathfrak q$, then $c/1\in\mathfrak m_A$; if $c\notin\mathfrak q$, then $c/1$ has inverse
   $1/c$ in $A$, so is not in its proper maximal ideal. Hence $\mathfrak m_A\cap C=\mathfrak q$.
   Contracting through the inclusions yields $\mathfrak m_A\cap R=(\mathfrak q\cap D)\cap
   R=\mathfrak m_D\cap R=\mathfrak m_R$. Together with step 7 this proves every required clause,
   including that each element of $L$ is a quotient of elements of this very subring $A$.
-/
theorem IsLocalRing.exists_discreteValuationSubring_of_fg_extension
    (R : Type u) (K : Type v) (L : Type w)
    [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [Field K] [Field L] [Algebra R K] [IsFractionRing R K] [Algebra K L]
    (hR : ¬ IsField R) (hL : (⊤ : IntermediateField K L).FG) :
    ∃ (A : LocalSubring L) (f : R →+* A.toSubring),
      IsDiscreteValuationRing A.toSubring ∧ IsFractionRing A.toSubring L ∧
        A.toSubring.subtype.comp f = (algebraMap K L).comp (algebraMap R K) ∧
        Ideal.comap f (IsLocalRing.maximalIdeal A.toSubring) = IsLocalRing.maximalIdeal R := by
  sorry
