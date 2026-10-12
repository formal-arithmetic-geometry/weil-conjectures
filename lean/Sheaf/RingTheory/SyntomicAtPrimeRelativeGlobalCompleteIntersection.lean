/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.RingHom.Flat
public import Sheaf.RingTheory.CompleteIntersectionOverField
public import Sheaf.Paper.RelativeGlobalCompleteIntersectionPresentation
import Sheaf.RingTheory.EquationCountLocalizeRelativeGlobalCompleteIntersection
import Sheaf.RingTheory.GlobalCompleteIntersectionPrincipalLocalization
import Sheaf.RingTheory.LciConormalFreeRankCodimension
import Sheaf.RingTheory.LocalizationPrimeResidueFieldIso
import Sheaf.RingTheory.PolynomialQuotientDimensionAtPointHeightDifference
import Sheaf.RingTheory.RelativeGlobalCompleteIntersectionPrincipalLocalization
import WeilConjectures.Mathlib.Topology.KrullDimension

/-!
# Syntomic at a prime: a relative global complete intersection neighbourhood

Source: Stacks Project, Algebra, Lemma 00SY, implication (3) ⇒ (2), with Lemma 00SG
for the complete-intersection fibre condition
(blueprint: lem-weil-pbc-syntomic-at-prime-relative-global-complete-intersection).
-/

@[expose] public section

universe u v

namespace Algebra

/-- A ring map finitely presented near a prime, flat on the induced local rings, and with
complete-intersection fibre near the canonical fibre prime admits a relative global complete
intersection presentation after a principal localization outside the prime.
Source: Stacks Project, Algebra, Lemma 00SY, implication (3) ⇒ (2), and Lemma 00SG.
(blueprint: lem-weil-pbc-syntomic-at-prime-relative-global-complete-intersection).

The algebra structure represents the arbitrary ring map. The fibre is Mathlib's
`κ(p) ⊗[R] S`, identified by tensor symmetry with the source's `S ⊗[R] κ(p)`.
`PrimeSpectrum.preimageEquivFiber` constructs precisely the kernel of the natural map
from this fibre to `κ(q)`.

Proof (the node's complete argument):
1. (Reduction to $S$ finitely presented.) Let $g_0\in S\setminus\mathfrak q$ be as in hypothesis
(1), $S_1=S_{g_0}$ and $\lambda:S\to S_1$ the localization map [def-weil-ring-localization-away].
By [lem-weil-pbc-localization-prime-residue-field-iso] (1)-(3) (with $W=\{g_0^N\}$, disjoint from
$\mathfrak q$), $\mathfrak q_1=\mathfrak qS_1$ is a prime of $S_1$ with $\lambda^{-1}(\mathfrak
q_1)=\mathfrak q$ (so its inverse image in $R$ is $\mathfrak p$), $S_{\mathfrak
q}\to(S_1)_{\mathfrak q_1}$ is an isomorphism of $S$-algebras and $\kappa(\mathfrak
q)\cong\kappa(\mathfrak q_1)$ compatibly with $\lambda$. Hence $R_{\mathfrak p}\to(S_1)_{\mathfrak
q_1}$ is the flat map of hypothesis (2) followed by an isomorphism, so it is flat
[def-weil-pbc-flat-ring-map]. By [lem-weil-pbc-localization-tensor-over-base] (with $A=M=S$,
$T=\{g_0^N\}$, $N=k:=\kappa(\mathfrak p)$) the fibre ring $F_1=S_1\otimes_Rk$ is isomorphic, as a
$k$-algebra under $F$, to $F_{\bar g_0}$, $\bar g_0=g_0\otimes1$; $\bar g_0\notin\mathfrak Q$
since $g_0$ has nonzero image in $\kappa(\mathfrak q)$. The map $F_{\bar g_0}\to\kappa(\mathfrak
q)$ extending $F\to\kappa(\mathfrak q)$ has a prime kernel whose inverse image in $F$ is
$\mathfrak Q$, so by [lem-weil-pbc-localization-prime-residue-field-iso] (1) this kernel is
$\mathfrak QF_{\bar g_0}$, and it corresponds to the kernel $\mathfrak Q_1$ of
$F_1\to\kappa(\mathfrak q_1)$. With $h$ from hypothesis (3), $h/1\notin\mathfrak QF_{\bar g_0}$
(its inverse image is $\mathfrak Q\not\ni h$), and $(F_{\bar g_0})_{h/1}\cong F_{\bar
g_0h}\cong(F_h)_{\bar g_0/1}$ as $k$-algebras by [lem-weil-pbc-localization-of-localization] (part
(1) applied to both composites: each is a localization of $F$ at the saturation of $\{(\bar
g_0h)^N\}$, as $\bar g_0h$ becomes a unit, every element is $x/(\bar g_0h)^N$ after multiplying
numerator and denominator by a power of the other factor, and the kernels agree). $F_h$ is a
global complete intersection over $k$ by (3), so $(F_h)_{\bar g_0/1}$ is one by
[lem-weil-pbc-global-complete-intersection-principal-localization], and the definition
[def-weil-pbc-complete-intersection-over-field] is invariant under $k$-algebra isomorphism. Thus
$S_1$, $\mathfrak q_1$ satisfy (1) (with $g=1$: $S_1$ is finitely presented), (2) and (3).
Conversely, if the conclusion holds for $S_1,\mathfrak q_1$ with $g_1'\in S_1\setminus\mathfrak
q_1$, write $g_1'=s/g_0^m$ ($s\in S$); then $s\notin\mathfrak q$, $g'=g_0s\notin\mathfrak q$, and
$(S_1)_{g_1'}\cong S_{g'}$ as $R$-algebras by [lem-weil-pbc-localization-of-localization]
($g_0s\mapsto g_0^{m+1}g_1'$ is a unit, $(x/g_0^l)/(s/g_0^m)^j=xg_0^{mj}s^lg_0^j/(g_0s)^{l+j}$,
and kernels are killed by powers of $g_0s$). So we may and do assume that $S$ is a finitely
presented $R$-algebra.

2. (Presentation and the fibre.) By [def-weil-pbc-finitely-presented-algebra] choose $n\ge0$ and
$a_1,\dots,a_m\in P=R[x_1,\dots,x_n]$ [def-weil-pbc-mv-polynomial-ring] with $S\cong P/I$,
$I=(a_1,\dots,a_m)$; let $\pi:P\to S$ be the quotient map and $\mathfrak q'=\pi^{-1}(\mathfrak
q)$, a prime of $P$ containing $I$ whose inverse image in $R$ is $\mathfrak p$. Let $\rho:P\to
k[x_1,\dots,x_n]$ be the coefficient reduction along $R\to R_{\mathfrak p}\to k$; $\ker(R\to
k)=\mathfrak p$. Let $\bar I=(\rho(a_1),\dots,\rho(a_m))\subseteq k[x_1,\dots,x_n]$, the ideal
generated by $\rho(I)$. By [lem-weil-pbc-polynomial-scalar-extension] $P\otimes_Rk\cong
k[x_1,\dots,x_n]$, $p\otimes\lambda\mapsto\lambda\rho(p)$, and by associativity of $\otimes$ and
[lem-weil-pbc-tensor-quotient-base-change] (with $A=P$, $B=k[x_1,\dots,x_n]$)
$F=(P/I)\otimes_Rk\cong k[x_1,\dots,x_n]/\bar I=:\bar F$ as $k$-algebras, $(a\bmod
I)\otimes\lambda\mapsto\lambda\rho(a)\bmod\bar I$. Let $\bar{\mathfrak Q}\subset\bar F$ be the
image of $\mathfrak Q$ and $\bar{\mathfrak q}'\subset k[x_1,\dots,x_n]$ its inverse image, i.e.
the kernel of the $k$-algebra map $\psi:k[x_1,\dots,x_n]\to\bar F\cong F\to\kappa(\mathfrak q)$;
it is a prime containing $\bar I$, and $\psi(x_i)$ is the class of $\pi(x_i)$ in $\kappa(\mathfrak
q)$. For $a\in P$, $\psi(\rho(a))$ is the image of $(\pi(a))\otimes1$ in $\kappa(\mathfrak q)$,
i.e. the class of $\pi(a)$, which vanishes iff $\pi(a)\in\mathfrak q$; hence
$\rho^{-1}(\bar{\mathfrak q}')=\mathfrak q'$, so $\rho(P\setminus\mathfrak q')\subseteq
k[x_1,\dots,x_n]\setminus\bar{\mathfrak q}'$.

3. (The conormal module of the fibre at $\bar{\mathfrak Q}$ is free of rank $c$.) By hypothesis
(3) there is $h\in F\setminus\mathfrak Q$ with $F_h$ a global complete intersection over $k$; its
image $\bar h\in\bar F\setminus\bar{\mathfrak Q}$ has $\bar F_{\bar h}\cong F_h$ as $k$-algebras,
so $\bar F_{\bar h}$ is a global complete intersection
[def-weil-pbc-complete-intersection-over-field]. Apply
[lem-weil-pbc-lci-conormal-free-rank-codimension] to $k$, $n$, the ideal $\bar I\subseteq
k[x_1,\dots,x_n]$, $\bar F=k[x_1,\dots,x_n]/\bar I$, the prime $\bar{\mathfrak Q}$ and the element
$\bar h$: $d:=\dim_{\bar{\mathfrak Q}}(\operatorname{Spec}\bar F)$
[def-kun-topological-dimension-at-point] is an integer with $0\le d\le n$, and with $c:=n-d$ the
localization $(\bar I/\bar I^2)_{\bar{\mathfrak Q}}$ is a free $\bar F_{\bar{\mathfrak Q}}$-module
of rank $c$. (This is condition (4) of Lemma 00SC, which Lemma 00SG yields from condition (3) of
00SG.)

4. (Choice of $f_1,\dots,f_c$.) Let $L=k[x_1,\dots,x_n]_{\bar{\mathfrak q}'}$
[def-weil-pbc-localization-at-prime], a local ring with maximal ideal $\mathfrak m=\bar{\mathfrak
q}'L$ and residue field $\kappa=L/\mathfrak m$, and $\bar IL$ the ideal generated by $\bar I$. The
image of $k[x_1,\dots,x_n]\setminus\bar{\mathfrak q}'$ in $\bar F$ is $\bar
F\setminus\bar{\mathfrak Q}$, so localizing at either gives the same modules
[def-weil-pbc-module-localization]; localizing the exact sequences $0\to\bar I^2\to\bar I\to\bar
I/\bar I^2\to0$ and $0\to\bar I\to k[x]\to\bar F\to0$ [lem-weil-pbc-localization-module-exact]
gives $(\bar I/\bar I^2)_{\bar{\mathfrak Q}}\cong\bar IL/\bar I^2L$ over $\bar F_{\bar{\mathfrak
Q}}\cong L/\bar IL$. Reducing modulo $\mathfrak m$ and using $\bar I^2L\subseteq\mathfrak m\bar
IL$ (as $\bar I\subseteq\bar{\mathfrak q}'$), step 3 shows that $\bar IL/\mathfrak m\bar IL$ is a
$\kappa$-vector space of dimension $c$ (a free module of rank $c$ reduces to $\kappa^{\oplus c}$).
It is spanned by the classes of $\rho(a_1)/1,\dots,\rho(a_m)/1$, which generate $\bar IL$; choose
among them a basis, and let $f_1,\dots,f_c\in\{a_1,\dots,a_m\}\subseteq I$ be the corresponding
elements, $\bar f_j=\rho(f_j)$. Since $\bar IL$ is a finitely generated module over the local ring
$L$, [lem-weil-pbc-nakayama-local-generators] shows that $\bar f_1/1,\dots,\bar f_c/1$ generate
$\bar IL$: $\bar IL=(\bar f_1,\dots,\bar f_c)L$.

5. (The comparison ring $S'$.) Let $S'=P/(f_1,\dots,f_c)$ with quotient map $\pi'$. Since
$(f_1,\dots,f_c)\subseteq I$, $\pi$ factors as $P\to S'\to S$ with $S'\to S$ surjective with
kernel $J=I/(f_1,\dots,f_c)$, a $P$-module generated by the classes $\bar a_1,\dots,\bar a_m$. Let
$\mathfrak q'_{S'}=\pi'(\mathfrak q')$, the inverse image of $\mathfrak q$ in $S'$ (a prime). Let
$U=P\setminus\mathfrak q'$ and localize the exact sequence of $P$-modules $0\to J\to S'\to S\to0$
at $U$ [lem-weil-pbc-localization-module-exact]: $0\to U^{-1}J\to U^{-1}S'\to U^{-1}S\to0$ is
exact. As $\pi(U)=S\setminus\mathfrak q$ and $\pi'(U)=S'\setminus\mathfrak q'_{S'}$,
$U^{-1}S=S_{\mathfrak q}$ and $U^{-1}S'=S'_{\mathfrak q'_{S'}}$
[def-weil-pbc-module-localization]. Localizing $0\to I\to P\to S\to0$ and $0\to(f)\to P\to S'\to0$
likewise gives $S_{\mathfrak q}=P_{\mathfrak q'}/IP_{\mathfrak q'}$ and $U^{-1}S'=P_{\mathfrak
q'}/(f)P_{\mathfrak q'}$, the map between them being the projection. All these are $P_{\mathfrak
q'}$-modules, hence $R_{\mathfrak p}$-modules via $R_{\mathfrak p}\to P_{\mathfrak q'}$ (defined
because $R\setminus\mathfrak p$ maps into $U$).

6. (Flatness: the sequence stays exact modulo $\mathfrak p$.) By hypothesis (2), $S_{\mathfrak q}$
is a flat $R_{\mathfrak p}$-module [def-weil-pbc-flat-ring-map]. Apply
[lem-weil-pbc-flat-quotient-tensor-injective] over the ring $R_{\mathfrak p}$ to the exact
sequence $0\to U^{-1}J\to U^{-1}S'\to S_{\mathfrak q}\to0$ of step 5 with $N=k=R_{\mathfrak
p}/\mathfrak pR_{\mathfrak p}$: $0\to k\otimes_{R_{\mathfrak p}}U^{-1}J\to k\otimes_{R_{\mathfrak
p}}U^{-1}S'\to k\otimes_{R_{\mathfrak p}}S_{\mathfrak q}\to0$ is exact. By
[lem-weil-pbc-tensor-over-quotient-ring] (1) (ring $R_{\mathfrak p}$, ideal $\mathfrak
pR_{\mathfrak p}$), $k\otimes_{R_{\mathfrak p}}M\cong M/\mathfrak pM$ by $\bar r\otimes x\mapsto
rx$, compatibly with linear maps $M\to M'$; so $0\to U^{-1}J/\mathfrak pU^{-1}J\to
U^{-1}S'/\mathfrak pU^{-1}S'\to S_{\mathfrak q}/\mathfrak pS_{\mathfrak q}\to0$ is exact.

7. (The fibres of $S'$ and $S$ agree at $\mathfrak q'$.) By step 5, the middle map of step 6 is
the projection $P_{\mathfrak q'}/((f)P_{\mathfrak q'}+\mathfrak pP_{\mathfrak q'})\to P_{\mathfrak
q'}/(IP_{\mathfrak q'}+\mathfrak pP_{\mathfrak q'})$; it is injective iff $IP_{\mathfrak
q'}\subseteq(f)P_{\mathfrak q'}+\mathfrak pP_{\mathfrak q'}$. Let $\sigma:P_{\mathfrak q'}\to L$,
$a/u\mapsto\rho(a)/\rho(u)$, well defined since $\rho(U)\cap\bar{\mathfrak q}'=\emptyset$ (step
2). (i) $\ker\sigma=\mathfrak pP_{\mathfrak q'}$: $\rho$ kills $\mathfrak pP$; if
$\rho(a)/\rho(u)=0$ then $w\rho(a)=0$ for some $w\notin\bar{\mathfrak q}'$, and $k[x_1,\dots,x_n]$
is a domain, so $\rho(a)=0$, i.e. every coefficient of $a$ lies in $\ker(R\to k)=\mathfrak p$, so
$a\in\mathfrak pP$ and $a/u\in\mathfrak pP_{\mathfrak q'}$. (ii) $\sigma$ is surjective: every
element of $k=R_{\mathfrak p}/\mathfrak pR_{\mathfrak p}$ is the class of some $r/s$ ($r\in R$,
$s\in R\setminus\mathfrak p$); taking for $s$ the product of the denominators of the finitely many
coefficients, any $y\in k[x_1,\dots,x_n]$ is $y=\rho(s)^{-1}\rho(y')$ with $y'\in P$, $s\in
R\setminus\mathfrak p$; for $y/w\in L$ write likewise $w=\rho(t)^{-1}\rho(w')$; then
$\rho(w')=\rho(t)w\notin\bar{\mathfrak q}'$ (as $\rho(t)\in k^\times$), so $w'\in U$ by step 2,
$sw'\in U$, and
$\sigma(y't/(w's))=\rho(y')\rho(t)/(\rho(w')\rho(s))=(\rho(s)y)\rho(t)/((\rho(t)w)\rho(s))=y/w$.
(iii) For $b\in I$, $\sigma(b/1)=\rho(b)/1\in\bar IL=(\bar f_1,\dots,\bar f_c)L$ (step 4), say
$\rho(b)/1=\sum_j\ell_j\bar f_j$ with $\ell_j\in L$; by (ii) $\ell_j=\sigma(z_j)$, so
$b/1-\sum_jz_jf_j\in\ker\sigma=\mathfrak pP_{\mathfrak q'}$ by (i). Hence $IP_{\mathfrak
q'}\subseteq(f)P_{\mathfrak q'}+\mathfrak pP_{\mathfrak q'}$ and the middle map of step 6 is
injective (it is also surjective), so by exactness in step 6, $U^{-1}J/\mathfrak pU^{-1}J=0$.

8. (Nakayama: $S'$ and $S$ agree near $\mathfrak q'$.) By step 7, $U^{-1}J=\mathfrak
pU^{-1}J\subseteq(\mathfrak q'P_{\mathfrak q'})U^{-1}J$, since the image of $\mathfrak p$ in $P$
lies in $\mathfrak q'$. $U^{-1}J$ is a finitely generated $P_{\mathfrak q'}$-module (by the $\bar
a_i/1$), and $\mathfrak q'P_{\mathfrak q'}$ is the maximal ideal of the local ring $P_{\mathfrak
q'}$ [def-weil-pbc-localization-at-prime], hence its Jacobson radical; by
[lem-weil-pbc-nakayama-jacobson] $U^{-1}J=0$. So $\bar a_i/1=0$, i.e. $u_i\bar a_i=0$ for some
$u_i\in U$ [def-weil-pbc-module-localization]; $u=u_1\cdots u_m\in U$ (a prime's complement is
multiplicative) and $uJ=0$. Localizing $0\to J\to S'\to S\to0$ at $\{u^N\}$
[lem-weil-pbc-localization-module-exact] gives $J_u=0$, so the induced $R$-algebra map
$S'_{\pi'(u)}\to S_{\pi(u)}$ is an isomorphism; here $\pi'(u)\notin\mathfrak q'_{S'}$ and
$\pi(u)\notin\mathfrak q$.

9. (The fibre of $S'$ has dimension $n-c$ at $\mathfrak q'_{S'}$.) As in step 2,
$F'=S'\otimes_Rk\cong\bar F':=k[x_1,\dots,x_n]/(\bar f_1,\dots,\bar f_c)$
[lem-weil-pbc-polynomial-scalar-extension] [lem-weil-pbc-tensor-quotient-base-change]. Since
$S'/\mathfrak q'_{S'}=P/\mathfrak q'=S/\mathfrak q$, $\kappa(\mathfrak q'_{S'})=\kappa(\mathfrak
q)$ compatibly with $S'\to S$, and the composite $k[x_1,\dots,x_n]\to\bar F'\cong
F'\to\kappa(\mathfrak q)$ is the $k$-algebra map sending $x_i$ to the class of $\pi(x_i)$, i.e. it
is $\psi$ of step 2; so the kernel $\mathfrak Q'$ of $F'\to\kappa(\mathfrak q'_{S'})$ corresponds
to $\bar{\mathfrak Q}'=\bar{\mathfrak q}'/(\bar f)$. By
[lem-weil-pbc-polynomial-quotient-dimension-at-point-height-difference], applied to $\bar
F=k[x]/\bar I$ at $\bar{\mathfrak Q}$ and to $\bar F'=k[x]/(\bar f)$ at $\bar{\mathfrak Q}'$ (both
with inverse image $\bar{\mathfrak q}'$ in $k[x]$): $\dim_{\bar{\mathfrak
Q}}\operatorname{Spec}\bar F=n-\operatorname{ht}\bar{\mathfrak q}'+\operatorname{ht}\bar{\mathfrak
Q}$ and $\dim_{\bar{\mathfrak Q}'}\operatorname{Spec}\bar F'=n-\operatorname{ht}\bar{\mathfrak
q}'+\operatorname{ht}\bar{\mathfrak Q}'$. The chains of primes of $\bar F$ (resp. $\bar F'$)
inside $\bar{\mathfrak Q}$ (resp. $\bar{\mathfrak Q}'$) are the chains of primes $\mathfrak P$ of
$k[x]$ with $\bar I\subseteq\mathfrak P\subseteq\bar{\mathfrak q}'$ (resp. $(\bar
f)\subseteq\mathfrak P\subseteq\bar{\mathfrak q}'$), and for a prime $\mathfrak
P\subseteq\bar{\mathfrak q}'$ the two conditions agree: $(\bar f)\subseteq\bar I$; conversely if
$(\bar f)\subseteq\mathfrak P$ and $b\in\bar I$, then by step 4 $b/1=\sum_j(y_j/w_j)\bar f_j$ in
$L$, so $vw_1\cdots w_cb\in(\bar f)\subseteq\mathfrak P$ for some $v\notin\bar{\mathfrak q}'$
(definition of equality of fractions [def-weil-pbc-localization-at-prime]), and $vw_1\cdots
w_c\notin\mathfrak P$ (it is not in $\bar{\mathfrak q}'\supseteq\mathfrak P$), so $b\in\mathfrak
P$. Hence $\operatorname{ht}\bar{\mathfrak Q}=\operatorname{ht}\bar{\mathfrak Q}'$ and
$\dim_{\mathfrak Q'}\operatorname{Spec}F'=\dim_{\bar{\mathfrak Q}'}\operatorname{Spec}\bar
F'=d=n-c$ [def-kun-topological-dimension-at-point] (isomorphic rings have homeomorphic spectra).

10. (Localizing to a relative global complete intersection.) By step 9,
[lem-weil-pbc-equation-count-localize-relative-global-complete-intersection] applies to
$S'=R[x_1,\dots,x_n]/(f_1,\dots,f_c)$ and its prime $\mathfrak q'_{S'}$ (inverse image $\mathfrak
p$ in $R$): there is $h_1\in P$ with $\bar g:=\pi'(h_1)\notin\mathfrak q'_{S'}$ such that
$T_1=R[x_1,\dots,x_{n+1}]/(f_1,\dots,f_c,h_1x_{n+1}-1)$ is a relative global complete intersection
[def-weil-pbc-relative-global-complete-intersection] and $T_1\cong S'_{\bar g}$ as $R$-algebras,
$x_i\mapsto x_i/1$, $x_{n+1}\mapsto1/\bar g$. Under this isomorphism $\pi'(u)/1\in S'_{\bar g}$
(with $u$ from step 8) is the image of $u\in R[x_1,\dots,x_n]\subseteq R[x_1,\dots,x_{n+1}]$ in
$T_1$. By [lem-weil-pbc-relative-global-complete-intersection-principal-localization] (applied to
$T_1$ with $n+1$ variables, $c+1$ equations and the element $u$),
$T_2=R[x_1,\dots,x_{n+2}]/(f_1,\dots,f_c,h_1x_{n+1}-1,ux_{n+2}-1)$ is a relative global complete
intersection and $T_2\cong(T_1)_u\cong(S'_{\bar g})_{\pi'(u)/1}$ as $R$-algebras (an $R$-algebra
isomorphism carrying an element to an element induces an isomorphism of the localizations
[def-weil-ring-localization-away]).

11. (Back to $S$; conclusion.) By [lem-weil-pbc-localization-of-localization] (as in step 1),
$(S'_{\bar g})_{\pi'(u)/1}\cong S'_{\pi'(h_1u)}\cong(S'_{\pi'(u)})_{\bar g/1}$ as $R$-algebras,
and the isomorphism $S'_{\pi'(u)}\cong S_{\pi(u)}$ of step 8 carries $\bar g/1$ to $\pi(h_1)/1$,
so $(S'_{\pi'(u)})_{\bar g/1}\cong(S_{\pi(u)})_{\pi(h_1)/1}\cong S_{g'}$ with $g'=\pi(h_1u)$.
Since $\bar g\notin\mathfrak q'_{S'}$, the inverse image of $\mathfrak q$, we have
$\pi(h_1)\notin\mathfrak q$; with $\pi(u)\notin\mathfrak q$ and $\mathfrak q$ prime,
$g'\notin\mathfrak q$. Thus $S_{g'}\cong
T_2=R[x_1,\dots,x_{n+2}]/(f_1,\dots,f_c,h_1x_{n+1}-1,ux_{n+2}-1)$ as $R$-algebras, a relative
global complete intersection [def-weil-pbc-relative-global-complete-intersection] in $n+2$
variables with $c+2$ equations; this is the conclusion (with $n+2$, $c+2$ in place of $n$, $c$),
for the finitely presented $S$ of step 1, hence for the original $S$ by step 1. -/
theorem exists_relativeGlobalCompleteIntersection_of_syntomicAtPrime
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S)
    (hfp : ∃ g : S, g ∉ q.asIdeal ∧ FinitePresentation R (Localization.Away g))
    (hflat : (Localization.localRingHom (q.asIdeal.comap (algebraMap R S)) q.asIdeal
      (algebraMap R S) rfl).Flat)
    (hci : ∃ h : (q.asIdeal.comap (algebraMap R S)).Fiber S,
      h ∉ (PrimeSpectrum.preimageEquivFiber R S (q.comap (algebraMap R S))
        ⟨q, rfl⟩).asIdeal ∧
      IsGlobalCompleteIntersection (q.asIdeal.comap (algebraMap R S)).ResidueField
        (Localization.Away h)) :
    ∃ (g' : S), g' ∉ q.asIdeal ∧
      ∃ (n c : ℕ) (f : Fin c → MvPolynomial (Fin n) R),
        IsRelativeGlobalCompleteIntersectionPresentation f ∧
        Nonempty (Localization.Away g' ≃ₐ[R]
          (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))) := by
  sorry

end Algebra
