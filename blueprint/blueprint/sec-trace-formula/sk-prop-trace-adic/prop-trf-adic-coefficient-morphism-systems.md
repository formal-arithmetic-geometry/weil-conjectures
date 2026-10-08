+++
id = "prop-trf-adic-coefficient-morphism-systems"
kind = "theorem"
title = "Adic realization for systems of Frobenius coefficient morphisms"
order = 2386
tags = ["latex:proposition"]
uses = ["def-trf-adic-system", "def-trf-categorical-trace", "def-trf-coefficient-conventions", "def-trf-frobenius-coefficient-morphism", "def-weil-derived-complete-integral-detailed", "def-weil-derived-pullback-tensor-hom", "def-weil-finite-coefficient-point", "def-weil-finite-field-fiber", "def-weil-integral-rational-qbar-compact-support", "def-weil-pbc-adic-coefficient-datum", "def-weil-pbc-completed-pullback", "def-weil-pbc-derived-inverse-limit", "lem-fix-compact-support-coefficient-change", "lem-trf-chain-supertrace", "prop-trf-compact-support-perfectness", "prop-trf-graph-frobenius-operator", "prop-trf-rational-frobenius-integral-model", "prop-trf-scheme-galois-comparison", "prop-trf-trace-formal-laws", "thm-trf-finite-coefficient-map"]
+++
Fix the global finite-field datum $p,a,q,k_0,k$ and the coefficient
conventions of [def-trf-coefficient-conventions], with
$A_n=A_{E,n}=\mathcal O_E/\varpi^n$ and $k_E=A_1$. Let $X_0$ be a separated
finite-type $k_0$-scheme, $X=X_0\times_{k_0}k$, $\Phi$ the $q$-power scheme
Frobenius, $g_\gamma$ the geometric-Frobenius automorphism and
$\kappa^{(m)}:L\Phi^{m*}\xrightarrow{\sim}Lg_\gamma^{m*}$ the comparison of
[prop-trf-scheme-galois-comparison].

Let $K_\bullet=(K_n)_{n\geq1}$ be a normalized $A_\bullet$-system of
[def-trf-adic-system], $K_n\in D^b_{ctf}(X,A_n)$, with normalization
isomorphisms $\nu_n:K_{n+1}\otimes^L_{A_{n+1}}A_n\xrightarrow{\sim}K_n$; no
Weil structure is assumed. A *compatible system of Frobenius coefficient
morphisms* on $K_\bullet$ is a family of Frobenius coefficient morphisms
$\psi_n:L\Phi^*K_n\to K_n$ of [def-trf-frobenius-coefficient-morphism]
such that
$$
\nu_n\circ(\psi_{n+1}\otimes^L_{A_{n+1}}A_n)=\psi_n\circ L\Phi^*(\nu_n)\circ\mu_n
\qquad(n\geq1),
$$
where $\mu_n:(L\Phi^*K_{n+1})\otimes^L_{A_{n+1}}A_n\xrightarrow{\sim}
L\Phi^*(K_{n+1}\otimes^L_{A_{n+1}}A_n)$ is the monoidality of pullback
([def-weil-derived-pullback-tensor-hom]); no invertibility is assumed.
Examples: the scheme-Frobenius maps $\varphi_n\circ\kappa_{K_n}$ of a system
with a strict Weil structure at every level, and the systems
$\psi_n=u_n\circ\kappa_{K_n}$ of [prop-trf-rational-frobenius-integral-model],
item (2), attached to a lattice $K_{\mathcal O}$ and a clearing of
denominators $\varphi_E=\varpi^{-N}u$.

Put, for a geometric point $\bar y$ of $X$,
$$
P_n=R\Gamma_c(X,K_n),\qquad P_{\bar y,n}=(K_n)_{\bar y},\qquad
P_{\mathcal O}=R\!\varprojlim_nP_n,\qquad
P_{\bar y,\mathcal O}=R\!\varprojlim_nP_{\bar y,n},
$$
the derived limits of [def-weil-pbc-derived-inverse-limit] of the towers
in $D(\mathcal O_E)$ (via the point identification of
[def-weil-finite-coefficient-point]) whose transition maps are the
composites $P_{n+1}\to P_{n+1}\otimes^L_{A_{n+1}}A_n\xrightarrow{\sim}P_n$ of
item (1) below, with projections $\mathrm{pr}_n$. If $K_\bullet$ is the
reduction tower $K_n=K_{\mathcal O}\otimes^L_{\mathcal O_E}A_n$ of an integral
object $K_{\mathcal O}$ ([def-weil-derived-complete-integral-detailed],
[def-weil-pbc-adic-coefficient-datum]), then
$P_{\mathcal O}=R\Gamma_c(X,K_{\mathcal O})$ by
[def-weil-integral-rational-qbar-compact-support] and
$P_{\bar y,\mathcal O}=L\bar y^*_{\mathrm{comp}}K_{\mathcal O}=:K_{\mathcal O,\bar y}$
is the completed stalk of [def-weil-pbc-completed-pullback].

Call a family $f_\bullet=(f_n)$ of endomorphisms $f_n$ of $P_n$
*compatible* if $f_n$ corresponds to $f_{n+1}\otimes^L_{A_{n+1}}A_n$ under
the isomorphisms of item (1), and call an endomorphism $V$ of $P_{\mathcal O}$
in $D(\mathcal O_E)$ a *lift* of $f_\bullet$ if
$\pi_n\circ(V\otimes^L_{\mathcal O_E}A_n)=f_n\circ\pi_n$ for all $n$, where
$\pi_n:P_{\mathcal O}\otimes^L_{\mathcal O_E}A_n\to P_n$ is the
$A_n$-linear map adjoint to $\mathrm{pr}_n$; likewise for the stalks. Then:

1. *Levelwise perfectness and normalization.* Each $P_n$ and $P_{\bar y,n}$ lies
in $D^b_{\mathrm{fin}}(A_n)$, and $\nu_n$ induces isomorphisms
$P_{n+1}\otimes^L_{A_{n+1}}A_n\xrightarrow{\sim}P_n$ and
$P_{\bar y,n+1}\otimes^L_{A_{n+1}}A_n\xrightarrow{\sim}P_{\bar y,n}$.
1. *Integral realization and lifts.* $P_{\mathcal O}$ and
$P_{\bar y,\mathcal O}$ are represented by bounded complexes of finite free
$\mathcal O_E$-modules, and every $\pi_n$ is an isomorphism. Every
compatible family of endomorphisms has a lift, and every $V$ with
$\mathrm{pr}_n\circ V=f_n\circ\mathrm{pr}_n$ for all $n$ (for instance the
derived limit of a morphism of towers) is a lift of $f_\bullet$.
1. *Compatibility of the Frobenius operators.* For every $m\geq1$ the global
operators $F_{c,m}(\psi_n)=T_{c_m}(\psi_{n,m})$ of
[def-trf-frobenius-coefficient-morphism] form a compatible family on
$(P_n)$, and for $y\in X_0(\mathbf F_{q^m})$ with geometric point $\bar y$
the stalk endomorphisms $\psi_{n,m,\bar y}=(\psi_{n,m})_{\bar y}\circ\iota_{K_n}$
(normalized as in [prop-trf-rational-frobenius-integral-model]) form a
compatible family on $(P_{\bar y,n})$.
1. *Traces.* If $V$ lifts the compatible family $f_\bullet$, then the
categorical trace $\operatorname{tr}_{\mathcal O_E}(V\mid P_{\mathcal O})$
reduces modulo $\varpi^n$ to $\operatorname{tr}_{A_n}(f_n\mid P_n)$ for
every $n$; hence
$$
\operatorname{tr}_{\mathcal O_E}(V\mid P_{\mathcal O})
=\bigl(\operatorname{tr}_{A_n}(f_n\mid P_n)\bigr)_n\in\varprojlim_nA_n=\mathcal O_E,
$$
independently of the lift. In particular the elements
$\operatorname{tr}_{\mathcal O_E}\bigl(F_{c,m}(\psi_\bullet)\mid P_{\mathcal O}\bigr)$
and
$\operatorname{tr}_{\mathcal O_E}\bigl(\psi_{\bullet,m,\bar y}\mid P_{\bar y,\mathcal O}\bigr)$,
the traces of any lifts of the families of item (3), are well defined.

Here $\operatorname{tr}_{\mathcal O_E}$ is the categorical trace of
[def-trf-categorical-trace] formed over the commutative ring
$\mathcal O_E$, with the duality data of [lem-trf-chain-supertrace].

## Proof

*(1).* Each $K_n$ lies in $D^b_{ctf}(X,A_n)$, so $P_n$ and $P_{\bar y,n}$ are
perfect by [prop-trf-compact-support-perfectness]. The finite-level
coefficient change of [thm-trf-finite-coefficient-map] for
$\rho:A_{n+1}\to A_n$ and $f=a_X:X\to\Spec k$ (its compact-support
isomorphism is the coefficient comparison of
[lem-fix-compact-support-coefficient-change]), followed by $R\Gamma_c(X,\nu_n)$,
gives $P_{n+1}\otimes^L A_n\cong R\Gamma_c(X,K_{n+1}\otimes^LA_n)\cong P_n$;
for the stalks, its pullback isomorphism for $\bar y$ ($L\bar y^*$ is a
pullback, hence monoidal, [def-weil-derived-pullback-tensor-hom]) gives
$P_{\bar y,n+1}\otimes^LA_n\cong(K_{n+1}\otimes^LA_n)_{\bar y}\cong P_{\bar y,n}$.

*(2).* We prove the assertion for an arbitrary tower $(Q_n)$ of objects
$Q_n\in D^b_{\mathrm{fin}}(A_n)$ with isomorphisms
$\theta_n:Q_{n+1}\otimes^L_{A_{n+1}}A_n\xrightarrow{\sim}Q_n$, the transition
maps being $Q_{n+1}\to Q_{n+1}\otimes^LA_n\xrightarrow{\theta_n}Q_n$; by (1)
this applies to $(P_n)$ and to $(P_{\bar y,n})$.

*Minimal models.* By [def-trf-categorical-trace] each $Q_n$ is a bounded
complex $M$ of finite projective, hence free, modules over the local ring
$A_n$. If some differential satisfies $d^i\otimes k_E\neq0$, pick
$e\in M^i$ with $f=d^ie\notin\varpi M^{i+1}$; by Nakayama $f$ is part of a
basis, $M^{i+1}=A_nf\oplus D'$ with $D'$ free, and $A_ne\cong A_n$
(as $ae=0$ forces $af=0$). Put
$C=(d^i)^{-1}(D')$. Writing $d^ix=af+d'$ one has $x-ae\in C$, so
$M^i=A_ne\oplus C$; if $d^ix=0$ then $af\in D'$, so $a=0$ and
$\ker d^i\subset C$; in particular $d^{i-1}(M^{i-1})\subset C$, and $C$, a
direct summand of a free module over a local ring, is free. Since $d^{i+1}f=0$, the complex $M$ is the direct sum of
the contractible complex $A_ne\xrightarrow{\sim}A_nf$ and of the complex
$\cdots\to M^{i-1}\to C\to D'\to M^{i+2}\to\cdots$ of finite free modules.
Discarding the contractible summand lowers the total rank, so after finitely
many steps $Q_n$ is represented by a *minimal* complex, i.e. one with
$d\otimes k_E=0$. A quasi-isomorphism $\alpha:M\to M'$ between minimal
complexes is an isomorphism of complexes: $\alpha\otimes k_E$ is a
quasi-isomorphism between complexes with zero differential, hence bijective
in each degree, and by Nakayama each $\alpha^i$ is a surjection between free
modules of the same finite rank, hence bijective. Morphisms in $D(A_n)$
between bounded complexes of projectives are homotopy classes of chain maps.

*Strictification.* Choose a minimal model $\chi_1:M_1\xrightarrow{\sim}Q_1$.
Given a minimal $\chi_n:M_n\xrightarrow{\sim}Q_n$, choose a minimal model
$\chi':M'\xrightarrow{\sim}Q_{n+1}$. The isomorphism
$\chi_n^{-1}\circ\theta_n\circ(\chi'\otimes A_n):M'\otimes A_n\to M_n$ in
$D(A_n)$ is represented by a chain map $\alpha$ between minimal complexes,
hence by an isomorphism of complexes; so $M'^i$ and $M_n^i$ have the same
rank $r_i$. In bases, each $\alpha^i\in\mathrm{GL}_{r_i}(A_n)$; lift it to
$\beta^i\in\mathrm{GL}_{r_i}(A_{n+1})$ (a lift of an invertible matrix over
a local ring is invertible) and let $M_{n+1}$ be $M'$ with the differential
transported by $\beta$. Then $\beta:M'\to M_{n+1}$ is an isomorphism of
complexes, $M_{n+1}\otimes A_n=M_n$ as complexes because $\alpha$ is a chain
map, and $\chi_{n+1}=\chi'\circ\beta^{-1}$ satisfies
$\theta_n\circ(\chi_{n+1}\otimes A_n)=\chi_n$. Under the $\chi_n$ the
transition maps become the reduction maps $\rho_n:M_{n+1}\to M_n$, which are
surjective in each degree.

*Limit.* Put $M=\varprojlim_nM_n$ degreewise: a bounded complex with
$M^i\cong\mathcal O_E^{r_i}$ and $M/\varpi^n=M_n$. The sequence
$0\to M\to\prod_nM_n\xrightarrow{1-\rho}\prod_nM_n\to0$ is exact in each
degree (given $(y_n)$, choose $x_1$ and inductively $x_{n+1}$ lifting
$x_n-y_n$), so it gives a distinguished triangle; products in the derived
category are computed termwise ([def-weil-pbc-derived-inverse-limit]), so this
is the Roos triangle of the tower, and $R\varprojlim_nQ_n\cong M$ compatibly
with the maps to $\prod_nQ_n$. Thus $\mathrm{pr}_n$ is $\chi_n$ composed with
the projection $M\to M_n$, and its adjoint
$\pi_n:M\otimes^L_{\mathcal O_E}A_n=M/\varpi^n\to M_n\xrightarrow{\chi_n}Q_n$
is an isomorphism.

*Lifts.* Transport a compatible family along the $\chi_n$. Then
$f_n=[g_n]\in H^0\operatorname{Hom}^\bullet(M_n,M_n)$ with
$[\rho(g_{n+1})]=[g_n]$, and
$\operatorname{Hom}^\bullet(M,M)=\varprojlim_n\operatorname{Hom}^\bullet(M_n,M_n)$
with surjective transitions (matrices over $\mathcal O_E$ modulo $\varpi^n$).
Choose representatives inductively: if $\rho(g'_{n+1})=g_n+dh_n$, lift $h_n$
to $h'_{n+1}$ and replace $g'_{n+1}$ by $g_{n+1}=g'_{n+1}-dh'_{n+1}$, a
cocycle in the same class with $\rho(g_{n+1})=g_n$. Then $V=(g_n)_n$ is a
chain endomorphism of $M$ with $V\otimes A_n=g_n$, i.e. a lift. Finally, if
$\mathrm{pr}_n\circ V=f_n\circ\mathrm{pr}_n$, then $\pi_n\circ(V\otimes A_n)$
and $f_n\circ\pi_n$ are both adjoint to this map under the adjunction between
$-\otimes^L_{\mathcal O_E}A_n$ and restriction of scalars, so they are equal.

*(3).* The iterates are compatible: by induction on $m$, using the recursion
of [def-trf-frobenius-coefficient-morphism], the monoidality isomorphisms
$\mu$ and their compatibility with the composition isomorphisms of pullback
([def-weil-derived-pullback-tensor-hom]), $\psi_{n+1,m}\otimes A_n$
corresponds to $\psi_{n,m}$. The comparison $\kappa^{(m)}$ is natural and
compatible with the coefficient reductions, as shown in the proof of item (2)
of [prop-trf-rational-frobenius-integral-model]; hence
$v_n=\psi_{n,m}\circ(\kappa^{(m)}_{K_n})^{-1}:Lg_\gamma^{m*}K_n\to K_n$
satisfy $v_{n+1}\otimes A_n=v_n$ under $\nu_n$. By the general clause of
[prop-trf-graph-frobenius-operator], which allows non-invertible $v$,
$$
F_{c,m}(\psi_n)=T_{c_m}(v_n\circ\kappa^{(m)}_{K_n})
=R\Gamma_c(X,v_n)\circ g_{\gamma,c}^{m,*}.
$$
The coefficient comparison of [lem-fix-compact-support-coefficient-change]
is natural in the complex and compatible with pullback, hence with the
base-change isomorphisms $g_{\gamma,c}^{m,*}$; so $F_{c,m}(\psi_{n+1})\otimes A_n$
corresponds to $F_{c,m}(\psi_n)$ under the isomorphism of (1). For the stalks,
$\iota_{K_n}$ is built from composition isomorphisms of pullback for
$\Phi^m\circ\bar y=\bar y$, and $L\bar y^*$ is monoidal; hence
$\psi_{n+1,m,\bar y}\otimes A_n$ corresponds to $\psi_{n,m,\bar y}$.

*(4).* Represent $P_{\mathcal O}$ by $M$ as in (2) and $V$ by a chain map.
By [lem-trf-chain-supertrace], over $\mathcal O_E$ and over $A_n$,
$\operatorname{tr}_{\mathcal O_E}(V\mid M)=\sum_i(-1)^i\operatorname{Tr}(V^i\mid M^i)$,
whose reduction modulo $\varpi^n$ is
$\sum_i(-1)^i\operatorname{Tr}(V^i\bmod\varpi^n\mid M_n)=\operatorname{tr}_{A_n}(V\otimes A_n\mid M_n)$
(equivalently, item (3) of [prop-trf-trace-formal-laws]). Since $\pi_n$
conjugates $V\otimes A_n$ into $f_n$, conjugacy invariance
([prop-trf-trace-formal-laws], item (1)) gives
$\operatorname{tr}_{A_n}(V\otimes A_n)=\operatorname{tr}_{A_n}(f_n\mid P_n)$.
As $\mathcal O_E$ is $\varpi$-adically complete and separated,
$\mathcal O_E\to\varprojlim_nA_n$ is an isomorphism, which gives the displayed
formula and its independence of the lift. The last sentence combines this
with (2) and (3).
