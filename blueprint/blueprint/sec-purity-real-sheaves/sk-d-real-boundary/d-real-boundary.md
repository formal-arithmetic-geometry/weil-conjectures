+++
id = "d-real-boundary"
kind = "definition"
title = "Boundary extension and inertia"
order = 2641
uses = ["d-real-setup", "def-real-weil-representation-operations", "def-wf-fundamental-representation", "def-wf-weil-group"]
+++
Let $j:U_0\hookrightarrow C_0$ be a nonempty open in a
curve in the sense of [d-real-setup], with finite complement $S_0$, and let
$\mathcal F$ be lisse Weil on $U_0$, with Weil fundamental representation
$\rho$ of [def-wf-fundamental-representation].
Write $J=j_*\mathcal F$ for ordinary sheaf direct image, defined by
sections over the inverse image of an etale neighborhood; use this
construction at finite coefficient levels for adic coefficients.
For $s\in S_0$, let $K_s$ be the fraction field of the henselization of
$\mathcal O_{C_0,s}$, and put

$$
I_s=\ker\bigl(\Gal(\overline K_s/K_s)\to
\Gal(\overline{k(s)}/k(s))\bigr).
$$

Henselization is the universal local henselian extension with unchanged
residue field; a henselian ring lifts simple roots of monic polynomials.
Choose a geometric point over $\operatorname{Spec}K_s\to U_0$ and a path
from it to the base point of $\rho$; this gives a
decomposition-group homomorphism $\Gal(\overline K_s/K_s)\to\pi_1(U_0)$
carrying $I_s$ into $\pi_1(U)$ and the inverse image $W(K_s)$ of the
integer powers of geometric Frobenius of $k(s)$ into the Weil group
$W(U_0)$ of [def-wf-weil-group].
The local generic stalk $V_s$ is the space of $\rho$ with $W(K_s)$ acting through $\rho$.
Residue Frobenius lifts in $W(K_s)$ differ by elements of $I_s$, so they act
unambiguously on the invariants $V_s^{I_s}$ in the sense of
[def-real-weil-representation-operations].
Another path changes the homomorphism by conjugation by some
$g\in\pi_1(U_0)$. Write $g=wd$ with $w\in W(U_0)$ and $d$ in the image
$D$ of $\Gal(\overline K_s/K_s)$: identify $\Gal(k/\Fq)$ with
$\widehat{\mathbf Z}$ by sending geometric Frobenius to $1$, so that the
degree of [def-wf-weil-group] extends to
$\pi_1(U_0)\to\widehat{\mathbf Z}$ with $W(U_0)=\deg^{-1}(\mathbf Z)$;
then $\deg(D)=e_s\widehat{\mathbf Z}$, because $\Gal(\overline K_s/K_s)$
maps onto $\Gal(\overline{k(s)}/k(s))=\Gal(k/k(s))$, and
$\widehat{\mathbf Z}=\mathbf Z+e_s\widehat{\mathbf Z}$, so some $d\in D$
has $\deg g-\deg d\in\mathbf Z$, and $w=gd^{-1}$ lies in $W(U_0)$.
Conjugation by $d$ preserves the image of the normal subgroup $I_s$, and
it changes the image of a residue Frobenius lift $\Phi$ only by an
element of $I_s$, because the residue Galois group
$\Gal(\overline{k(s)}/k(s))$ is abelian, so that
$\delta\Phi\delta^{-1}\Phi^{-1}\in I_s$ for every
$\delta\in\Gal(\overline K_s/K_s)$. Hence the invariant space for the
new homomorphism is $\rho(w)V_s^{I_s}$, and the map $\rho(w)$ identifies
the two invariant spaces Frobenius-equivariantly, so $V_s^{I_s}$ is
independent of the choice up to Frobenius-equivariant isomorphism.

Uses: [d-real-setup], [def-real-weil-representation-operations], [def-wf-fundamental-representation], [def-wf-weil-group]
