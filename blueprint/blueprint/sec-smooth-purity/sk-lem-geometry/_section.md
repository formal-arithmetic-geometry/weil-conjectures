+++
id = "sk-lem-geometry"
kind = "section"
title = "Geometry of the deformation of a section"
order = 1997
uses = ["sk-def-purity-conv", "sk-prop-an"]
lean = ["AlgebraicGeometry.Scheme.Hom.nonempty_deformationToNormalConeData"]
+++
*Lemma (sketch).*

In the conventions of [sk-def-purity-conv] let $g:V\to B$ be smooth of pure
relative dimension $d$ with closed section $s$, and let $N_s\to B$ be the
normal bundle of $s$ with zero section $0_N$ and projection $\pi_N$. Then:

1. **(1)** *the fibres.* The fibre of $\widetilde g$ over $1$ is
$(g:V\to B,s)$ and the fibre over $0$ is $(\pi_N:N_s\to B,0_N)$; writing
$i_0,i_1:B\to\Aaf^1_B$ for the two sections, base change gives
$Li_1^{*}\mathcal F\simeq\mathcal C(g,s)$ and
$Li_0^{*}\mathcal F\simeq\mathcal C(\pi_N,0_N)$.
1. **(2)** *coordinates.* Since $s$ is a section of a smooth map, there
are étale-locally coordinates $x_1,\dots,x_d$ on $V$ over $B$ in which $s$
is $x_i=0$; on the deformation chart $u_i=x_i/t$, so $\widetilde g$ is smooth
of pure relative dimension $d$.
1. **(3)** *the punctured trivialization.* Over $\mathbf G_{m,B}$ the
deformation space is canonically $V\times_B\mathbf G_{m,B}$ with
$\widetilde s=s\times1$, so base change gives a canonical
$\kappa^{\circ}:j^{*}\mathcal F\xrightarrow{\ \sim\ }j^{*}a^{*}\mathcal C(g,s)$,
where $a:\Aaf^1_B\to B$.
1. **(4)** *the standard pair.* For $(\Aaf^d_B\to B,0)$ the deformation
space is $\Aaf^d_B\times_B\Aaf^1_B$ with $x_k=tu_k$, the family object is
$a^{*}0^{*}\omega_{\Aaf^d_B/B}$, and $0^{*}\omega_{\Aaf^d_B/B}=\Lambda(d)[2d]$
by the $R\pi^{!}$-form [sk-prop-an] (ii)
($\omega_{\Aaf^d_B/B}\cong\Lambda(d)[2d]$, pulled back along the zero
section).
1. **(5)** *base change.* All of this commutes with base change in $B$
and with étale localization.

## Proof

*Rees description.* The blow-up of [sk-def-purity-conv] with the
strict transform of the closed fibre deleted is
$\Spec_V\bigl(\bigoplus_{r\in\Z}\mathcal I_s^{\,r}t^{-r}\bigr)$, with
$\mathcal I_s^{\,r}=\mathcal O_V$ for $r\le0$ and $\widetilde g$ induced by
$t$. Inverting $t$ gives $\mathcal O_V[t,t^{-1}]$, which is (3) and the
fibre $V$ over $1$; setting $t=0$ gives
$\bigoplus_{r\ge0}\mathcal I_s^{\,r}/\mathcal I_s^{\,r+1}$, the normal cone,
a vector bundle because a section of a smooth map is a regular immersion.
This is (1), the comparison of fibres being base change for $\omega$
([sk-prop-cohsm] (c)).

*Coordinates.* A closed section of a smooth map is étale-locally
$x_i=0$ in relative coordinates $x_1,\dots,x_d$ (the relative local
linearization). On the chart $u_i=x_i/t$ the extended Rees algebra is
$\mathcal O[u_1,\dots,u_d,t]/(tu_i-x_i)$, in which each $x_i$ is eliminated,
so the chart is $\Aaf^d\times\Aaf^1$ over the base and $\widetilde g$ is the
last projection; this is (2), and the remaining charts give the same
computation after substituting a generator of the centre. Item (4) is this
computation for the standard pair together with [sk-prop-an] (ii), and (5) is
the base-change behaviour of the Rees algebra, of the punctured
trivialization and of the normal cone.

Uses: [sk-def-purity-conv], [sk-prop-an]
