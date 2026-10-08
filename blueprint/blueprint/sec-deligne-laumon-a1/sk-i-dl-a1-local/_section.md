+++
id = "sk-i-dl-a1-local"
kind = "section"
title = "Local boundary duality and ramification at infinity"
order = 2724
uses = ["sk-d-dl-a1-setup", "sk-d-real-boundary", "sk-prop-sf-biduality-general", "sk-prop-sf-closed-unit", "sk-prop-sf-open-closed-triangle", "sk-rem-sf-kv-formal", "sk-thm-sf-ctf-stability", "sk-thm-sf-dual-perfect", "sk-thm-sf-verdier-exchange"]
lean = ["AlgebraicGeometry.exists_linearEquiv_dual_stalk_higherDirectImage", "AlgebraicGeometry.not_isUnramifiedAtInfinity_artinSchreier"]
+++
*Proposition (sketch).*

For a dense open immersion $j:U_0\hookrightarrow C_0$ of smooth curves,
a lisse Weil sheaf $F$, and a missing closed point $s$, there is a
Frobenius-equivariant perfect pairing

$$
(j_*F^\vee)_{\bar s}\otimes (R^1j_*F)_{\bar s}
\longrightarrow\DLAQ(-1).
$$

Also, for a nontrivial character $\psi:\mathbf F_p\to\DLAQ^\times$
and $a\in k^\times$, the geometric linear Artin–Schreier sheaf
$\mathcal L_{\psi(ax)}$ is ramified at infinity.

## Proof

*Local duality.* Work on the geometric curves with their Weil
structures, under the coefficient and admissibility hypotheses of
Section [sec-six-functors]. Let $i:Z=C\setminus U\hookrightarrow C$
be the whole closed complement, and put $A(F)=i^*Rj_*F$.
Verdier exchange and general constructible biduality give
$\mathbb D_C Rj_*\simeq j_!\mathbb D_U$; by adjunction they also give
$\mathbb D_Zi^*\simeq i^!\mathbb D_C$. Here $i^!$ denotes the derived
exceptional inverse image. General biduality applies to the boundary
complexes, even though they need not be lisse on $C$.

For a constructible complex $G$ on $U$, adjunction and $j^*i_*=0$ give
$i^!Rj_*G=0$. Apply $i^!$ to the open–closed triangle

$$
j_!G\longrightarrow Rj_*G\longrightarrow i_*i^*Rj_*G
\xrightarrow{+1}.
$$

Since $i^!i_*\simeq\operatorname{id}$, this yields
$i^!j_!G\simeq i^*Rj_*G[-1]$. Smooth curve duality supplies
$\mathbb D_UF=F^\vee(1)[2]$, hence

$$
\begin{aligned}
\mathbb D_Z A(F)
&\simeq i^!\mathbb D_C Rj_*F
\simeq i^!j_!\mathbb D_UF\\
&\simeq i^*Rj_*(\mathbb D_UF)[-1]
\simeq A(F^\vee)(1)[1].
\end{aligned}
$$

On the finite geometric scheme $Z$, Verdier duality is ordinary
finite-dimensional coefficient duality. Taking degree $-1$ at $\bar s$
therefore gives

$$
(R^1j_*F)_{\bar s}^{\vee}
\simeq (j_*F^\vee)_{\bar s}(1),
$$

which is the asserted perfect pairing. All maps are natural in the
Weil structures, so the pairing respects the local geometric Frobenius.

*Ramification at infinity.* Set $t=1/x$ and $K=k((t))$.
The Artin–Schreier cover is $u^p-u=a/t$. In the root field $L=K(u)$,
normalize the discrete valuation $v_L$ to have value group $\mathbf Z$
and write $v_L(t)=e$. The equation forces $v_L(u)<0$, so
$p\,v_L(u)=-e$. Thus $p\mid e$, and
$e\le[L:K]\le p$ implies $e=[L:K]=p$.
The extension is totally ramified, and its roots $u+c$, $c\in\mathbf F_p$,
show that it is Galois with group $\mathbf F_p$. The nontrivial character
$\psi$ of this group of prime order is faithful, so inertia acts
nontrivially on $\mathcal L_{\psi(ax)}$.

Uses: [sk-d-dl-a1-setup], [sk-prop-sf-biduality-general], [sk-prop-sf-closed-unit], [sk-prop-sf-open-closed-triangle], [sk-rem-sf-kv-formal], [sk-thm-sf-ctf-stability], [sk-thm-sf-dual-perfect], [sk-thm-sf-verdier-exchange]
