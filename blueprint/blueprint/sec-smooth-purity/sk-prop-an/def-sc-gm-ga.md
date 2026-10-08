+++
id = "def-sc-gm-ga"
kind = "definition"
title = "The multiplicative group, the additive group, and their finite subgroups"
order = 1963
uses = ["def-sc-gm-torsor", "def-sc-group-scheme", "def-sc-group-scheme-subgroup", "def-sc-kummer-sequence"]
+++
Let $k$ be a field. The *multiplicative group* is the
group scheme
$\mathbf G_m=\Spec k[t,t^{-1}]$, with comultiplication, counit and
antipode the $k$-algebra maps $m^*(t)=t\otimes t$,
$\varepsilon(t)=1$, $i^*(t)=t^{-1}$; the group-scheme axioms of
[def-sc-group-scheme] hold because the identities
$(t_1t_2)t_3=t_1(t_2t_3)$, $1\cdot t=t=t\cdot1$ and $t^{-1}t=1$
hold in the Laurent polynomial ring. The *additive group* is
$\mathbf G_a=\Spec k[y]$, with $m^*(y)=y\otimes1+1\otimes y$,
$\varepsilon(y)=0$, $i^*(y)=-y$; here the axioms are the
corresponding identities for addition. For $n\geq1$,

$$
\mu_n:=\Spec k[t]/(t^n-1)\subseteq\mathbf G_m
$$

is the *group scheme of $n$-th roots of unity*, and, when
$\operatorname{char}k=p>0$,

$$
\alpha_p:=\Spec k[y]/(y^p)\subseteq\mathbf G_a
$$

is the *Frobenius kernel* of $\mathbf G_a$; both are closed
subgroup schemes, the closed
immersion being the one induced by the displayed surjections of
coordinate rings. The group schemes $\mathbf G_m$ and $\mu_n$ are
the ones occurring in the
$\mathbf G_m$-torsors and in the
Kummer sequence of the smooth-curve chapter.
