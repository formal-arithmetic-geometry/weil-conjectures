+++
id = "def-fd-artin-schreier-sheaf"
kind = "definition"
title = "The Artin–Schreier sheaf"
order = 2677
lean = ["AlgebraicGeometry.Etale.artinSchreierSheaf"]
uses = ["def-fd-additive-character", "def-weil-pbc-etale-site", "def-weil-pbc-finite-torsors", "def-weil-pbc-scheme-conventions"]
+++
Let $X_0$ be a separated scheme of finite type over $k_0=\mathbf F_q$
(conventions of [def-weil-pbc-scheme-conventions]), let
$f\in\Gamma(X_0,\mathcal O_{X_0})$, and let
$\psi=\Psi\circ\operatorname{Tr}_{k_0/\mathbf F_p}$ be the nondegenerate
additive character of [def-fd-additive-character], with $\Psi$ the fixed
nontrivial character of $\mathbf F_p$. The *Artin–Schreier covering*
attached to $f$ is

$$
\pi:Y\to X_0,\qquad
Y=\operatorname{Spec}_{X_0}\mathcal O_{X_0}[T]/(T^p-T-f),
$$

a finite étale morphism in the sense of [def-weil-pbc-etale-site], with the
$\mathbf F_p$-action $\sigma_a:T\mapsto T+a$ ($a\in\mathbf F_p$), which makes
it an $\mathbf F_p$-torsor in the sense of [def-weil-pbc-finite-torsors];
the $\sigma_a$ act on $\pi_*\overline{\mathbf Q}_\ell$ by pullback. The
*Artin–Schreier sheaf* $\mathcal L_{\psi,f}$ is the $\Psi$-isotypic
component

$$
\mathcal L_{\psi,f}:=e_\Psi\cdot\pi_*\overline{\mathbf Q}_\ell
\;\subseteq\;\pi_*\overline{\mathbf Q}_\ell,
\qquad
e_\Psi=\frac1p\sum_{a\in\mathbf F_p}\Psi(-a)\,\sigma_a ,
$$

i.e. the subsheaf on which each $\sigma_a$ acts by $\Psi(a)$ ($e_\Psi$ is
defined since $p\neq\ell$). The idempotent uses the character $\Psi$ of
$\mathbf F_p$, not $\psi|_{\mathbf F_p}$, which is trivial when
$p\mid[k_0:\mathbf F_p]$. The same construction for the character
$\psi^{-1}=\Psi^{-1}\circ\operatorname{Tr}_{k_0/\mathbf F_p}$ defines
$\mathcal L_{\psi^{-1},f}:=e_{\Psi^{-1}}\cdot\pi_*\overline{\mathbf Q}_\ell$.
For $a\in k_0$ put
$\mathcal L_{\psi(af)}:=\mathcal L_{\psi,af}$ (similarly
$\mathcal L_{\psi^{-1}(af)}:=\mathcal L_{\psi^{-1},af}$); on
$\mathbf A^1_{k_0}=\operatorname{Spec}k_0[x]$ one writes
$\mathcal L_\psi:=\mathcal L_{\psi,x}$ (the *Artin–Schreier*, or
*exponential*, sheaf) and $\mathcal L_{\psi(ax)}:=\mathcal L_{\psi,ax}$.
