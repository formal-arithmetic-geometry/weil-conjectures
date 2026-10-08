+++
id = "sk-def-as"
kind = "section"
title = "The Artin–Schreier sheaf"
order = 2676
lean = ["AlgebraicGeometry.Etale.artinSchreierSheaf"]
uses = ["sk-def-char"]
+++
*Definition (sketch).*

Let $\psi=\Psi\circ\Tr_{k_0/\Fp}$ be the additive character of
[sk-def-char]. For $X_0/k_0$ and $f\in\Gamma(X_0,\mathcal O_{X_0})$, the
Artin–Schreier covering is
$\pi:Y=\Spec_{X_0}\mathcal O_{X_0}[T]/(T^p-T-f)\to X_0$ with its $\Fp$-action
$\sigma_a:T\mapsto T+a$, which acts on $\pi_*\Qlb$ by pullback. The
*Artin–Schreier sheaf* $\mathcal L_{\psi,f}$ is the $\Psi$-isotypic
component

$$
\mathcal L_{\psi,f}:=e_\Psi\,\pi_*\Qlb,\qquad
e_\Psi=\frac1p\sum_{a\in\Fp}\Psi(-a)\,\sigma_a ,
$$

the subsheaf on which each $\sigma_a$ acts by $\Psi(a)$. The idempotent uses
the character $\Psi$ of $\Fp$, not $\psi|_{\Fp}$, which is trivial when
$p\mid[k_0:\Fp]$. For $a\in k_0$ put $\mathcal L_{\psi(af)}:=\mathcal L_{\psi,af}$; on $\Aone$ one writes $\mathcal L_\psi=\mathcal L_{\psi,x}$ and
$\mathcal L_{\psi(ax)}=\mathcal L_{\psi,ax}$. (Blueprint the Fourier–Deligne chapter,
def:fd-artin-schreier-sheaf.)

Uses: [sk-def-char]
