+++
id = "def-weil-integral-rational-qbar-compact-support"
kind = "definition"
title = "Integral, rational, and algebraically closed compact-support functors"
order = 1490
uses = ["def-compact-support-direct-image-detailed", "def-weil-algebraically-closed-coefficients", "def-weil-derived-complete-integral-detailed", "def-weil-finite-torsion-constructibility", "def-weil-rationalization-karoubi", "def-weil-scheme-morphism-properties"]
+++
Let $K_0$ be a field, let $X,Y$ be finite-type
[def-weil-scheme-morphism-properties] $K_0$-schemes, and let $f:X\to Y$ be a
separated finite-type $K_0$-morphism. Fix a prime $\ell$, write
$\Ql=\mathbf Q_\ell$, choose an algebraic closure $\Qlb$ of $\Ql$, and
require that its image in $K_0$ is invertible. Choose a finite extension
$E/\Ql$ with valuation ring $\mathcal O_E$, and a uniformizer $\varpi_E$. For
every $n\in\mathbf Z_{\geq1}$, set $A_{E,n}=\mathcal O_E/\varpi_E^n$. The
categories $D^b_c(X,\mathcal O_E)$, $D^b_c(X,E)$, and $D^b_c(X,\Qlb)$ use,
respectively, the derived-complete integral
[def-weil-derived-complete-integral-detailed], rationalized
[def-weil-rationalization-karoubi], and common-stage algebraically closed
[def-weil-algebraically-closed-coefficients] constructions. The finite levels
use finite-torsion constructibility
[def-weil-finite-torsion-constructibility]. For $K\in D^b_c(X,\mathcal
O_E)$, put $K_n=K\otimes^L_{\mathcal O_E}A_{E,n}$ and define

$$
 Rf_!K=
 R\varprojlim_n\operatorname{Res}_n Rf_{!,n}K_n.
$$

This is the compactification-independent direct image
[def-compact-support-direct-image-detailed]. If $K_E\in D^b_c(X,E)$ is
represented by $K$, define

$$
 Rf_!K_E=(Rf_!K)\otimes_{\mathcal O_E}^L E
$$

in the rationalized category. If $K_{\Qlb}\in D^b_c(X,\Qlb)$ is represented
at a finite stage by $K_E$ for some $E\subset\Qlb$, define

$$
 Rf_!K_{\Qlb}=Rf_!K_E\otimes_E\Qlb
$$

in the common-stage category.
