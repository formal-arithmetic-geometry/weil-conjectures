+++
id = "def-wf-tate-twist"
kind = "definition"
title = "Tate twists"
order = 2566
uses = ["def-weil-pbc-proetale-site", "def-wf-weil-category"]
+++
On the pro-etale site put

$$
\mathbf Z_\ell(1)=\varprojlim_n\mu_{\ell^n},\qquad
E(1)=\mathbf Z_\ell(1)\otimes_{\mathbf Z_\ell}E,
$$

with transition the $\ell$-th power map.
Put $E(0)=E_X$, $E(m)=E(1)^{\otimes^L_E m}$ for $m>0$, and
$E(-m)=R\operatorname{Hom}_E(E(m),E_X)$ for $m>0$, with the induced
tensor and internal-Hom arrows. The *Tate twist* functor is

$$
(-)(m)=-\otimes^L_E E(m):\mathrm{WeilD}(X_0,E)
\longrightarrow\mathrm{WeilD}(X_0,E).
$$
