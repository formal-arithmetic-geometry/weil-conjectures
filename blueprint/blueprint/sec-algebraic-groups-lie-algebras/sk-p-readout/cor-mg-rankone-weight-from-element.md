+++
id = "cor-mg-rankone-weight-from-element"
kind = "theorem"
title = "Rank-one weight from a positive-degree element"
order = 2556
tags = ["latex:corollary"]
uses = ["def-weil-punctual-weights", "def-wf-weil-category", "def-wf-weil-group", "lem-wf-rank-one-component-modulus"]
+++
Let $X_0$ be a normal geometrically connected curve over $k_0$, put
$|k_0|=q$, and let
$\mathcal L_0$ be a rank-one lisse
Weil sheaf on $X_0$ with Weil
character $\chi:\hyperref[def-wf-weil-group]{W(X_0)}\to E^\times$, with $E/\mathbf Q_\ell$
finite, such that $\chi(\pi_1(X))$ is finite, and fix
$\iota:E\hookrightarrow\mathbf C$. For $w\in\mathbf R$ the
sheaf $\mathcal L_0$ is punctually $\iota$-pure of weight $w$ if
and only if there is (equivalently, for every) element
$\sigma\in W(X_0)$ of positive degree $d$ with

$$
|\iota(\chi(\sigma))|=q^{wd/2}.
$$

## Proof

Fix a degree-one lift $s\in W(X_0)$ as in
[def-wf-weil-group], and put $c=\chi(s)$. By
hypothesis the restriction of
$\chi$ to $\pi_1(X)$ has finite image, and by the modulus identity
of [lem-wf-rank-one-component-modulus] applied to the image of
the degree-$m$ coset of $W(X_0)$ in
$G^{[m]}\subseteq G_{\mathrm{arith}}(\rho)$ (an element
$w=\gamma s^m$ with $\gamma\in\pi_1(X)$ has matrix
$\rho(\gamma)\rho(s)^m$), one has

$$
|\iota(\chi(w))|=|\iota(c)|^{m}\qquad\text{for all }w\in W(X_0)
\text{ with }\deg(w)=m.
$$

If $\mathcal L_0$ is punctually $\iota$-pure of weight $w$, then at
a closed point $x$ the eigenvalue $\chi(F_x)$ of the local
geometric Frobenius $F_x$ (of degree $d(x)$) has modulus
$q_x^{w/2}=q^{d(x)w/2}$ by [def-weil-punctual-weights], so the
identity above gives $|\iota(c)|^{d(x)}=q^{d(x)w/2}$, whence
$|\iota(c)|=q^{w/2}$ and
$|\iota(\chi(\sigma))|=|\iota(c)|^{d}=q^{wd/2}$ for every
positive-degree $\sigma$. Conversely, if the displayed equality
holds for one such $\sigma$, then $|\iota(c)|=q^{w/2}$ by the same
identity, and every closed point $x$ satisfies
$|\iota(\chi(F_x))|=|\iota(c)|^{d(x)}=q_x^{w/2}$, which is the
punctual purity of [def-weil-punctual-weights].
