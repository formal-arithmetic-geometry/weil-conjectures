+++
id = "lem-wf-weil-group-constant-extension"
kind = "lemma"
title = "Weil group after a finite constant-field extension"
order = 2578
uses = ["def-tw-frobenius-action", "def-weil-finite-field-fiber", "def-weil-pbc-scheme-conventions", "def-wf-weil-group", "lem-wf-weil-group-exact-sequence"]
+++
Let $X_0$ be a
separated finite-type
$\mathbf F_q$-scheme with geometrically connected fibre
$X=X_0\times_{\mathbf F_q}\overline{\mathbf F}_q$. For $m\geq1$,
put

$$
X_0^{(m)}=X_0\times_{\mathbf F_q}\mathbf F_{q^m}
$$

and regard it as an $\mathbf F_{q^m}$-scheme. Under the natural map to
$X_0$, its Weil group identifies with

$$
W(X_0^{(m)})
\xrightarrow{\;\sim\;}
W(X_0)^{[m]}:=\deg^{-1}(m\mathbf Z)\subseteq W(X_0).
$$

Its geometric subgroup is still $\pi_1(X)$, and its normalized degree is

$$
\deg_{\mathbf F_{q^m}}(w)=\deg_{\mathbf F_q}(w)/m.
$$

In particular, if $s\in W(X_0)$ has degree one, then $s^m$ has degree
one for the $\mathbf F_{q^m}$-Weil group.

## Proof

Use the finite-field datum of [def-weil-finite-field-fiber]. A finite
etale cover of $X_0^{(m)}$ is the same as a finite etale cover of $X_0$
whose constant-field action factors through
$\operatorname{Gal}(\overline{\mathbf F}_q/\mathbf F_{q^m})$: this follows
directly by pulling a finite etale algebra along
$\mathbf F_q\subseteq\mathbf F_{q^m}$, and descending it along the finite
Galois action. Consequently the induced arithmetic fundamental group is
the inverse image of
$\operatorname{Gal}(\overline{\mathbf F}_q/\mathbf F_{q^m})$ inside the
arithmetic fundamental group of $X_0$. The geometric kernel is unchanged,
because both geometric fibres equal $X$.

The geometric Frobenius over $\mathbf F_{q^m}$ is the $m$-th power of
the geometric Frobenius over $\mathbf F_q$, by the convention of
[def-tw-frobenius-action]. Taking the inverse image of the cyclic
group it generates in the exact sequence of [def-wf-weil-group],
whose degree-zero part is the geometric subgroup $\pi_1(X)$ by
[lem-wf-weil-group-exact-sequence], therefore gives exactly
$\deg^{-1}(m\mathbf Z)$. Dividing the old degree by $m$ sends this
Frobenius, and hence $s^m$, to one, which proves the normalized-degree
formula.
