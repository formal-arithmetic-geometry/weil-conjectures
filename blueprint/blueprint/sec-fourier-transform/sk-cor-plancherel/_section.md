+++
id = "sk-cor-plancherel"
kind = "section"
title = "P9: Plancherel"
order = 2708
uses = ["sk-lem-orthogonality", "sk-thm-fourier-trace-formula"]
+++
*Corollary (sketch).*

Fix, as in [sk-d-real-setup], a field embedding
$\iota:\Qlb\hookrightarrow\mathbf C$; the trace functions take values in
$E\subset\Qlb$, and the absolute value and the complex conjugation below are
those of $\mathbf C$, read through $\iota$. Then for every $n\ge1$ and every
Weil complex $K$ on $\Aone$,

$$
\sum_{y\in\mathbf F_{q^n}}\bigl|\iota\,t_{\FT_\psi(K)}(y)\bigr|^2
=q^n\sum_{x\in\mathbf F_{q^n}}\bigl|\iota\,t_K(x)\bigr|^2 .
$$

(Blueprint cor:fd-plancherel.)

## Proof

Apply $\iota$ to the finite Fourier sum of P8, multiply by its complex
conjugate and sum over $y$; since $\iota\psi_n(z)$ is a complex root of
unity, $\overline{\iota\psi_n(x'y)}=\iota\psi_n(-x'y)$, so

$$
\sum_y\Bigl|\sum_x\iota t_K(x)\,\iota\psi_n(xy)\Bigr|^2
=\sum_y\sum_{x,x'}\iota t_K(x)\,\overline{\iota t_K(x')}\,
\iota\psi_n\bigl((x-x')y\bigr);
$$

the orthogonality of [sk-lem-orthogonality] (an identity in $\Qlb$,
transported by $\iota$) makes the inner $y$-sum $q^n$
on the diagonal and $0$ off it, which is the identity. This is the classical
Plancherel theorem for the finite group $(\mathbf F_{q^n},+)$, transported to
trace functions; no weight enters.

Uses: [sk-lem-orthogonality], [sk-thm-fourier-trace-formula]
