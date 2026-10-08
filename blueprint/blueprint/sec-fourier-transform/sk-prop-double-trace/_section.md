+++
id = "sk-prop-double-trace"
kind = "section"
title = "P10: trace-level Fourier inversion"
order = 2710
uses = ["sk-lem-orthogonality", "sk-thm-fourier-trace-formula"]
+++
*Corollary (sketch).*

For a constructible Weil complex $K$ on $\Aone$, every $n\ge1$ and every
$y\in\mathbf F_{q^n}$,

$$
t_{\FT_{\psi^{-1}}\FT_\psi(K)}(y)=q^n\,t_K(y),
$$

which is the trace function of the Tate twist $K(-1)$ at points of degree
$n$. This is the rank-one trace-level consequence of the functorial
inversion isomorphism in [sk-thm-inversion]; the calculation below also
deduces it directly from the Fourier trace formula.
*Note: this corollary seems never to be used later — the inversion
needed downstream is the functorial [sk-thm-inversion] — so it is kept only
as a consistency check and has no detailed counterpart in the blueprint.*

## Proof

Apply P8 twice, with $\psi$ and then with $\psi^{-1}$; orthogonality
[sk-lem-orthogonality] in the form
$\sum_y\psi_n((x-x')y)=q^n\delta_{x,x'}$ returns $q^nt_K(x)$. The Tate twist
$K(-1)$ has trace function $q^nt_K$ at degree-$n$ points by the
normalization built into the twist def:wf-tate-twist.

Uses: [sk-lem-orthogonality], [sk-thm-fourier-trace-formula]
