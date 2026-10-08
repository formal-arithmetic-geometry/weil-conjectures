+++
id = "cor-weil-finite-constructible-hom"
kind = "theorem"
title = "Internal Hom for arbitrary finite-stage constructible complexes"
order = 2138
tags = ["latex:corollary"]
uses = ["def-weil-derived-pullback-tensor-hom", "lem-sf-tensor-ctf", "lem-weil-finite-duality-site-comparison", "lem-weil-verdier-preservation-strata", "thm-fix-general-biduality"]
+++
Let $\dim X\leq d$, and let $K,L\in D^b_{ctf}(X,A_{E,n})$,
on the etale or pro-etale site over $\overline{\mathbf F}_q$.
Then $R\mathcal Hom_A(K,L)$ is bounded constructible of finite
Tor amplitude. If the Tor intervals of $K,L$ are respectively
$[a,b]$, $[c,e]$, one valid interval for this internal Hom is
$[c-b-2d,e-a+2d]$.

## Proof

The tensor–Hom adjunction of
[def-weil-derived-pullback-tensor-hom] and biduality
[thm-fix-general-biduality] give the natural identity

$$
R\mathcal Hom_A(K,L)
\cong R\mathcal Hom_A(K,D_XD_XL)
\cong D_X(K\otimes_A^LD_XL).
$$

By [lem-weil-verdier-preservation-strata], $D_XL$ has Tor
interval $[-e-2d,-c]$. Tensor preservation
[lem-sf-tensor-ctf] gives interval $[a-e-2d,b-c]$ for the
tensor inside the last dual. Apply the same duality bound again to
obtain $[c-b-2d,e-a+2d]$. All the objects are constructible by
the same two results. The argument on the pro-etale site is the
transport by [lem-weil-finite-duality-site-comparison]; it makes
no site-perfectness assumption on $K$ or $L$ on all of $X$.
