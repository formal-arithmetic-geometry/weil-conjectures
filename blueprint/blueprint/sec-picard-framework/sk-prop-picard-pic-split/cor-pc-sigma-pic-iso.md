+++
id = "cor-pc-sigma-pic-iso"
kind = "theorem"
title = "$\\operatorname{Pic}_{X/k,\\sigma}$ is isomorphic to $\\operatorname{Pic}_{X/k}$"
order = 817
tags = ["latex:corollary"]
uses = ["def-pc-pic-sigma-functor", "def-pc-picard-functor", "lem-pc-k-sheaf", "lem-pc-rational-hyp", "thm-pc-pic-split"]
+++
Let $k$ be a field and let $X$ be a smooth projective curve over $k$ with
a $k$-rational point $\sigma$. Then the functors
$\operatorname{Pic}_{X/k,\sigma}$ and
$\operatorname{Pic}_{X/k}$ on
$(\mathit{Sch}/k)_{fppf}$ are isomorphic. In particular
$\operatorname{Pic}_{X/k,\sigma}$ is an fppf sheaf (represented once $\operatorname{Pic}_{X/k}$ is;
and covariantly: if $\operatorname{Pic}_{X/k,\sigma}$ is representable, then so is
$\operatorname{Pic}_{X/k}$, by the group law of [thm-pc-pic-split]).

## Proof

By [lem-pc-rational-hyp] and [thm-pc-pic-split],
$\operatorname{Pic}_{X/k}$ is the fppf sheafification of the presheaf
$K(T)=\operatorname{Ker}(\sigma_T^*)$, and by [lem-pc-k-sheaf] the
presheaf $K$ is itself an fppf sheaf; since
$\operatorname{Pic}_{X/k,\sigma}=K$ ([def-pc-pic-sigma-functor]), the two functors
are naturally isomorphic. [The reference is the discussion in Stacks
Project, Picard Schemes of Curves, Section 44.6, after Lemma 44.6.1.]
