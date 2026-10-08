+++
id = "lem-fd-affine-line-constant-cohomology"
kind = "lemma"
title = "Constant cohomology of the affine line"
order = 2684
uses = ["def-fd-additive-character", "def-weil-pbc-qbar-category", "lem-sc-pic-affine", "sbc-thm-cohomological-dimension-of-an-affine-curve", "thm-sc-affine-cohomology"]
+++
For $k$ finite or algebraically closed,

$$
H^q(\mathbf A^1_{\bar k},\overline{\mathbf Q}_\ell)=\begin{cases}\overline{\mathbf Q}_\ell,&q=0,\\0,&q>0.\end{cases}
$$

## Proof

The affine line is irreducible, hence connected, so $H^0=\overline{\mathbf Q}_\ell$. For $q>0$ the $\overline{\mathbf Q}_\ell$-cohomology is computed from the compatible finite-level cohomologies of the constant sheaves $\mathbf Z/\ell^n$ by [def-weil-pbc-qbar-category], and $H^q(\mathbf A^1_{\bar k},\mathbf Z/\ell^n)=0$ for every $q>0$: the vanishing for $q>1$ is the cohomological dimension of an affine curve of [sbc-thm-cohomological-dimension-of-an-affine-curve], and $H^1(\mathbf A^1_{\bar k},\mathbf Z/\ell^n)\cong\operatorname{Pic}(\mathbf A^1_{\bar k})[\ell^n]=0$ by [thm-sc-affine-cohomology], the Picard group being trivial by [lem-sc-pic-affine] (the compactification is $\mathbf P^1$ of genus $0$, whose Jacobian is trivial, so the quotient of [lem-sc-pic-affine] is $\operatorname{Pic}(\mathbf A^1)=0$).
