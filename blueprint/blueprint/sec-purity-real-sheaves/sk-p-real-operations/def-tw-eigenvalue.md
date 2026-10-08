+++
id = "def-tw-eigenvalue"
kind = "definition"
title = "Eigenvalues and q-adic absolute values"
order = 2591
uses = ["def-tw-conventions", "def-tw-frobenius-action"]
+++
Let $\alpha\in\overline{\mathbf Q}_\ell$ be an eigenvalue of the
$\overline{\mathbf Q}_\ell$-linear automorphism $\Phi_X^*$ of
[def-tw-frobenius-action]. The $q$-adic absolute value of
$\alpha$, in the *weight normalization*, is

$$
|\alpha|:=q^{v(\alpha)},\qquad|q|=q,
$$

where $v$ is the $\mathbf Q_\ell$-adic valuation normalized by
$v(q)=1$ (equivalently:
$|\alpha|=|\alpha|_{\mathbf Q_\ell\text{-adic}}^{-1}$ for the usual
normalized absolute value on $\mathbf Q_\ell$ with
$|\ell|=\ell^{-1}$), extended to each finite extension of
$\mathbf Q_\ell$ by the usual
$(|\alpha|)^{[K:\mathbf Q_\ell]}= |N_{K/\mathbf Q_\ell}(\alpha)|$ rule (the absolute value
$|\cdot|_{\mathbf Q_\ell\text{-adic}}$ alone would give
$|q|=q^{-1}$, so the reciprocal normalization is what makes
$|q|=q$ and hence the weight convention below). The
eigenvalue $\alpha$ has *weight* $w\in\mathbf Z$ if
$|\alpha|=q^{w/2}$.
