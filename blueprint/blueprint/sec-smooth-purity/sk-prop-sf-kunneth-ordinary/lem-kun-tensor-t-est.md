+++
id = "lem-kun-tensor-t-est"
kind = "lemma"
title = "Left t-exactness of derived direct image"
order = 1727
uses = ["def-weil-pbc-derived-categories", "def-weil-pbc-direct-image", "def-weil-pbc-hypercohomology-filtrations"]
+++
Let $f:X\to Y$ be a morphism of schemes and $E\in\Dplus(X_{\Et})$.
If $\mathcal H^i(E)=0$ for $i<b$, then
$\mathcal H^i(Rf_*E)=0$ for $i<b$.

## Proof

The hypercohomology spectral sequence of
[def-weil-pbc-hypercohomology-filtrations] has
$E_2^{p,q}=R^pf_*\mathcal H^q(E)$; for $q<b$ all
$\mathcal H^q(E)$ vanish, so $E_2^{p,q}=0$ for $q<b$, and no
term with $p+q<b$ survives, giving
$\mathcal H^i(Rf_*E)=0$ for $i<b$.
