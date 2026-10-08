+++
id = "sbc-lem-bounded-below-truncation-criterion"
kind = "lemma"
title = "Bounded-below truncation criterion"
order = 1439
uses = ["def-weil-pbc-hypercohomology-filtrations", "sbc-def-derived-categories-with-allowable-torsion"]
+++
Let $K\in D^+_{\mathcal P\text{-tor}}(T_{\Et})$. For fixed $n$, only
$H^q(K)$ with $q\leq n$ can contribute to $H^n(Rg_*K)$. Hence

$$
H^n(Rg_*\tau_{\leq n}K)\xrightarrow{\ \sim\ }H^n(Rg_*K),
$$

and the analogous statement holds after pullback and for $h_*$.

## Proof

The hypercohomology spectral sequence of
[def-weil-pbc-hypercohomology-filtrations] has
$E_2^{p,q}=R^pg_*H^q(K)$; for $p+q=n$ only $q\leq n$ contributes since
$g_*$ is $t$-left exact, so
$H^n(Rg_*\tau_{\leq n}K)\cong H^n(Rg_*K)$; pullback and $h$ are handled
identically.
