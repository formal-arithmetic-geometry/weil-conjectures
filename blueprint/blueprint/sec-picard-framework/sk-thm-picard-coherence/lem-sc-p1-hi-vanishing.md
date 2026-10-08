+++
id = "lem-sc-p1-hi-vanishing"
kind = "lemma"
title = "Vanishing above the dimension on $\\mathbf P^1_k$"
order = 640
uses = ["def-sc-p1-standard", "lem-sc-cech-spectral", "lem-sc-p1-monomial", "pqf-lem-affine-vanishing"]
+++
Let $k$ be a field and $\mathcal F$ a quasi-coherent
$\mathcal O_{\mathbf P^1_k}$-module. Then
$H^q(\mathbf P^1_k,\mathcal F)=0$ for all $q\geq2$.

## Proof

Exactly as in the proof of [lem-sc-p1-monomial]: by
[lem-sc-cech-spectral] for the Zariski covering of
[def-sc-p1-standard], with
$E_2^{p,q}=\check H^p(\mathfrak U,\underline H^q(\mathcal F))$,
the presheaves $\underline H^q(\mathcal F)$ vanish for $q>0$ on
the affine members ([pqf-lem-affine-vanishing], $\mathcal F$
quasi-coherent) and $\check H^p=0$ for $p\geq2$ (two members);
so $E_2^{p,q}=0$ whenever $p+q\geq2$, and the convergence of the
spectral sequence gives $H^n(\mathbf P^1_k,\mathcal F)=0$ for
$n\geq2$.
