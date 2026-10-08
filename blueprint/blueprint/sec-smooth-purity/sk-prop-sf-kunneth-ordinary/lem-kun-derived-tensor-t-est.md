+++
id = "lem-kun-derived-tensor-t-est"
kind = "lemma"
title = "Connectivity of the derived tensor product"
order = 1728
uses = ["def-kun-derived-tensor", "def-weil-pbc-derived-categories"]
+++
Let $A,B\in D(T_{\Et},\Lambda)$. If $\mathcal H^i(A)=0$ for $i<a$
and $\mathcal H^i(B)=0$ for $i<b$, then
$\mathcal H^i(A\kunotimes{\Lambda}B)=0$ for $i<a+b$
(standard homological algebra: the Kunneth spectral sequence of the
derived tensor product).

## Proof

Represent $B$ by a K-flat complex $Q$, so that
$A\otimes^{\mathbf L}_\Lambda B=A\otimes_\Lambda Q$ by
[def-kun-derived-tensor]. The standard Tor spectral sequence of
the derived tensor product has

$$
E^2_{p,q}=\bigoplus_{q_1+q_2=q}
\operatorname{Tor}^{\Lambda}_{p}\bigl(\mathcal H^{q_1}(A),
\mathcal H^{q_2}(Q)\bigr)
\Longrightarrow
\mathcal H^{p+q}(A\otimes_\Lambda Q)
$$

(this is basic homological algebra: the filtration of the total complex
of a double complex). If $\mathcal H^i(A)=0$ for $i<a$ and
$\mathcal H^i(B)=0$ for $i<b$, then $q_1\ge a$ and $q_2\ge b$
for every nonzero term, so $q=q_1+q_2\ge a+b$ and $p\ge0$; hence
$E^2_{p,q}=0$ whenever $p+q<a+b$, and the abutment vanishes in
those degrees.
