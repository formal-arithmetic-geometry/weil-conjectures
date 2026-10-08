+++
id = "lem-kun-leray-finite"
kind = "lemma"
title = "Leray through a finite morphism"
order = 1698
uses = ["def-weil-pbc-scheme-conventions", "lem-weil-pbc-grothendieck-spectral-sequence", "lemma-weil-pbc-finite-direct-image-exact"]
+++
Let $\pi:X'\to X$ and $h:Z\to X'$ be morphisms of schemes with
$\pi$ finite. For every
abelian sheaf $G$ on $Z$ and every $q\ge0$,

$$
R^q(\pi\circ h)_*G=\pi_*R^qh_*G.
$$

## Proof

The Grothendieck spectral sequence of
[lem-weil-pbc-grothendieck-spectral-sequence] for the composite
$Z\xrightarrow{h}X'\xrightarrow{\pi}X$ has
$E_2^{p,q}=R^p\pi_*R^qh_*G$. As $\pi$ is finite,
$R^p\pi_*=0$ for $p>0$ by
[lemma-weil-pbc-finite-direct-image-exact], so the spectral
sequence degenerates at $E_2$ and its abutment in total degree $q$
is the edge term $E_2^{0,q}=\pi_*R^qh_*G$, which is the assertion.
