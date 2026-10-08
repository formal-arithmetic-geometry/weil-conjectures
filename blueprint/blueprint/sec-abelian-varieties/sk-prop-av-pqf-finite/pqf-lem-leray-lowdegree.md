+++
id = "pqf-lem-leray-lowdegree"
kind = "lemma"
title = "Low degree terms of the Leray spectral sequence"
order = 543
uses = ["pqf-def-cohomology", "pqf-lem-leray"]
+++
Let $f:X\to Y$ be a morphism of schemes and $\mathcal F$ a
quasi-coherent $\mathcal O_X$-module. The low degree terms of the
spectral sequence of [pqf-lem-leray] give an exact sequence

$$
0\longrightarrow\mathrm H^1(Y,f_*\mathcal F)
\longrightarrow\mathrm H^1(X,\mathcal F)
\longrightarrow\mathrm H^0(Y,R^1f_*\mathcal F)
\longrightarrow\mathrm H^2(Y,f_*\mathcal F).
$$

In particular, if $R^1f_*\mathcal F=0$, then
$\mathrm H^1(X,\mathcal F)\cong\mathrm H^1(Y,f_*\mathcal F)$.

## Proof

The spectral sequence of [pqf-lem-leray] is
$E_2^{p,q}=\mathrm H^p(Y,R^qf_*\mathcal F)$; the terms with $p+q=0,1,2$
are the displayed sequence, exact by the standard edge and connecting
maps of a spectral sequence and by the cohomology long exact
sequences of [pqf-def-cohomology] (the maps
$E_2^{0,1}\to E_2^{2,0}$ being the second differential and its
composites). If $R^1f_*\mathcal F=0$, the middle term vanishes and the
resulting exact sequence gives the stated isomorphism.
