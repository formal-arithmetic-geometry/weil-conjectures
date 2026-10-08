+++
id = "def-sp-spectral-sequence"
kind = "definition"
title = "Spectral sequences"
order = 506
uses = ["def-sp-abelian"]
+++
Let $\mathcal C$ be an abelian category [def-sp-abelian], let $\kappa$ be a
set, let $c:\mathbb Z\to\operatorname{ComplexShape}\kappa$ be a family of
complex shapes, and let $r_0\in\mathbb Z$ be a starting page. A *spectral
sequence* $E$ consists of a complex $E(r)$ of shape $c(r)$ (the $r$-th
*page*, with differentials $d_r$) for every $r\geq r_0$, together with
isomorphisms $\mathcal H(E(r))_{pq}\xrightarrow{\sim}E(r+1)_{pq}$ for every
$r\geq r_0$ and every index $pq$; a *morphism* of spectral sequences is a
compatible family of morphisms of pages.
