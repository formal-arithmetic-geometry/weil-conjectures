+++
id = "lem-sp-grothendieck-edge-maps"
kind = "lemma"
title = "Edge maps of the Grothendieck spectral sequence"
order = 603
uses = ["def-sp-composite-acyclicity", "def-sp-convergence", "thm-sp-grothendieck"]
+++
Let $(F,G)$ be a composable pair [def-sp-composite-acyclicity] with $F$
sending injectives to $G$-acyclics, and let $X\in\mathcal A$. The *bottom
edge map* of the Grothendieck spectral sequence of $X$ is

$$
 R^nG(F(X))\longrightarrow R^n(G\circ F)(X),
$$

and the *left edge map* is

$$
 R^n(G\circ F)(X)\longrightarrow G(R^nF(X));
$$

both are functorial in $X$. In the sheaf setting $F=f_*$, $G=h_*$ of the
proper-base-change chapter they are respectively $R^nh_*f_*\mathcal F\to
R^n(hf)_*\mathcal F$ and $R^n(hf)_*\mathcal F\to h_*R^nf_*\mathcal F$.

## Proof

Write $H^n=R^n(G\circ F)(X)$ and use the finite decreasing abutment
filtration of [thm-sp-grothendieck]. No differential leaves $E_r^{n,0}$ for
$r\geq2$; hence the successive page maps give a surjection
$E_2^{n,0}\twoheadrightarrow E_\infty^{n,0}=F^nH^n$. Composing with
$F^nH^n\hookrightarrow H^n$ gives the bottom edge. No differential enters
$E_r^{0,n}$; hence $E_\infty^{0,n}\hookrightarrow E_2^{0,n}$. Composing with
$H^n\twoheadrightarrow H^n/F^1H^n=E_\infty^{0,n}$ gives the left edge. These
associated graded identifications are the convergence data of
[def-sp-convergence]. The constructions commute with morphisms of filtered
abutments and of pages, so they are functorial.
