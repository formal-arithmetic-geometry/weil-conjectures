+++
id = "pqf-lem-fff-vanishing"
kind = "lemma"
title = "Formal functions vanishing over finite fibres"
order = 539
uses = ["pqf-def-coherent", "pqf-def-cohomology", "pqf-def-locnoeth", "pqf-lem-leray"]
+++
Let $f:X\to Y$ be a proper morphism of schemes and $y\in Y$. Assume
that $Y$ is locally Noetherian and that $f^{-1}(\{y\})$ is finite.
Then for any coherent sheaf $\mathcal F$ on $X$ we have
$(R^pf_*\mathcal F)_y=0$ for all $p>0$.
(*Stacks Project, Cohomology of Schemes, Lemma 30.20.8, Tag
[02OE](https://stacks.math.columbia.edu/tag/02OE), whose proof uses
the theorem on formal functions, Theorem 30.20.5, Tag
[02OC](https://stacks.math.columbia.edu/tag/02OC).*)

## Proof

The theorem on formal functions (recorded classical input cited in the
statement): with $\widehat{\mathcal O_{Y,y}}$ the completion of the
local ring, with the $n$-th infinitesimal neighbourhoods

$$
X_n:=X\times_Y\operatorname{Spec}\bigl(\mathcal O_{Y,y}/\mathfrak m_y^n\bigr)
$$

of the fibre $X_y:=f^{-1}(\{y\})$, and with $\widehat X$ the
*formal completion* of $X$ along the closed fibre $X_y$ (the
formal scheme $X^{\wedge}_{X_y}$, with $\mathrm H^p(-,-)$ the
cohomology functors of [pqf-def-cohomology]), the canonical
comparisons are

$$
(R^pf_*\mathcal F)_y\otimes_{\mathcal O_{Y,y}}\widehat{\mathcal
O_{Y,y}}\ \cong\ \mathrm H^p\bigl(\widehat X,\widehat{\mathcal F}\bigr)
\ \cong\ \varprojlim_n\mathrm H^p(X_n,\mathcal F_n)\qquad(p\ge0),
$$

$\widehat{\mathcal F}$ being the pullback of $\mathcal F$ to the
formal completion and $\mathcal F_n$ its restriction to the
thickenings, the second comparison being the defining property of the
cohomology of formal coherent sheaves. (The *scheme*
$X\times_Y\operatorname{Spec}\widehat{\mathcal O_{Y,y}}$, whose
underlying topological space can also contain points over the generic
points of the completed local base, is not a formal
completion, and its cohomology is not the limit of the cohomologies
of the $X_n$; it is $\widehat X$ that the theorem on formal
functions uses.) The
underlying topological space of the formal completion $\widehat X$,
equivalently of each $X_n$, is that of the fibre $X_y$:
$f^{-1}(\{y\})$; it is finite, zero-dimensional, and hence
discrete. Each $X_n$ is therefore a finite scheme (a disjoint union of
spectra of local Artinian rings), and a coherent sheaf on a finite
discrete space has vanishing cohomology in positive degrees (on a
discrete space every sheaf is flasque, and flasque sheaves are acyclic
for $\Gamma$, as in the Leray proof of [pqf-lem-leray]);
hence $\mathrm H^p(X_n,\mathcal F_n)=0$ for every $p>0$ and every
$n$, and the displayed limit gives
$\mathrm H^p(\widehat X,\widehat{\mathcal F})=0$ for every $p>0$;
hence
$(R^pf_*\mathcal F)_y\otimes_{\mathcal O_{Y,y}}\widehat{\mathcal O_{Y,y}}=0$ for $p>0$.
Finally, $(R^pf_*\mathcal F)_y$ is a finitely generated
$\mathcal O_{Y,y}$-module: for a proper morphism with a locally
Noetherian target and a coherent $\mathcal F$ on the source
([pqf-def-locnoeth], [pqf-def-coherent]), the higher direct images
$R^pf_*\mathcal F$ are coherent (classical: the coherence of higher
direct images for proper morphisms, cf. Stacks Cohomology of
Schemes, Proposition 30.19.1, Tag [02O5](https://stacks.math.columbia.edu/tag/02O5)), and the stalk of a
coherent sheaf is finitely generated. A finitely generated module
$M$ over the Noetherian local ring $\mathcal O_{Y,y}$ with
$M\otimes_{\mathcal O_{Y,y}}\widehat{\mathcal O_{Y,y}}=0$ is zero:
following Nakayama, the completion of a finitely generated module is
$M\otimes_{\mathcal O_{Y,y}}\widehat{\mathcal O_{Y,y}}$, so the
quotients $M/\mathfrak m_y^nM$ all vanish, and with
$M/\mathfrak m_yM=0$ Nakayama's lemma gives $M=0$. Thus
$(R^pf_*\mathcal F)_y=0$ for all $p>0$.
