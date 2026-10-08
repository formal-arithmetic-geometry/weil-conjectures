+++
id = "thm-weil-pbc-direct-image-finiteness-proper"
kind = "theorem"
title = "Finiteness of proper direct images"
order = 1304
uses = ["def-weil-pbc-constructible-direct-image-finiteness", "def-weil-pbc-scheme-conventions", "prop-weil-pbc-comparison-direct-image"]
+++
Let $\Lambda=P_n$ be as in
[def-weil-pbc-constructible-direct-image-finiteness], let $X,Y$ be
noetherian of finite dimension with the torsion orders invertible, and let
$f:X\to Y$ be a proper morphism whose geometric fibers have dimension at
most $e\in\mathbf Z_{\geq0}$. Then
$$
 \mathrm{FIN}(f,\Lambda;2e)
$$
holds.

*Source:* the finiteness theorem for higher direct images of constructible
sheaves under proper morphisms — Deligne, SGA 4 1/2, Theoreme de finitude,
Th. 1.1, for constructibility, together with the amplitude bound of Stacks
Project, Etale Cohomology, Lemma 59.92.2, [Tag
095U](https://stacks.math.columbia.edu/tag/095U)
($R^qf_*\mathcal F=0$ for $q>2n$ when all fibers have dimension at most $n$
and $\mathcal F$ is an abelian torsion sheaf on $X_{\Et}$); a
compact-support form of the constructibility input is Stacks Project, More
Etale Cohomology, Theorem 63.14.5, [Tag
0GL0](https://stacks.math.columbia.edu/tag/0GL0) (for $f$ separated of
finite presentation and $K\in D^+_{tors,c}(X_{\Et},\Lambda)$, $Rf_!K$ has
constructible cohomology sheaves; for $f$ proper $Rf_!=Rf_*$), and the
etale-to-pro-etale transfer below is the comparison of
[prop-weil-pbc-comparison-direct-image]; difference: both are etale-site
statements for a single Noetherian coefficient ring, neither tracks an
amplitude shift, only 0GL0 uses constructibility of the coefficient, and
neither mentions a coefficient tower or a pro-etale site. No Stacks Project
entry states this form for the pro-etale site, the blueprint adding the
pro-etale form of the finiteness statement with the tracked bound $2e$, the
etale-origin witnesses and the amplitude bookkeeping used by the
amplification conditions below.

## Proof

Let $F$ be constructible on $X_{\Proet}$, so $F\cong\nu_X^*F_{\Et}$ with
$F_{\Et}$ a constructible $\Lambda$-module sheaf on $X_{\Et}$. Since the
finite ring $\Lambda=P_n$ is annihilated by an integer, $F_{\Et}$ is a
torsion abelian sheaf, so the classical input of the source note (Th. 1.1 of
SGA 4 1/2 and [Tag 095U](https://stacks.math.columbia.edu/tag/095U)) applies
to $f_{\Et}$: the sheaves $R^qf_{\Et,*}F_{\Et}$ are constructible and zero
for $q>2e$. By [prop-weil-pbc-comparison-direct-image],
$$
 R^qf_{\Proet,*}F\cong R^qf_{\Proet,*}\nu_X^*F_{\Et}
 \cong\nu_Y^*R^qf_{\Et,*}F_{\Et}\qquad(q\geq0),
$$
which is constructible on $Y_{\Proet}$ and vanishes for $q>2e$. This is the
two clauses of [def-weil-pbc-constructible-direct-image-finiteness] for
$u=f$, $c=2e$.
