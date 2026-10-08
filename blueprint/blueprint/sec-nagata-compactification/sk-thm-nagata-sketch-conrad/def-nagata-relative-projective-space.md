+++
id = "def-nagata-relative-projective-space"
kind = "definition"
title = "Relative projective space"
order = 203
uses = ["def-nagata-relative-proj", "lemma-nagata-relative-proj-exists"]
+++
For $r\in\mathbb N$, define the relative projective-space interface by

$$
\mathbf P^r_X
=\operatorname{Proj}_X
\bigl(\operatorname{Sym}_{\mathcal O_X}(\mathcal O_X^{r+1})\bigr),
$$

with the symmetric-algebra generators placed in degree one. Its standard
opens are required to be the relative affine schemes of the degree-zero
homogeneous localizations at those generators. The existence and
compatibility of this object are supplied by
[lemma-nagata-relative-proj-exists].

This node is not formalized: it presupposes relative Proj, which is not
formalized either. Everything that needs only the scheme
$\mathbf P^r_X\to X$, and not its standard charts, uses
[def-nagata-projective-space-base-change] instead.
