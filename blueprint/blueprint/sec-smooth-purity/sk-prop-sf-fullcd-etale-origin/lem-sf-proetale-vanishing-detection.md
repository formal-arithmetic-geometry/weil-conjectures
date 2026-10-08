+++
id = "lem-sf-proetale-vanishing-detection"
kind = "lemma"
title = "Detection of vanishing on affine weakly contractible objects"
order = 1792
uses = ["def-weil-pbc-etale-site", "def-weil-pbc-proetale-modules", "def-weil-pbc-proetale-site", "lem-cbc-proetale-stalk-conservative"]
+++
Let $\Lambda$ be a finite discrete ring, let $T$ be a scheme and let
$F$ be a sheaf of $\Lambda$-modules on the
small pro-étale site
$T_{\Proet}$.

1. **(i)** $F=0$ if and only if $F(W)=0$ for every affine weakly
contractible object $W\to T$ of $T_{\Proet}$.
1. **(ii)** More generally, a complex of $\Lambda$-module sheaves on
$T_{\Proet}$ is acyclic if and only if its evaluation at every affine
weakly contractible object of $T_{\Proet}$ is an acyclic complex.

Consequently the family of evaluation functors $F\mapsto F(W)$, indexed
by the affine weakly contractible objects, is a detection device on the
whole pro-étale topos, although the geometric-point stalks are not
conservative there by clause (4) of
[lem-cbc-proetale-stalk-conservative].

## Proof

*(i).* The implication from left to right is trivial. For the
converse let $V$ be an object of $T_{\Proet}$. The pro-étale site has
enough affine quasi-compact weakly contractible objects: this is Stacks
Project, Pro-étale Cohomology, Lemma 61.13.4,
[Tag 0990](https://stacks.math.columbia.edu/tag/0990), which states
that $T_{\mathrm{proet}}$ has enough (affine) quasi-compact
weakly contractible objects in the sense of the definition of weakly
contractible objects of a site, so that every object of $T_{\Proet}$
admits a covering $\lbrace W_i\to V\rbrace$ by affine weakly contractible
objects; the cited lemma is the pro-étale instance of that general
notion. The sheaf axiom embeds $F(V)$ into $\prod_iF(W_i)=0$, so
$F(V)=0$, and $V$ was arbitrary.
*(ii).* A complex of sheaves is acyclic if and only if each of its
three-term segments $K^n\to K^{n+1}\to K^{n+2}$ is exact in the middle.
Exactness of such a segment is detected by evaluation at the objects of
any class $\mathcal B$ of weakly contractible objects that covers every
object of the site: this is Stacks Project, Cohomology on Sites,
Proposition 21.51.2,
[Tag 0947](https://stacks.math.columbia.edu/tag/0947), part (1),
quoted here and applied with $\mathcal B$ the affine weakly contractible
objects, whose covering property is the input of (i); the remaining parts
of that proposition are not used. Combining the two equivalences gives
(ii). The final sentence restates that (i) and (ii) are proved by
evaluation at weakly contractible objects and never by geometric-point
stalks, in contrast with clause (4) of
[lem-cbc-proetale-stalk-conservative].
