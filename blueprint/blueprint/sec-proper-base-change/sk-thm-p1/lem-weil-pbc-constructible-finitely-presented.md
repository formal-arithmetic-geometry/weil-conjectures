+++
id = "lem-weil-pbc-constructible-finitely-presented"
kind = "lemma"
title = "Constructible sheaves are finitely presented in the category of sheaves"
order = 1128
uses = ["def-weil-pbc-constructible-complexes", "def-weil-pbc-etale-sheaves"]
+++
Let $X$ be a quasi-compact and quasi-separated scheme, let $\Lambda$ be a
Noetherian ring, let $F$ be a constructible sheaf of $\Lambda$-modules on
$X_{\Et}$, and let $G=\varinjlim_iG_i$ be a filtered colimit of sheaves of
$\Lambda$-modules. Then the canonical map

$$
 \varinjlim_i\operatorname{Mor}(F,G_i)\longrightarrow
 \operatorname{Mor}(F,G)
$$

is a bijection; equivalently, every morphism $F\to G$ factors through one of
the $G_i$, and any two such factorizations agree after passing to a common
refinement of the index.
(*Stacks Project, Etale Cohomology, Lemma 59.73.8, Tag
[09Z4](https://stacks.math.columbia.edu/tag/09Z4).*)

## Proof

Two recorded inputs are used. First, a constructible sheaf of
$\Lambda$-modules is a finite colimit of representable sheaves $h_W$ with
$W\to X$ quasi-compact and quasi-separated (Stacks Project, Etale Cohomology,
Lemma 59.73.5, Tag [09Y9](https://stacks.math.columbia.edu/tag/09Y9), whose
proof argues by a finite stratification of $X$ and induction on the number of
strata). Second, for such a $W$ the sections $\mathcal
G(W)=\operatorname{Mor}(h_W,\mathcal G)$ of a sheaf commute with filtered
colimits of sheaves (Stacks Project, Sites, Lemma 7.17.7, Tag
[0738](https://stacks.math.columbia.edu/tag/0738): a quasi-compact
quasi-separated object of a site is coherent). Colimits in the first variable
are computed on the presentation, and the two assertions of the statement are
respectively the existence and the uniqueness of the factorization, so the two
inputs give the bijection.
