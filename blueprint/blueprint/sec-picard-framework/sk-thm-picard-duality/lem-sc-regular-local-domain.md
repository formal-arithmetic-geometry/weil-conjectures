+++
id = "lem-sc-regular-local-domain"
kind = "lemma"
title = "Regular local rings are domains"
order = 686
+++
A regular local ring $R$ is a domain.

## Proof

For a regular local ring $(R,\mathfrak m)$, the associated graded
ring

$$
\operatorname{gr}_{\mathfrak m}R
:=\bigoplus_{i\geq0}\mathfrak m^i/\mathfrak m^{i+1}
$$

is a polynomial ring over the residue field $R/\mathfrak m$ in
$\dim R$ variables (the standard characterization of regularity:
$R$ is regular if and only if
$\operatorname{gr}_{\mathfrak m}R$ is a polynomial ring;
*reference: Stacks Project, Commutative Algebra, Lemma
10.106.1, [Tag 00NO](https://stacks.math.columbia.edu/tag/00NO)*). A polynomial ring over a field is a domain.
Finally, a ring whose associated graded ring is a domain is a
domain: if $ab=0$ with $a,b\neq0$, let $\bar a,\bar b$ be
the leading (lowest-degree nonzero) homogeneous components of
$a,b$; the lowest-degree component of $ab$ is
$\bar a\bar b\neq0$, contradicting $ab=0$. Hence $R$ is a
domain.
