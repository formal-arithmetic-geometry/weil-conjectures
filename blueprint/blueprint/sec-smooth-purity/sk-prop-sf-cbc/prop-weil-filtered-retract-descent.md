+++
id = "prop-weil-filtered-retract-descent"
kind = "theorem"
title = "Filtered retract descent"
order = 1541
uses = ["def-weil-pbc-finite-stage-pair-category", "prop-weil-pbc-common-stage-calculus", "thm-weil-pbc-finite-stage-karoubian"]
tags = ["latex:proposition"]
+++
Assume that for every $E\in\mathsf{FinExt}_\ell$ the category
$\mathcal C_E(T)=\Dbc(T,E)$ of
[def-weil-pbc-finite-stage-pair-category] is idempotent complete (for
instance by [thm-weil-pbc-finite-stage-karoubian]). Then the pair category
$\mathcal P_T$ is idempotent complete: every idempotent of $\mathcal P_T$
splits, and a splitting may be represented over a single finite coefficient
field.

*Source note:* no Stacks Project entry states this descent: the ledger's
verified entries contain no idempotent-completion or filtered-colimit entry,
and the blueprint adds the splitting of an idempotent of the pair category
over a single finite coefficient field, given idempotent completeness of the
finite-stage categories. The nearest entries, each fetched and quoted, are
Homological Algebra, Definition 12.4.1 ([Tag
09SG](https://stacks.math.columbia.edu/tag/09SG), Karoubian: every
idempotent endomorphism of an object has a kernel) and Lemma 12.4.2 ([Tag
09SH](https://stacks.math.columbia.edu/tag/09SH), Karoubian iff every
idempotent has a cokernel iff $z=x\oplus y$ with $p$ the projection onto
$y$), with the Karoubianity criteria Lemma 12.4.3 ([Tag
05QV](https://stacks.math.columbia.edu/tag/05QV), countable products with
kernels of maps having a right inverse) and Lemma 13.4.14 ([Tag
05QW](https://stacks.math.columbia.edu/tag/05QW), a triangulated category
with countable products, or with countable coproducts, is Karoubian); the
only idempotent inside a filtered colimit in Stacks is the one of Remark
4.21.6 ([Tag 09P8](https://stacks.math.columbia.edu/tag/09P8)), where the
colimit of an idempotent diagram in *Sets* is its image. Difference: those
entries test a category that is already given, and Stacks constructs no
idempotent completion (the request to add the Karoubi envelope stands as a
comment on Section 12.4, Tag 09SF); here idempotent completeness is assumed
for every finite stage and the conclusion is a splitting over one stage.

## Proof

Let $e:(E,K)\to(E,K)$ be an idempotent of the pair category
$\mathcal P_T$ of [def-weil-pbc-finite-stage-pair-category] and let
$(M,u)$, with $u:T_{M/E}K\to T_{M/E}K$, be a representative of $e$. The
equality $e^2=e$ holds in $\mathcal P_T$, so by the equivalence relation and
the transport formula of [prop-weil-pbc-common-stage-calculus] there is a
finite $P\supset M$ with
$$
 u_P\circ u_P=u_P
 \qquad\text{in }\mathcal C_P(T)
$$
(the composite $e^2$ being represented by $(M,u\circ u)$). The category
$\mathcal C_P(T)=\Dbc(T,P)$ is idempotent complete by the hypothesis
(verified by [thm-weil-pbc-finite-stage-karoubian]), so there exist
$K'_P\in\mathcal C_P(T)$, $p_P:T_{P/E}K\to K'_P$, and
$i_P:K'_P\to T_{P/E}K$ with
$$
 p_P\,i_P=\operatorname{id}_{K'_P},\qquad i_P\,p_P=u_P.
$$
In $\mathcal P_T$, let $K'=(P,K'_P)$, and let
$$
 i=[P,i_P]:K'\longrightarrow(P,T_{P/E}K)\cong(E,K),
\qquad
 p=[P,p_P]:(E,K)\cong(P,T_{P/E}K)\longrightarrow K',
$$
where the displayed isomorphisms are the classes of the identity morphisms
(well defined, since $P\supset E$). Then $p\,i=[P,p_P\,i_P]$ is the class of
the identity, i.e. the identity of $K'$, and $i\,p=[P,i_P\,p_P]=[P,u_P]$ is
the class of $e$. Hence $e$ splits in $\mathcal P_T$, over the single field
$P$.
