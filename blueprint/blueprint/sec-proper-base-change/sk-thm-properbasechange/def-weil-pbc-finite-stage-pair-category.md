+++
id = "def-weil-pbc-finite-stage-pair-category"
kind = "definition"
title = "Finite-stage pair category"
order = 1308
uses = ["def-weil-pbc-bounded-constructible-complete", "def-weil-pbc-rational-category", "prop-weil-pbc-scalar-extension"]
+++
Let $\mathsf{FinExt}_\ell$ be the poset of finite intermediate fields
$\Ql\subset E\subset\Qlb$; it is filtered because the compositum of two
finite fields is finite. Put
$$
 \mathcal C_E(T)=\Dbc(T,E),
 \qquad T_{F/E}=F\otimes_E^L-:\mathcal C_E(T)\to\mathcal C_F(T),
$$
the categories $\Dbc(T,E)$ being those of
[def-weil-pbc-rational-category]. The normalized units
$T_{E/E}=\operatorname{id}$, the associators $a_{G,F,E}$, and the shift
comparisons $\sigma_{F/E}$ used below are the data constructed in
[prop-weil-pbc-scalar-extension].

Define an object of $\mathcal P_T$ to be a pair $(E,K)$ with
$K\in\mathcal C_E(T)$. A morphism representative
$(M,u):(E,K)\to(F,L)$ consists of a finite field $M\supset E,F$ and a map
$$
 u:T_{M/E}K\longrightarrow T_{M/F}L
 \quad\text{in }\mathcal C_M(T).
$$
For $M\subset N$, transport it to
$$
 u_N=
 a_{N,M,F,L}\circ T_{N/M}(u)\circ a_{N,M,E,K}^{-1}.
$$
Representatives $(M,u)$ and $(N,v)$ are equivalent if $u_P=v_P$ in
$\mathcal C_P(T)$ for some finite $P\supset M,N$. Define
$$
 \Hom_{\mathcal P_T}((E,K),(F,L))
 =\varinjlim_{M\supset E,F}
 \Hom_{\mathcal C_M(T)}(T_{M/E}K,T_{M/F}L)
$$
as the resulting equivalence classes. Addition, identities, negatives, and
composition are computed after transporting all representatives to one
common finite overfield.

*Source note:* no Stacks Project entry states this construction: the
ledger's verified entries contain no filtered-colimit or Karoubi
construction of coefficient categories, and the blueprint adds the pair
category $\mathcal P_T$ of finite stages, whose morphism sets are filtered
colimits over the finite extensions $E/\Ql$. The nearest entries, each
fetched and quoted, are Categories, Definition 4.21.1 ([Tag
00D3](https://stacks.math.columbia.edu/tag/00D3), directed set) and Lemma
4.21.5 ([Tag 0032](https://stacks.math.columbia.edu/tag/0032), a filtered
index category may be replaced by a directed set without changing colimits)
with Remark 4.21.6 ([Tag
09P8](https://stacks.math.columbia.edu/tag/09P8), a colimit indexed by a
finite filtered category need not be trivial), and Definition 61.29.1 ([Tag
09C1](https://stacks.math.columbia.edu/tag/09C1)), which fixes one
Noetherian coefficient ring $\Lambda$ and forms no colimit over coefficient
fields. Difference: those entries take colimits of diagrams inside a fixed
category and keep the coefficient ring fixed, whereas the blueprint adds
both the filtered poset $\mathsf{FinExt}_\ell$ and the category
$\mathcal P_T$ built from it.
