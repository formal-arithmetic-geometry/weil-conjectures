+++
id = "lem-pc-degree-agrees-sc"
kind = "lemma"
title = "Degree agrees with the degree of file 06"
order = 812
uses = ["def-pc-curve", "def-pc-degree-line-bundle", "def-pc-divisor-line-bundle", "def-sc-divisor", "def-sc-pic0", "lem-pc-degree-base-change", "lem-pc-divisor-line-bundle-properties", "lem-pc-euler-additive"]
+++
Let $k$ be a field, $C$ a proper smooth
curve over $k$, and $D$ a
divisor of $C$ which is effective. Then the
degree $\deg(\mathcal{O}_C(D))$ of
Definition [def-pc-degree-line-bundle]
equals $\deg D$ of [def-sc-pic0] (for $k$ algebraically closed
where it is defined). In particular for a $k$-rational point $P$,
$\deg(\mathcal{O}_C([P]))=1$.

## Proof

Both notions are additive in $D$: $\mathcal{O}_C(D_1+D_2)=\mathcal{O}_C(D_1)\otimes\mathcal{O}_C(D_2)$
(for the module of
[def-pc-divisor-line-bundle]: by the local checks of
[lem-pc-divisor-line-bundle-properties]; for the degree:
[lem-pc-degree-base-change] / [lem-pc-euler-additive]), so it
suffices to treat $D=[P]$ with $P$ a closed point. The exact sequence
$0\to\mathcal{O}_C\to\mathcal{O}_C([P])\to\kappa(P)\to0$ (the quotient
$\mathcal{O}_C([P])/\mathcal{O}_C=\mathcal{O}_C([P])|_P=\kappa(P)$: the module
$\mathcal{O}_C([P])=\mathcal{I}_P^\vee$ contains $\mathcal{O}_C$ with quotient
$\mathcal{I}_P^\vee\otimes_{\mathcal{O}_C}\mathcal{O}_P\cong\kappa(P)$ since
$\mathcal{I}_P\otimes\mathcal{O}_P=\mathfrak m_P$; the inclusion being the embedding of
the ideal, dualizing gives an inclusion $\mathcal{O}_C\subseteq\mathcal{I}_P^\vee$ with
quotient as stated) together with the additivity of $\chi$
([lem-pc-euler-additive]) gives

$$
\chi(C,\mathcal{O}_C([P]))=\chi(C,\mathcal{O}_C)+\dim_k\kappa(P),
$$

and for a $k$-rational point $P$ (i.e. $\dim_k\kappa(P)=1$) therefore
$\deg(\mathcal{O}_C([P]))=\chi(\mathcal{O}_C([P]))-\chi(\mathcal{O}_C)=1=\deg([P])$ of
[def-sc-pic0] (degree of a $k$-rational point is $1$). For
general closed points the same computation gives
$\deg(\mathcal{O}_C([P]))=[\kappa(P):k]=\deg([P])$, and additivity finishes.
