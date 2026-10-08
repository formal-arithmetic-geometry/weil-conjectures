+++
id = "def-weil-pbc-completed-base-change-map"
kind = "definition"
title = "Completed base-change map"
order = 1338
uses = ["def-weil-pbc-completed-pullback", "def-weil-pbc-derived-inverse-limit", "def-weil-pbc-etale-origin-witness", "def-weil-pbc-projection-formula-map"]
+++
Let $K$ be derived complete and let every $K_n$ have a displayed witness
$\epsilon_X^{-1}L_n\simeq K_n$ with
$L_n\in D_c^+(X_{\mathrm{et}},\Lambda/I^n)$. Define

$$
\operatorname{Ex}^{\mathrm{comp}}_{\square,K}:
Lg^*_{\mathrm{comp}}Rf_*K\longrightarrow
Rf'_*L(g')^*_{\mathrm{comp}}K
$$

to be the ordered composite

$$
\begin{aligned}
Lg^*_{\mathrm{comp}}Rf_*K
&\xrightarrow{\sim}R\varprojlim_n Lg^*Rf_*K_n\\
&\xrightarrow{R\varprojlim_n\operatorname{Ex}_{\square,K_n}}
R\varprojlim_nRf'_*L(g')^*K_n\\
&\xrightarrow{\sim}Rf'_*R\varprojlim_nL(g')^*K_n
=Rf'_*L(g')^*_{\mathrm{comp}}K.
\end{aligned}
$$

In the notation above, the first two arrows are $H$ followed by $V'$.
The first isomorphism uses reconstruction and the perfect projection formula;
the second displayed isomorphism is the inverse of direct-image/limit
commutation. This definition fills the map-construction omission in Tag
`09C9`.

## Detailed form

Assume that every $K_n$ carries a specified etale-origin witness
[def-weil-pbc-etale-origin-witness]. Define
$$
 \Ex^{\mathrm{comp}}_{\square,K}:
 Lg^*_{\mathrm{comp}}Rf_*K
 \longrightarrow Rf'_*Lg'^*_{\mathrm{comp}}K
$$
as the ordered composite
$$
 \begin{aligned}
  Lg^*_{\mathrm{comp}}Rf_*K
  &\xrightarrow{\sim}\Rlim B_\bullet\\
  &\xrightarrow{\Rlim(v'_\bullet)}\Rlim D_\bullet\\
  &\xrightarrow{\sim}
  Rf'_*\Rlim\bigl(Lg'^*_{\operatorname{Tow}}K_\bullet\bigr)
  =Rf'_*Lg'^*_{\mathrm{comp}}K.
 \end{aligned}
$$
The first isomorphism is reconstruction followed by the projection formula
for the finite quotients, and the last is the inverse of the canonical
direct-image/derived-limit comparison. These choices are part of the
displayed ordered composite.

The completeness of $Lg^*_{\mathrm{comp}}$ and the
direct-image/derived-limit comparison used here are clauses (2) and (4) of
Stacks Project, Lemma 61.20.2 ([Tag
099N](https://stacks.math.columbia.edu/tag/099N), Section 61.20, [Tag
099L](https://stacks.math.columbia.edu/tag/099L)): the Stacks entry assumes
a Noetherian ring $\Lambda$, an ideal $I$ and a morphism of topoi, and
states $Rf_*K=\Rlim Rf_*(K\otimes^L_\Lambda\underline{\Lambda/I^n})$ and
$Lf^*_{comp}M=\Rlim Lf^*(M\otimes^L_\Lambda\underline{\Lambda/I^n})$, while
the form used here is the ordered composite assembled from the tower
category and the per-level witnesses of
[def-weil-pbc-etale-origin-witness].

This identifier carries a `-detailed` suffix: the sketch import already uses
`def-weil-pbc-completed-base-change-map` for the corresponding statement.
