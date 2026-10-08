+++
id = "sk-def-sf-exchanges"
kind = "section"
title = "Exchange and projection transformations, typed"
order = 1500
lean = ["AlgebraicGeometry.Etale.baseChange"]
+++
*Definition (sketch).*

Let $f:X\to Y$ be separated of finite type with a Cartesian square

$$
\begin{array}{ccc}
X'&\xrightarrow{\ g'\ }&X\\
{\scriptstyle f'}\downarrow&&\downarrow{\scriptstyle f}\\
Y'&\xrightarrow{\ g\ }&Y .
\end{array}
$$

The *exchange transformations* are the natural transformations

$$
\operatorname{Ex}_*:Lg^*Rf_*\longrightarrow Rf'_*Lg'^*,
\qquad
\operatorname{Ex}_!:Lg^*Rf_!\longrightarrow Rf'_!Lg'^*,
$$

the first between functors $D^+(X,\Lambda)\to D^+(Y',\Lambda)$ and the second
between functors on the ambient categories on which $Rf_!,Rf'_!$ are defined
([sk-def-sf-operations] (iv); at the adic stages, on the derived-complete
pro-étale complexes, it is the completed exchange
$\operatorname{Ex}^{\mathrm{comp}}_!$ through the completed pullbacks
$Lg^*_{\mathrm{comp}}$, def:cbc-completed-exchange-map). This only
fixes the source and target of $\operatorname{Ex}_!$; the range on which it is
an isomorphism is the one stated in [sk-prop-sf-cbc], and nothing is
asserted outside it. For $K\in\Dbc(X,\Lambda)$ and
$L\in\Dctf(Y,\Lambda)$ the *projection transformation* is the morphism

$$
\operatorname{PF}_{f,K,L}:Rf_!K\otimes^L_\Lambda L\longrightarrow
Rf_!\bigl(K\otimes^L_\Lambda Lf^*L\bigr)
\qquad\text{in }D^+(Y,\Lambda),
$$

natural in $K$ and $L$. All three are those of
def:exchange-projection; their source and target categories are the ones
written above, and whether they are isomorphisms is a theorem
([sk-thm-properbasechange], [sk-thm-smooth-base-change], [sk-prop-sf-cbc],
[sk-rem-sf-pf-done]).
