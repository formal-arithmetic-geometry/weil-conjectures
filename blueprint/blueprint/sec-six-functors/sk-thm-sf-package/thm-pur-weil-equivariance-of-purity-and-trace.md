+++
id = "thm-pur-weil-equivariance-of-purity-and-trace"
kind = "theorem"
title = "Weil equivariance of purity and trace"
order = 2238
uses = ["def-coefficient-twists-detailed", "def-pur-compact-support-transport", "def-pur-conventions", "def-pur-scheme-geometric-frobenius", "def-pur-smooth-pullback-exchange", "def-pur-smooth-trace", "def-pur-tate-datum", "def-sbc-smooth-morphisms", "def-weil-frobenius-coefficient-twists", "def-weil-pbc-proetale-site", "def-weil-scheme-morphism-properties", "thm-pur-adic-reconstruction", "thm-pur-smooth-base-change-coherence"]
+++
In the purity conventions of this chapter ([def-pur-conventions] fixed setting),
geometric-Frobenius datum,
and let $f:X\to Y$ be smooth of relative dimension $d$ with strict
Weil datum $(K,\varphi_K)$ as in [def-pur-tate-datum]. Then smooth
purity is equivariant: the square

$$
\begin{array}{ccc}
Lg_{X,\gamma}^*Lf^*K(d)[2d]
& \xrightarrow{\ Lg_{X,\gamma}^*(\gamma_{f,K})\ }
& Lg_{X,\gamma}^*Rf^!K\\
\big\downarrow\ \varphi^{\mathrm{pur}}_{f,K}
& \sim & \big\downarrow\ \varphi^!_{f,K}\\
Lf^*K(d)[2d]
& \xrightarrow{\ \gamma_{f,K}\ }
& Rf^!K
\end{array}
$$

commutes. If $\varphi_{f_!Rf^!K}$ is formed from $\varphi^!_{f,K}$ by
[def-pur-compact-support-transport], then the exceptional counit is
equivariant, and if $\varphi_{f_!Lf^*K(d)[2d]}$ is formed from
$\varphi^{\mathrm{pur}}_{f,K}$, then the normalized smooth trace of
[def-pur-smooth-trace] is equivariant:

$$
\begin{array}{ccc}
Lg_{Y,\gamma}^*Rf_!Lf^*K(d)[2d]
& \xrightarrow{\ Lg_{Y,\gamma}^*(\operatorname{Tr}^{\mathrm{sm}}_{f,K})\ }
& Lg_{Y,\gamma}^*K\\
\big\downarrow\ \varphi_{f_!Lf^*K(d)[2d]}
& \sim & \big\downarrow\ \varphi_K\\
Rf_!Lf^*K(d)[2d]
& \xrightarrow{\ \operatorname{Tr}^{\mathrm{sm}}_{f,K}\ }
& K.
\end{array}
$$

## Proof

Step 1: the purity square. By [thm-pur-smooth-base-change-coherence]
for the first Cartesian square of
[def-pur-scheme-geometric-frobenius], the composite of
$Lg_{X,\gamma}^*(\gamma_{f,K})$ with the
$\operatorname{Ex}^{!,\mathrm{sm}}_{f,g_{Y,\gamma},K}$ (the
equivalence of the sources) equals

$$
\gamma_{f,Lg_{Y,\gamma}^*K}\circ\bigl(Lf^*\otimes\tau_d\bigr)\circ
\bigl(Lg_{X,\gamma}^*Lf^*\cong Lf^*Lg_{Y,\gamma}^*\bigr)
$$

(the base-change square of purity); the definition of the data
$\varphi^{\mathrm{pur}}_{f,K}$ and $\varphi^!_{f,K}$ in
[def-pur-tate-datum] and of
$\operatorname{Ex}^{!,\mathrm{sm}}$ in
[def-pur-smooth-pullback-exchange] – the middle square being
the definition of the exchange and the twist datum $\tau_d$ being
the twist normalization of
[def-weil-frobenius-coefficient-twists] – transposes this
equality into the commutativity of the purity square of the
statement. Step 2: the counit square. The compact-support transport
$\varphi_{f_!Rf^!K}$ of [def-pur-compact-support-transport] is the
composite of the compact-support base-change exchange $\operatorname{Ex}_!$
for the same Cartesian square with the pushforward $Rf_!$ of the datum
$\varphi^!_{f,K}$. The counit $\operatorname{Tr}_{f,K}$ is the
adjoint of the identity of $K$, conjugated by the adjunction
$Rf_!\dashv Rf^!$; the exchange maps of the base change are exactly
the adjoints of the exceptional base-change identifications, so the
counit-square commutativity is the base-change compatibility of the
adjunction: the transpose of the counit square is the square in
which the purity square and the $\varphi$-data commute, i.e. the
square of Step 1. More explicitly, both composites

$$
Lg_{Y,\gamma}^*Rf_!Rf^!K\longrightarrow Lg_{Y,\gamma}^*K\longrightarrow K
$$

and

$$
Lg_{Y,\gamma}^*Rf_!Rf^!K\longrightarrow
Rf_!Lg_{X,\gamma}^*Rf^!K\longrightarrow Rf_!Rf^!K\longrightarrow K
$$

are the same: the first arrow is the counit pulled back and the
second is the counit of the pulled-back adjunction, which is the
$Lg_{Y,\gamma}^*$-image of the counit, by the definition of the
transport and the compatibility of the adjunction with base change.
Step 3: the trace square. The smooth trace
$\operatorname{Tr}^{\mathrm{sm}}_{f,K}$ of
[def-pur-smooth-trace] is the counit of the adjacency after
$Rf_!(\gamma_{f,K})$, so the trace square is the composite of the
squares of Steps 1 and 2, using the definition of the data
$\varphi^{\mathrm{pur}}_{f,K}$ and $\varphi^!_{f,K}$ of
[def-pur-scheme-geometric-frobenius] (the datum of the source of
the trace is the transport of $\varphi^{\mathrm{pur}}_{f,K}$, and the
datum of the target is $\varphi_K$). Step 4: the scheme-Frobenius
form. Precomposing the vertical maps with the natural comparisons
$\kappa_X,\kappa_Y$ of [def-pur-scheme-geometric-frobenius] –
which satisfy $Lf^*\kappa_Y=\kappa_XLf^*$ – identifies the
geometric-Frobenius squares with the scheme-Frobenius squares of the
operators $u_N$, all three displayed squares commuting then for the
$u$'s as for the $\varphi$'s. Step 5: the transports. The
compatibility with finite reduction, scalar extension, composition,
and base change is the corresponding compatibility of the data and of
the coherence statements of [thm-pur-smooth-base-change-coherence]
and [thm-pur-adic-reconstruction] (the data are constructed from
the operations and coherences, all of which transport).
